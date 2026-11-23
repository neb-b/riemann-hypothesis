module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0104
public import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import Formalism.LocalToGlobal.KernelLattices.DeterminantCokernelCount.JetMomTA
public import Formalism.LocalToGlobal.GlobalTheory.GL3.PThIndep
public import Formalism.LocalToGlobal.KernelLattices.LateralTheory
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0101
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0028
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdBox
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TWMain
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0014
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0105
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0097
public import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ImagQuadraticMaximalOrderArithmeticAtSplitPrime
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.UwEllipticFlow
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FormalGroupPadicMulIntegralVanishingOrder
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsUnitCoeffMulSeriesLeNorm
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FrameNStHolds
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.UniversalStatement

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsIntegralTypesAndDirectionsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_types_and_directions' : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y) (ϖ : T.V), Irreducible ϖ → ∀ (g : ℕ), g.Prime → ¬ IsUnit ((g : ℕ) : T.V) → (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {(g : 𝓞 E)})).card = Module.finrank ℚ E → (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {(g : 𝓞 E)})).Nodup → ∀ (F : Type) [Field F] [CharZero F] [Algebra T.Fr F] [Algebra T.V F] [IsScalarTower T.V T.Fr F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v → letI := io.toAlgebra; ∃ (σ : (E →+* ℂ) → 𝓞 E →+* TWO.Ov v) (e : Lt1 Dw → Fin (chD C.ch) → TWO.Ov v), (∀ τ a, (σ τ a : F) = algebraMap T.Fr F (io (embK c τ a))) ∧ (∀ ℓ i, (e ℓ i : F) = algebraMap T.V F (C.uvecT ℓ i)) ∧ (∀ ℓ i, (e ℓ i : F) = algebraMap T.Fr F (C.ch.uvec ℓ i)) ∧ (∀ (a : 𝓞 E) ℓ, (dAct F C.ch.B a).mulVec (fun i => (e ℓ i : F)) = (σ ℓ.1 a : F) • fun i => (e ℓ i : F)) ∧ (∀ τ a, (0 < v (σ τ a : F) → σ τ a ∈ Ideal.span {((g : ℕ) : TWO.Ov v)}) ∧ (¬ 0 < v (σ τ a : F) → IsUnit (σ τ a))) ∧ (∀ τ a, σ (ComplexEmbedding.conjugate τ) a = σ τ (star a)) ∧ (open Classical in ∃ lam : Lt1 Dw → Fin (chD C.ch) → TWO.Ov v, ∀ l l', ∑ s, lam l s * e l' s = if l = l' then 1 else 0) ∧ (open Classical in ∃ ε : (E →+* ℂ) → 𝓞 E, ∀ τ τ', σ τ' (ε τ) - (if τ = τ' then 1 else 0) ∈ Ideal.span {((g : ℕ) : TWO.Ov v)}) ∧ ¬ IsUnit ((g : ℕ) : TWO.Ov v) := by
  first | exact @GlobalTheory.PowGerm.exists_integral_types_and_directions | exact GlobalTheory.PowGerm.exists_integral_types_and_directions | (intros; apply GlobalTheory.PowGerm.exists_integral_types_and_directions <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsMahlerExpansion
section
open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

namespace GlobalTheory.MonomialDense
open GlobalTheory.MultiMahler

variable {p : ℕ} [Fact p.Prime]

noncomputable def incl (p : ℕ) [Fact p.Prime] : ℤ_[p] →+* ℂ_[p] :=
  (algebraMap ℚ_[p] ℂ_[p]).comp PadicInt.Coe.ringHom

theorem continuous_incl : Continuous (incl p) :=
  (continuous_algebraMap ℚ_[p] ℂ_[p]).comp continuous_subtype_val

theorem factorial_mul_binomC (k : ℕ) (x : ℤ_[p]) :
    (k.factorial : ℂ_[p]) * binomC k x
      = incl p (Polynomial.aeval x (descPochhammer ℤ k)) := by
  have h1 : binomC k x = incl p (Ring.choose x k) := rfl
  have h2 := Ring.descPochhammer_eq_factorial_smul_choose x k
  rw [← Polynomial.aeval_eq_smeval] at h2
  rw [h1, h2, nsmul_eq_mul, map_mul, map_natCast]

theorem exists_mahler_expansion {E : Type*} [NormedAddCommGroup E] [NormedSpace ℚ_[p] E]
    [IsUltrametricDist E] [CompleteSpace E] (f : C(ℤ_[p], E)) :
    ∃ t : ℕ → C(ℤ_[p], E), HasSum t f ∧
      ∀ n, ∃ a : E, ∀ x, t n x = ((mahler n x : ℤ_[p]) : ℚ_[p]) • a := by
  letI : Module ℤ_[p] E := Module.compHom E (algebraMap ℤ_[p] ℚ_[p])
  haveI : IsBoundedSMul ℤ_[p] E := IsBoundedSMul.of_norm_smul_le fun r x =>
    norm_smul_le (r : ℚ_[p]) x
  exact ⟨_, PadicInt.hasSum_mahler f, fun n => ⟨_, fun _ => rfl⟩⟩

variable {Z : Type} [TopologicalSpace Z] [CompactSpace Z]

omit [CompactSpace Z] in
theorem binomC_comp_mem (S : Subalgebra ℂ_[p] C(Z, ℂ_[p])) (φ : C(Z, ℤ_[p]))
    (X : C(Z, ℂ_[p])) (hX : ∀ z, X z = incl p (φ z)) (hS : X ∈ S) (k : ℕ) :
    (binomC k).comp φ ∈ S := by
  have hmem : ∀ P : Polynomial ℤ, ∃ G ∈ S, ∀ z, G z = incl p (Polynomial.aeval (φ z) P) := by
    intro P
    induction P using Polynomial.induction_on' with
    | add P Q hP hQ =>
      obtain ⟨G, hG, hG'⟩ := hP
      obtain ⟨G₂, hG₂, hG₂'⟩ := hQ
      exact ⟨G + G₂, S.add_mem hG hG₂, fun z => by simp [hG', hG₂']⟩
    | monomial n a =>
      refine ⟨(a : ℂ_[p]) • X ^ n, S.smul_mem (S.pow_mem hS n) _, fun z => ?_⟩
      simp [hX, Polynomial.aeval_monomial]
  obtain ⟨G, hG, hG'⟩ := hmem (descPochhammer ℤ k)
  have hk : (k.factorial : ℂ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
  have : (binomC k).comp φ = (k.factorial : ℂ_[p])⁻¹ • G := by
    ext z
    change binomC k (φ z) = (k.factorial : ℂ_[p])⁻¹ * G z
    rw [hG', ← factorial_mul_binomC, inv_mul_cancel_left₀ hk]
  rw [this]
  exact S.smul_mem hG _

noncomputable def evalAlong {Y : Type} [TopologicalSpace Y] [CompactSpace Y] [T2Space Y]
    (φ : C(Z, ℤ_[p])) (ψ : C(Z, Y)) :
    C(ℤ_[p], C(Y, ℂ_[p])) →L[ℂ_[p]] C(Z, ℂ_[p]) :=
  LinearMap.mkContinuous
    { toFun := fun G => ⟨fun z => G (φ z) (ψ z), by fun_prop⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl } 1 (fun G => by
      rw [one_mul, ContinuousMap.norm_le _ (norm_nonneg _)]
      intro z
      exact ((G (φ z)).norm_coe_le_norm _).trans (G.norm_coe_le_norm _))

theorem comp_mem (S : Subalgebra ℂ_[p] C(Z, ℂ_[p])) (hS : IsClosed (S : Set C(Z, ℂ_[p])))
    (g : ℕ) : ∀ (φ : C(Z, Fin g → ℤ_[p])),
      (∀ i, ∃ X ∈ S, ∀ z, X z = incl p (φ z i)) →
      ∀ F : C(Fin g → ℤ_[p], ℂ_[p]), F.comp φ ∈ S := by
  induction g with
  | zero =>
    intro φ _ F
    have : F.comp φ = algebraMap ℂ_[p] C(Z, ℂ_[p]) (F 0) := by
      ext z
      simp [Subsingleton.elim (φ z) 0]
    rw [this]
    exact S.algebraMap_mem _
  | succ g ih =>
    intro φ hφ F
    obtain ⟨t, ht, ht'⟩ := exists_mahler_expansion (curryFirst F)
    let φ0 : C(Z, ℤ_[p]) := ⟨fun z => φ z 0, by fun_prop⟩
    let ψ : C(Z, Fin g → ℤ_[p]) := ⟨fun z i => φ z i.succ, by fun_prop⟩
    have h := (evalAlong φ0 ψ).hasSum ht
    have e : evalAlong φ0 ψ (curryFirst F) = F.comp φ := by
      ext z
      exact congrArg F (Fin.cons_self_tail (φ z))
    rw [e] at h
    refine hS.mem_of_tendsto h (Filter.Eventually.of_forall fun s => S.sum_mem fun n _ => ?_)
    obtain ⟨a, ha⟩ := ht' n
    have e2 : evalAlong φ0 ψ (t n) = (binomC n).comp φ0 * a.comp ψ := by
      ext z
      change t n (φ0 z) (ψ z) = _
      rw [ha]
      change ((mahler n (φ0 z) : ℤ_[p]) : ℚ_[p]) • a (ψ z) = _
      rw [Algebra.smul_def]
      rfl
    rw [e2]
    obtain ⟨X, hX, hX'⟩ := hφ 0
    exact S.mul_mem (binomC_comp_mem S φ0 X hX' hX n) (ih ψ (fun i => hφ i.succ) a)

theorem eq_zero_of_monomials : ∀ (p r : ℕ) [Fact p.Prime] (μ : C(Fin r → ℤ_[p], ℂ_[p]) →L[ℂ_[p]] ℂ_[p]), (∀ (m : ℕ) (k : Fin m → Fin r) (g : C(Fin r → ℤ_[p], ℂ_[p])), (∀ a, g a = ∏ j, zc (a (k j))) → μ g = 0) → μ = 0 := by
  intro p r _ μ hμ
  let X : Fin r → C(Fin r → ℤ_[p], ℂ_[p]) := fun i =>
    ⟨fun a => incl p (a i), continuous_incl.comp (continuous_apply i)⟩
  let A : Subalgebra ℂ_[p] C(Fin r → ℤ_[p], ℂ_[p]) := Algebra.adjoin ℂ_[p] (Set.range X)
  have hA : ∀ f ∈ A, μ f = 0 := by
    intro f hf
    have hf' : f ∈ Submodule.span ℂ_[p] (Submonoid.closure (Set.range X) : Set _) := by
      rw [← Algebra.adjoin_eq_span]; exact hf
    refine (Submodule.span_le (p := LinearMap.ker μ.toLinearMap)).mpr ?_ hf'
    intro g hg
    have : ∃ (m : ℕ) (k : Fin m → Fin r), ∀ a, g a = ∏ j, zc (a (k j)) := by
      induction hg using Submonoid.closure_induction_left with
      | one => exact ⟨0, Fin.elim0, fun a => by simp⟩
      | mul_left x hx y _ ih =>
        obtain ⟨i, rfl⟩ := hx
        obtain ⟨m, k, hk⟩ := ih
        refine ⟨m + 1, Fin.cons i k, fun a => ?_⟩
        rw [Fin.prod_univ_succ, ContinuousMap.mul_apply, hk]
        rfl
    obtain ⟨m, k, hk⟩ := this
    exact hμ m k g hk
  ext F
  have hF := comp_mem A.topologicalClosure A.isClosed_topologicalClosure r (ContinuousMap.id _)
    (fun i => ⟨X i, A.le_topologicalClosure (Algebra.subset_adjoin ⟨i, rfl⟩), fun _ => rfl⟩) F
  have hcl : closure (A : Set C(Fin r → ℤ_[p], ℂ_[p])) ⊆ {f | μ f = 0} :=
    closure_minimal hA (isClosed_eq μ.continuous continuous_const)
  exact hcl hF

end GlobalTheory.MonomialDense
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsPelUnifOfUnifPow
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem exists_pelUnif_of_unifPow : Laws → Laws2 → Laws4 → TwistBaseChangeStatement → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (t : SAB H (Sp V)) (P : PELUnif (maximalIdeal V) t) (n : ℕ) (D' : DegData V (maximalIdeal V)) (A' : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G' : Over (Sp V)) [GrpObj G'] [IsCommMonObj G'] (pD : IsPowDeg D'.toPre P.D.toPre n) (pA : IsPowPolAV A' P.A n) (pG : IsPowGrp G' t.G n) (U' : Unif (maximalIdeal V) D' A' G') (_PU : UnifPowOf3 pD pA pG U' P.U), letI := H.starRing; ∀ [Module (𝓞 E) D'.toPre.X] (oD' : D'.toPre.OAct (𝓞 E)), (∀ (a : 𝓞 E) (x : D'.toPre.X) (i : Fin n), pD.xe (a • x) i = a • pD.xe x i) → (∀ (a : 𝓞 E) (i : Fin n), oD'.onB.act a ≫ pD.pw.pr i = pD.pw.pr i ≫ P.oD.onB.act a) → ∃ (oA' : A'.OAct (𝓞 E)), (∀ (a : 𝓞 E) (i : Fin n), oA'.act a ≫ pA.pr i = pA.pr i ≫ P.oA.act a) ∧ ∃ (t' : SAB H (Sp V)) (P' : PELUnif (maximalIdeal V) t'), t'.G = G' ∧ HEq t'.grp (inferInstance : GrpObj G') ∧ HEq t'.comm (inferInstance : IsCommMonObj G') ∧ P'.D = D' ∧ HEq P'.mod (inferInstance : Module (𝓞 E) D'.toPre.X) ∧ HEq P'.oD oD' ∧ P'.A = A' ∧ HEq P'.oA oA' ∧ HEq P'.U U' := by
  intro _ _ _ _ V _ _ _ _ E _ _ _ H t P n D' A' G' _ _ pD pA pG U' Q
  letI := H.starRing
  intro md oD' hxi hoD
  have hx : ∀ (a : 𝓞 E) (x : D'.toPre.X), pD.xe (a • x) = a • pD.xe x := fun a x => funext fun i => hxi a x i
  obtain ⟨act', hact⟩ := (GlobalTheory.exists_powAct _ _ _ n pG).2 _ t.act
  have iso : LBIso U'.LG.L (boxLB t.PP.L pG.pr) := by
    rw [← P.bundle]; exact ⟨Q.wL, Q.wL_gen⟩
  let t' : SAB H (Sp V) :=
    { G := G'
      semi := GlobalTheory.PowGrp.isSemiAbelian_pow _ _ _ n pG t.semi
      act := act'
      PP := U'.LG
      cub := U'.cubG
      sym := isSymmetric_of_symmetry_generator U'.LG U'.symG U'.symG_gen U'.symG_rig
      adj := fun a => GlobalTheory.PowAdj.lbIso_cube_pow _ _ _ n pG _ _ t.PP.isLB U'.LG.isLB iso _ _ _ _ (hact a) (hact (H.bar a)) (t.adj a)
      prim := GlobalTheory.PowPrimitive.lbIso_cube_pow _ _ _ n pG _ _ t.PP.isLB U'.LG.isLB iso _ _ (hact H.w0) t.prim }
  obtain ⟨rA, hrA⟩ := (GlobalTheory.exists_powAct _ _ _ n pA.toIsPowGrp).1 _ P.oA.toRingAct
  let oA' : A'.OAct (𝓞 E) :=
    { toRingAct := rA
      rosati := fun a => GlobalTheory.rosatiAdj_pow _ _ _ n pA.toIsPowGrp _ _ P.A.isLB A'.isLB ⟨pA.w, pA.w_gen⟩ _ _ _ _ (hrA a)
        (hrA (star a)) (P.oA.rosati a) }
  let P' : PELUnif (maximalIdeal V) t' :=
    { D := D'
      oD := oD'
      A := A'
      oA := oA'
      U := U'
      bundle := rfl
      lin := GlobalTheory.oLinear_of_unifPow V (maximalIdeal V) n _ _ _ _ _ _ pD pA pG U' P.U Q _ hx P.oD oD' P.oA oA'
        t.act.toRingAct act'.toRingAct hoD hrA hact P.lin
      w0 := GlobalTheory.PsiWZeroProd.main V n _ _ pD _ hx P.oD oD' hoD H.w0 P.w0 }
  exact ⟨oA', hrA, t', P', rfl, HEq.rfl, HEq.rfl, rfl, HEq.rfl, HEq.rfl, rfl, HEq.rfl, HEq.rfl⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.FamilySetupCayleyRecursion
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Moment

theorem n1_sub_single_one_le_add_one {n : ℕ} (ν : Fin n → ℤ) (s : Fin n) :
    n1 (ν - Pi.single s 1) ≤ n1 ν + 1 := by
  have h1 : (∑ i, ((Pi.single s (1 : ℤ) : Fin n → ℤ) i).natAbs) = 1 := by
    rw [Finset.sum_eq_single s]
    · simp
    · intro b _ hb
      simp [Pi.single_eq_of_ne hb]
    · simp
  unfold n1
  rw [← h1, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  exact Int.natAbs_sub_le _ _

theorem moment_first_length : Hyps → ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r) (l : ∀ ν, (R ν).H → Wp) (dg : (Fin (2 * r + k + 1) → ℤ) → ℝ) (Q : Mx k r) (E : ∀ ν, Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ (R ν).smSub), Setup lam u b bv ga h q0 z π μW μN μG νq R l dg → PI.UpqRep.IsCayleyU k r (PI.BesselPeriodGGP.eps48 k r) Q → (∀ ν, n1 ν ≤ q0 → (R ν).IsE Q (E ν) ∧ Formalism.REAL.GlRel (E ν)) → ∀ (q : ℕ) ν, n1 ν + q ≤ q0 → ∀ j : ℕ, j + 2 * q ≤ 4 * (2 * r + k + 1) ^ 2 → ∀ w : (R ν).smSub, Lev (PI.BesselPeriodGGP.eps48 k r) (E ν) (fun a => lam a + ((ν : Fin (2 * r + k + 1) → ℤ) a : ℝ)) j w → ∫⁻ x, ENNReal.ofReal (lenA k r z (Matrix.of x) 0 ^ (2 * q) * (dg ν * ‖l ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq ≤ ENNReal.ofReal ((((2 * r + k + 1) : ℝ) ^ 2 * (Formalism.QuantumDeterminants.Tz k r z * b ^ 4) * (6 * bv) ^ (2 * (2 * r + 2))) ^ q * ‖w‖ ^ 2) := by
  intro H k r Wp _ _ _ _ lam u b bv ga h q0 z π μW μN μG νq R l dg Q E hS hQ hE q
  have hT : 0 < Formalism.QuantumDeterminants.Tz k r z := hS.2.2.1.2.1
  have hC : 0 ≤ (((2 * r + k + 1) : ℝ) ^ 2 * (Formalism.QuantumDeterminants.Tz k r z * b ^ 4) * (6 * bv) ^ (2 * (2 * r + 2))) := by
    have h6 : 0 ≤ (6 * bv) ^ (2 * (2 * r + 2)) := by rw [pow_mul]; positivity
    positivity
  induction q with
  | zero =>
    intro ν hν j _ w _
    have := (GlobalTheory.T.bessel_functional_l2_bound_and_isometry H k r Wp lam u b bv ga h q0 z π μW μN μG νq R l dg hS ν (by omega)).1 w w.2
    simpa using this
  | succ q ih =>
    intro ν hν j hj w hw
    have := GlobalTheory.T.family_setup_cayley_moment H k r Wp lam u b bv ga h q0 z π μW μN μG νq R l dg Q E hS hQ hE ν (by omega) j q _
      (by omega) (pow_nonneg hC q)
      (fun s y hy => ih (ν - Pi.single s 1) (by have := n1_sub_single_one_le_add_one ν s; omega) (j + 2) (by omega) y hy) w hw
    rw [pow_succ' _ q]
    exact this

end GlobalTheory.Moment
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.HeightOneOfSplit
section
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne

private theorem norm_zc_eq {q : ℕ} [Fact q.Prime] (a : ℤ_[q]) : ‖zc a‖ = ‖a‖ := by
  unfold zc
  exact (PadicComplex.norm_extends' (p := q) (a : ℚ_[q])).trans (PadicInt.norm_def).symm

private theorem zc_natCast_eq {q : ℕ} [Fact q.Prime] (n : ℕ) : zc (n : ℤ_[q]) = (n : ℂ_[q]) := by
  simp [zc]

theorem height_one_of_split : ∀ (d q : ℕ) [Fact q.Prime] (M : Mdl q) (F : FormalGroup 𝓞_ℂ_[q]), d.Prime → d % 16 = 7 → Split d q → IsOK d M.L → M.Ok → MvPowerSeries.subst (![PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[q]) (PowerSeries.map (M.ι : ℂ →+* ℂ_[q]) (tay M.u)), PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[q]) (PowerSeries.map (M.ι : ℂ →+* ℂ_[q]) (tay M.u))] : Fin 2 → MvPowerSeries (Fin 2) ℂ_[q]) (MvPowerSeries.map (algebraMap 𝓞_ℂ_[q] ℂ_[q]) F.toPowerSeries) = PowerSeries.subst (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[q]) (PowerSeries.map (M.ι : ℂ →+* ℂ_[q]) (tay M.u)) → ∃ ℓ : ℂ_[q]⟦X⟧, constantCoeff ℓ = 0 ∧ PowerSeries.subst ℓ (PowerSeries.map (M.ι : ℂ →+* ℂ_[q]) (tay M.u)) = X ∧ ‖coeff q (PowerSeries.subst (C (q : ℂ_[q]) * ℓ) (PowerSeries.map (M.ι : ℂ →+* ℂ_[q]) (tay M.u)))‖ = 1 ∧ ∀ k < q, ‖coeff k (PowerSeries.subst (C (q : ℂ_[q]) * ℓ) (PowerSeries.map (M.ι : ℂ →+* ℂ_[q]) (tay M.u)))‖ < 1 := by
  intro d q _ M F hd hd16 hs hOK hM hF
  set U : ℂ_[q]⟦X⟧ := PowerSeries.map (M.ι : ℂ →+* ℂ_[q]) (tay M.u) with hUdef
  have flow := uw_elliptic_flow q M hM
  have hU0 : constantCoeff U = 0 := by
    rw [hUdef, ← coeff_zero_eq_constantCoeff_apply, coeff_map, tay, coeff_mk]
    simp [flow.2.2.2.2.1]

  obtain ⟨ℓ, hchart, hℓX⟩ := Basic.exists_chart M hM
  have hℓ0 : constantCoeff ℓ = 0 := hchart.2.1
  have hUℓ : U.subst ℓ = X := hℓX
  obtain ⟨P1, P2, P3⟩ := _root_.GlobalTheory.MomOne.FormalMul.padic_multiplications q F U ℓ hU0 hℓ0 hUℓ hF
  refine ⟨ℓ, hℓ0, hUℓ, ?_, ?_⟩
  ·

    have hle : ‖coeff q (U.subst (C (q : ℂ_[q]) * ℓ))‖ ≤ 1 := by
      have := P1 (q : ℤ_[q])
      rw [zc_natCast_eq] at this
      exact this q
    refine le_antisymm hle (not_lt.1 fun hlt => ?_)
    have P3' := P3 hlt
    set k : ℕ := d + 3 with hk
    obtain ⟨β, N, hβ, hβ0, hβn, hN, hNle⟩ := exists_small_in_prime_pow d q M.ι hd hd16 hs k
    have ar := okArith d q M.ι hd hd16 hs
    obtain ⟨a, ha⟩ := (ar.2.1 β hβ).1
    have hanorm : ‖a‖ ≤ (q : ℝ) ^ (-(k : ℤ)) := by
      rw [← norm_zc_eq, ← ha]
      exact hβn
    have hlat : ∀ l ∈ M.L.lattice, β * l ∈ M.L.lattice := by
      intro l hl
      rw [hOK] at hl ⊢
      exact (ar.1.2.2 β l hβ hl).2.1
    have hu0 : AnalyticAt ℂ M.u 0 := (flow.2.2.2.2.2.2.2.2 0 (Or.inl ((hOK 0).2 ⟨0, 0, by simp⟩))).1
    have hhat : hat M.ι ℓ (fun z => M.u (β * z)) = U.subst (C (zc a) * ℓ) := by
      rw [(TaylorRead.hat_laws q M.ι ℓ hℓ0).2.2.2.2.2.1 M.u β hu0, ← ha]
      rfl
    have hbd : Bd 1 (hat M.ι ℓ (fun z => M.u (β * z))) := by
      rw [hhat]
      exact P1 a
    obtain ⟨n, hnN, hn1⟩ := _root_.GlobalTheory.MomOne.MulDegree.exists_unit_coeff q M ℓ β N hchart hβ0 hlat hN hbd
    have hnlt : n < (2 * q) ^ k := by
      have hq : 0 < q ^ k := pow_pos (Fact.out : q.Prime).pos k
      have h2 : d + 3 < 2 ^ k := Nat.lt_two_pow_self
      calc n ≤ N := hnN
        _ ≤ (d + 3) * q ^ k := hNle
        _ < 2 ^ k * q ^ k := Nat.mul_lt_mul_of_pos_right h2 hq
        _ = (2 * q) ^ k := (mul_pow 2 q k).symm
    have := P3' k a hanorm n hnlt
    rw [← hhat, hn1] at this
    exact lt_irrefl _ this
  · intro k hk
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · have hc : constantCoeff (C (q : ℂ_[q]) * ℓ) = 0 := by simp [hℓ0]
      rw [coeff_zero_eq_constantCoeff_apply, TaylorRead.constantCoeff_subst_of hc, hU0, norm_zero]
      exact one_pos
    · exact P2 k (Nat.not_dvd_of_pos_of_lt hkpos hk)

end GlobalTheory.MomOne
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.JetsOnCopiesOfCompatibleFrames
section
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

namespace GlobalTheory.PowJets

theorem exists_position_basis {X X' : Type} [AddCommGroup X] [AddCommGroup X'] {n r : ℕ} (xe : X' ≃+ (Fin n → X))
    (b : Module.Basis (Fin r) ℤ X) :
    ∃ (r' : ℕ) (b' : Module.Basis (Fin r') ℤ X'), ∀ k, ∃ i j, xe (b' k) = Pi.single i (b j) := by
  classical
  let B : Module.Basis (Σ _ : Fin n, Fin r) ℤ (Fin n → X) := Pi.basis fun _ => b
  refine ⟨_, (B.map xe.toIntLinearEquiv.symm).reindex (Fintype.equivFin _), fun k => ?_⟩
  refine ⟨((Fintype.equivFin (Σ _ : Fin n, Fin r)).symm k).1, ((Fintype.equivFin (Σ _ : Fin n, Fin r)).symm k).2, ?_⟩
  simp [B, Pi.basis_apply]

theorem sum_single_add {X : Type} [AddCommGroup X] {n : ℕ} (Q : X → ℤ) (i : Fin n) (x : X) (w : Fin n → X) :
    ∑ k, Q ((Pi.single i x + w : Fin n → X) k) = ∑ k, Q (w k) + (Q (x + w i) - Q (w i)) := by
  classical
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), ← Finset.add_sum_erase _ (fun k => Q (w k)) (Finset.mem_univ i),
    Finset.sum_congr rfl (g := fun k => Q (w k)) fun k hk => by
      rw [Pi.add_apply, Pi.single_eq_of_ne (Finset.ne_of_mem_erase hk), zero_add]]
  simp only [Pi.add_apply, Pi.single_eq_same]
  ring

theorem exists_basis_bounds {X X' : Type} [AddCommGroup X] [AddCommGroup X'] {n r : ℕ} (xe : X' ≃+ (Fin n → X))
    (Q : X → ℤ) (h0 : Q 0 = 0) (hQ : ∀ x, 0 ≤ Q x) (Φ M0 : ℝ) (b : Module.Basis (Fin r) ℤ X)
    (hΦ : ∀ j, (Q (b j) : ℝ) ≤ Φ) (hM : ∀ j z, |((Q (b j + z) - Q (b j) - Q z : ℤ) : ℝ)| ≤ M0 * Q z) :
    ∃ (r' : ℕ) (b' : Module.Basis (Fin r') ℤ X'), (∀ j, (sumQ xe Q (b' j) : ℝ) ≤ Φ) ∧
      ∀ j w, |((sumQ xe Q (b' j + w) - sumQ xe Q (b' j) - sumQ xe Q w : ℤ) : ℝ)| ≤ max M0 0 * sumQ xe Q w := by
  obtain ⟨r', b', hb⟩ := exists_position_basis xe b
  have e1 : ∀ k i j, xe (b' k) = Pi.single i (b j) → sumQ xe Q (b' k) = Q (b j) := fun k i j h => by
    have := sum_single_add Q i (b j) 0
    simpa [sumQ, h, h0] using this
  refine ⟨r', b', fun k => ?_, fun k w => ?_⟩
  · obtain ⟨i, j, h⟩ := hb k
    rw [e1 k i j h]
    exact hΦ j
  · obtain ⟨i, j, h⟩ := hb k
    have e2 : sumQ xe Q (b' k + w) = sumQ xe Q w + (Q (b j + xe w i) - Q (xe w i)) := by
      unfold sumQ
      rw [map_add (f := _), h]
      exact sum_single_add Q i (b j) (xe w)
    have e3 : sumQ xe Q (b' k + w) - sumQ xe Q (b' k) - sumQ xe Q w = Q (b j + xe w i) - Q (b j) - Q (xe w i) := by
      rw [e1 k i j h, e2]; ring
    have e4 : Q (xe w i) ≤ sumQ xe Q w :=
      Finset.single_le_sum (f := fun k => Q (xe w k)) (fun k _ => hQ _) (Finset.mem_univ i)
    rw [e3]
    refine (hM j _).trans (mul_le_mul (le_max_left _ _) (by exact_mod_cast e4) (by exact_mod_cast hQ _) (le_max_right _ _))

theorem jets_on_copies : Laws → Laws2 → Laws4 → TwistBaseChangeStatement → JetsOnCopiesCompatibleFrames := by
  intro L1 L2 L4 TB E _ _ _ H Dw l Xo c inst hstar
  obtain rfl : inst = H.starRing := starSt E H inst hstar
  letI := H.starRing
  intro T io y _ C htr P ϖ hϖ Q hQ Φ M0 r b hΦ0 hΦ hM n _ D' A' G' _ _ pD pA pG U' PU F _ _ _ _ _ v hv q D hq hD f hf
  choose f₀ hf₀ using hf
  obtain ⟨τ, hτ, htrunc, hgerm⟩ := frameNSt_holds E H T.V C.I.G P (chD C.ch) C.FT C.actT C.ph1T C.ph2T C.syT C.adT C.tgT
    C.xT C.eT C.wPT C.chartT C.frameT C.primT n D' A' G' pD pA pG U' PU
  have hu := _root_.GlobalTheory.PowGerm.univPow T.V C.I.G.G G' n (chD C.ch) pG C.xT (_root_.GlobalTheory.PowGerm.univSt_holds E H Dw l Xo c T io y C)
  obtain ⟨r', b', h1, h2⟩ := exists_basis_bounds pD.xe Q (Q_zero hϖ P.D hQ) (RoundingSumAlt.Q_nonneg hϖ hQ) Φ M0 b hΦ hM
  have hD' : (D : ℝ) * max M0 0 < q := by
    rcases le_total M0 0 with h | h
    · rw [max_eq_right h, mul_zero]
      exact_mod_cast (by omega : 0 < q)
    · rwa [max_eq_left h]
  obtain ⟨s, σ', g, lam, a1, a2, a3, a4, a5, a6⟩ := GlobalTheory.UnifJets.jets L1 L2 L4 TB T.V ϖ hϖ D' A' G' U' (Fin n × Fin (chD C.ch))
    (zV pG C.xT) hu τ hτ (htrunc htr) (sumQ pD.xe Q) (GlobalTheory.QBox.main T.V ϖ hϖ n P.D D' pD Q hQ) Φ (max M0 0) r' b' hΦ0
    (le_max_right _ _) h1 h2 F v hv q D hq hD' (fun e => f₀ e)
  refine ⟨s, σ', g, lam, a1, a2, (hgerm F q σ' g).2 a3, a4, a5, fun e he => ?_⟩
  rw [a6 e he, map_smul, MvPowerSeries.coeff_map, ← hf₀ e, smul_eq_mul, ← IsScalarTower.algebraMap_apply]
  rfl

end GlobalTheory.PowJets
end
end

