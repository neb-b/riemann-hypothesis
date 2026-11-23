module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TWMain
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PeriodicValuation
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0014
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullGenPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsIntegralSectionUnitAt
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0089
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ValueAtZeroOfSectionValue
public import Formalism.SharpRestriction.Divisibility.ModuliIntegralCharts
public import Formalism.SharpRestriction.Divisibility.WeightFamilies
public import Development.AbelianVarietyTheory.BlockTheory.JetGauges.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdBox
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ProdSumReindex
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0087
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0086
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0067
public import Formalism.PeriodIntegrals.Bundle0011
public import Formalism.PeriodIntegrals.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0063
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DiscreteSeriesParameterUnique
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0039
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ContinuousMulMt
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0076

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsValEqOfNonneg
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ExactTerm

section

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
  {D : DegData V (maximalIdeal V)} {Q : D.toPre.X → ℤ} {F : Type} [Field F] [Algebra (FractionRing V) F]
  {v : AddValuation F (WithTop ℚ)}

theorem exists_val_eq_of_nonneg [IsAlgClosed F] (hv : ValOver ϖ F v) {r : ℚ} (hr : 0 ≤ r) :
    ∃ c : F, v c = ((r : ℚ) : WithTop ℚ) := by
  rcases hr.eq_or_lt with rfl | hr
  · exact ⟨1, by rw [AddValuation.map_one]; rfl⟩
  · obtain ⟨c, -, hc⟩ := exists_val_eq hv hr
    exact ⟨c, hc⟩

theorem nuGe_of_single (hϖ : Irreducible ϖ) (hQ : QForm.IsQ D.toPre ϖ Q) (hv : ValOver ϖ F v) {k : ℕ} (hk : 1 ≤ k)
    (s : Fam D.toPre F k) (α : D.toPre.X) (r : ℚ)
    (hs : ∀ β : D.toPre.X, (∀ mu, α + k • mu ≠ β) → ∀ j, (s.s β).f j = 0)
    (h : VGe D F v k α (s.s α) (r + (Q α : ℚ) / k)) : NuGe D Q F v k s r := by
  intro β
  by_cases hβ : ∃ mu, α + k • mu = β
  · obtain ⟨m0, rfl⟩ := hβ
    have H := SectionScalarValuation.fe_move hϖ hQ hv k m0 α s h
    have hk0 : (k : ℚ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
    have e : r + (Q α : ℚ) / k + ((k * Q m0 + QForm.bOf D.toPre Q m0 α : ℤ) : ℚ) = r + (Q (α + k • m0) : ℚ) / k := by
      rw [q_shift hϖ hQ α m0 k]; push_cast; field_simp; ring
    rwa [e] at H
  · exact vge_of_zero (hs β fun mu e => hβ ⟨mu, e⟩) _

theorem pullAl_zero {O : Type} [Ring O] [StarRing O] [Module O D.toPre.X] {oa : D.toPre.OAct O} {a : O} {k N : ℕ}
    {s : Fam D.toPre F k} {s' : Fam D.toPre F (k * N)} (h : PullAl D F oa a k N s s') (χ : D.toPre.X)
    (h0 : ∀ j, (s.s χ).f j = 0) : ∀ j, (s'.s (star a • χ)).f j = 0 := by
  intro j
  obtain ⟨u, -, -, hrel⟩ := h.1 χ
  refine sec_ext_val (s' := SecOps.secZero) D.toPre.P.isLB (fun y J hJ => ?_) j
  rw [(secRel_iff D.toPre.P.isLB _ _ _ _ _ _ _ _ _ u).1 hrel _ (𝟙 _) y J hJ,
    UUA.sval_zero_of h0 _ y J (hJ.mem _ _), UUA.sval_zero_of (s := SecOps.secZero) (fun _ => rfl) _ y J (hJ.mem _ _),
    MulZeroClass.zero_mul]

theorem phiRel_zero (hG : GlobalFnsSt) {k : ℕ} {p : QkPt D.toPre F k}
    {w : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F p.g.b) (DegPre.lineε k))} (hw : w.IsGen)
    {s t : Fam D.toPre F k} (h : PhiRel D.toPre F k p w s t) (α : D.toPre.X)
    (h0 : ∀ j, (s.s α).f j = 0) : ∀ j, (t.s (α + p.y)).f j = 0 := by
  intro j
  obtain ⟨⟨u, hu, hc⟩, -⟩ := gen_phi hG p w hw α
  refine sec_ext_val (s' := SecOps.secZero) D.toPre.P.isLB (fun y J hJ => ?_) j
  rw [(secRel_iff D.toPre.P.isLB _ _ _ _ _ _ _ _ _ u).1 (h α u hu hc) _ (𝟙 _) y J hJ,
    UUA.sval_zero_of h0 _ y J (hJ.mem _ _), UUA.sval_zero_of (s := SecOps.secZero) (fun _ => rfl) _ y J (hJ.mem _ _),
    MulZeroClass.zero_mul]

end

theorem main : Laws → TwistBCSpanStatement → TWM.VRatioGtStatement → UUStatement → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V) (hϖ : Irreducible ϖ) (D : DegData V (maximalIdeal V)) (Q : D.toPre.X → ℤ), QForm.IsQ D.toPre ϖ Q → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ)) (hv : ValOver ϖ F v) (O : Type) [CommRing O] [StarRing O] [Module O D.toPre.X] (oa : D.toPre.OAct O) (w0 : O), TraceFormTwistIso D.toPre oa w0 → ∀ (a : O) (N k : ℕ), 1 ≤ N → 4 ≤ k → a * star a = (N : O) → ∀ (p : QkPt D.toPre F (k * N)) (w : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F p.g.b) (DegPre.lineε (k * N)))), w.IsGen → ∀ ζ : F, ζ ≠ 0 → FinOrd D F (k * N) p w ζ → ∀ χ₀ : D.toPre.X, ∃ s : Fam D.toPre F k, NuGe D Q F v k s 0 ∧ ∀ s' t h : Fam D.toPre F (k * N), PullAl D F oa a k N s s' → PhiRel D.toPre F (k * N) p w s' t → Fam.IsSmul D.toPre F ζ t h → NuGe D Q F v (k * N) h 0 ∧ (∀ β : D.toPre.X, (∀ z, β ≠ p.y + star a • χ₀ + k • star a • z) → ∀ j, (h.s β).f j = 0) ∧ ∃ x : F, Val0 D F (k * N) (star a • χ₀ + p.y) (h.s (star a • χ₀ + p.y)) x ∧ v x = (((Q (star a • χ₀ + p.y) : ℚ) / (k * N) : ℚ) : WithTop ℚ) := by
  intro hL hTW hVR hUU V _ _ _ ϖ hϖ D Q hQ F _ _ _ v hv O _ _ _ oa w0 hw0 a N k hN hk haa p w hw ζ hζ hfin χ₀
  have hG := hL.globalFns
  have hk1 : 1 ≤ k := by omega
  have hkN : 1 ≤ k * N := Nat.mul_pos hk1 hN
  have haa' : star a * a = (N : O) := by rw [mul_comm, haa]
  obtain ⟨m, hm⟩ := TWM.exists_liftO hϖ hv (D := D) p.g.b
  obtain ⟨σ, hσ, G₀, hG₀, x, hx, hval⟩ :=
    GlobalTheory.exists_integral_section_unit_at hL hTW V ϖ hϖ D Q hQ F v hv k hk χ₀ (m ≫ oa.onB.act a)
  have hQ0 : (0 : ℚ) ≤ Q χ₀ := by
    by_cases hχ : χ₀ = 0
    · subst hχ; rw [QForm.Q_zero hϖ D hQ]; simp
    · have := QForm.Q_pos hϖ D hQ hχ; exact_mod_cast (by omega : (0 : ℤ) ≤ Q χ₀)
  obtain ⟨c, hc⟩ := exists_val_eq_of_nonneg hv (div_nonneg hQ0 (Nat.cast_nonneg k))
  obtain ⟨s₀, rfl, hs₀⟩ := GlobalTheory.FamFree.exists_fam_single hG D.tau_bimult hk1 χ₀ σ
  have hsupp : ∀ β : D.toPre.X, (∀ mu, χ₀ + k • mu ≠ β) → ∀ j, ((c • s₀).s β).f j = 0 := fun β hβ j => by
    rw [smul_f, hs₀ β hβ j, mul_zero]
  have hnu : NuGe D Q F v k (c • s₀) 0 :=
    nuGe_of_single hϖ hQ hv hk1 _ χ₀ 0 hsupp (hσ.smul hc.ge fun j => rfl)
  refine ⟨c • s₀, hnu, fun s' t h hP hΦ hsm => ⟨?_, fun β hβ j => ?_, ?_⟩⟩
  · exact (galois_fixed_adelic_matrices_descend hL (TWM.tw_of hG hTW hVR) V ϖ hϖ D Q hQ F v hv (k * N) hkN p w hw ζ hζ hfin s' t h hΦ hsm 0).1
      (pullback_valuation_forward_of (pullGen_of hG) (QuadraticAlgebraValuation.qAl_of hL) V ϖ hϖ D Q hQ F v hv O oa w0 hw0 a N hN haa haa' k hk1
        _ s' hP 0 hnu)
  · obtain ⟨α, rfl⟩ : ∃ α, α + p.y = β := ⟨β - p.y, sub_add_cancel _ _⟩
    have h1 : ∀ j, (s'.s α).f j = 0 := by
      by_cases hα : ∃ χ, α = star a • χ
      · obtain ⟨χ, rfl⟩ := hα
        refine pullAl_zero hP χ (hsupp χ ?_)
        rintro mu rfl
        refine hβ mu ?_
        rw [smul_add, smul_comm (star a) k mu]
        abel
      · exact hP.2 α fun χ e => hα ⟨χ, e⟩
    refine (hsm _ j).trans ?_
    rw [phiRel_zero hG hw hΦ α h1 j]
    exact mul_zero _
  · have hpull := GlobalTheory.pullAl_value_integral_point hL V ϖ hϖ D Q hQ F v hv O oa w0 hw0 a N k hN hk1 haa _ s' hP χ₀ m
      ((Q χ₀ : ℚ) / k) ⟨G₀, hG₀, c * x, by rw [AddValuation.map_mul, hc, hx, ← WithTop.coe_add, add_zero],
        fun z J hJ => by
          rw [sval_smul c s₀ χ₀ _ z hJ, hval z J hJ, ← Over.comp_left, lift_fst, Over.id_left, map_mul,
            gs_mul _ z ⊤ trivial, _root_.mul_assoc]⟩
    obtain ⟨y, hy, hvy⟩ := GlobalTheory.PhiValue.main hL hTW hVR hUU V ϖ hϖ D Q hQ F v hv (k * N) hkN p w hw ζ hζ hfin
      s' t h hΦ hsm (star a • χ₀) m hm _ hpull
    refine ⟨y, hy, hvy.trans (congrArg _ ?_)⟩
    have hk0 : (k : ℚ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
    have hN0 : (N : ℚ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
    rw [QuadraticAlgebraValuation.qAl_of hL V ϖ hϖ D Q hQ O oa a N haa haa' χ₀]
    push_cast
    field_simp
    ring

end GlobalTheory.ExactTerm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.FunctionalValuesNonempty
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LeastExponentCompare

open NumberField Formalism.MainNotions.ModuliIntegralCharts
open GlobalTheory.IndefiniteRowSideFullHecke.TraceFormDualSystem (bar balancedForms quad IsPosSemidef IsPosDef Exponent pairing pairingValues IsPhiC)
open GlobalTheory.IndefiniteRowSideFullHecke.BalancedHermitianSpace (IsBalancedSpace evalSum)
open GlobalTheory.IndefiniteRowSideFullHecke.PairingFromOuterAgreement (outer IsPosHerm)

variable {E : Type} [Field E] [NumberField E]

theorem finite_projective_iff (Y : Type) [AddCommGroup Y] [Module (𝓞 E) Y] :
    (Module.Finite (𝓞 E) Y ∧ Module.Projective (𝓞 E) Y) ↔ (Module.Finite ℤ Y ∧ Module.Free ℤ Y) := by
  constructor
  · rintro ⟨hf, hp⟩
    have hfin : Module.Finite ℤ Y := Module.Finite.trans (𝓞 E) Y
    have hfl : Module.Flat ℤ Y := Module.Flat.trans ℤ (𝓞 E) Y
    exact ⟨hfin, inferInstance⟩
  · rintro ⟨hf, hfr⟩
    exact ⟨Module.Finite.of_restrictScalars_finite ℤ (𝓞 E) Y, GlobalTheory.PointStepCompare.projective_of_free E⟩

variable [IsCMField E] {cj : E → E}

def IsConj (cj : E → E) : Prop := ∀ c : 𝓞 E, cj c = IsCMField.complexConj E (c : E)

variable {Y : Type} [AddCommGroup Y] [Module (𝓞 E) Y]

theorem isBalancedSpace (h : IsConj cj) : IsBalancedSpace E (SymB cj Y) := by
  intro β
  change ((∀ a b, β a b = β b a) ∧ ∀ (c c' : 𝓞 E), (c' : E) = cj (c : E) → ∀ a b, β (c • a) b = β a (c' • b)) ↔ _
  constructor
  · rintro ⟨hs, hb⟩
    refine ⟨hs, fun a x y => hb a _ ?_ x y⟩
    rw [h a, IsCMField.coe_ringOfIntegersComplexConj]
  · rintro ⟨hs, hb⟩
    refine ⟨hs, fun c c' hc x y => ?_⟩

    have hc' : c' = IsCMField.ringOfIntegersComplexConj E c := by
      apply RingOfIntegers.ext
      rw [hc, h c, IsCMField.coe_ringOfIntegersComplexConj]
    rw [hc']
    exact hb c x y


variable (Y) in
def formsEquiv (h : IsConj cj) : SymB cj Y ≃ₗ[ℝ] balancedForms E Y where
  toFun β := ⟨AddMonoidHom.mk' (fun x => ((β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) x).toAddMonoidHom)
      (fun x x' => by ext y; simp),
    ((isBalancedSpace h _).1 β.2).1, ((isBalancedSpace h _).1 β.2).2⟩
  invFun β := ⟨LinearMap.mk₂ ℤ (fun x y => β.1 x y) (fun _ _ _ => by simp) (fun _ _ _ => by simp)
      (fun _ _ _ => by simp) (fun _ _ _ => by simp),
    (isBalancedSpace h _).2 ⟨β.2.1, β.2.2⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

def Admissible (l : SymB cj Y →ₗ[ℝ] ℝ) : Prop :=
  (∀ β : SymB cj Y, (∀ a c, ∃ z : ℤ, (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) a c = z) → ∃ z : ℤ, l β = z) ∧
    ∀ β : SymB cj Y, (∀ a, 0 ≤ (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) a a) → β ≠ 0 → 0 < l β

def functionalValues (b : SymB cj Y) : Set ℝ := {x | ∃ l : SymB cj Y →ₗ[ℝ] ℝ, Admissible l ∧ x = l b}

variable [Module.Finite (𝓞 E) Y] [Module.Projective (𝓞 E) Y]

theorem functionalValues_nonempty (h : IsConj cj) (b : SymB cj Y) : (functionalValues b).Nonempty := by
  obtain ⟨_, _⟩ := (finite_projective_iff (E := E) Y).1 ⟨inferInstance, inferInstance⟩
  obtain ⟨l, hi, hp⟩ := GlobalTheory.PointStepCompare.exists_admissible E (isBalancedSpace (Y := Y) h)
  exact ⟨l b, l, ⟨hi, hp⟩, rfl⟩

section Host

open Formalism.BasicNotions

end Host

end GlobalTheory.LeastExponentCompare

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ImportsBis
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.BoxSectionValues

open GlobalTheory.FieldBaseChange GlobalTheory.BoxExpansion


set_option maxHeartbeats 1000000 in
theorem main : Laws → Laws2 → Laws4 → TwistBaseChangeStatement → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] (j : ℕ) (D D' : DegData V (maximalIdeal V)) (A A' : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G G' : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] (pD : IsPowDeg D'.toPre D.toPre j) (pA : IsPowPolAV A' A j) (pG : IsPowGrp G' G j) (U' : Unif (maximalIdeal V) D' A' G') (U : Unif (maximalIdeal V) D A G) (PU : UnifPowOf3 pD pA pG U' U) (F : Type) [Field F] [Algebra (FractionRing V) F] (k : ℕ), 1 ≤ k → ∀ (σ : Fin j → U.SecGF F k) (s : Fin j → Fam D.toPre F k) (σ' : U'.SecGF F k) (S : Fam D'.toPre F k), (∀ i, U.ExpandsG F k (σ i) (s i)) → IsBoxFam pD F k S s → U'.ExpandsG F k σ' S → ∀ (Z : Scheme.{0}) (r : Z ⟶ (UnifPre.GF (R := V) (G := G') F).left) (ri : Fin j → (Z ⟶ (UnifPre.GF (R := V) (G := G) F).left)), (∀ i, ri i ≫ UnifPre.gFK (G := G) F = r ≫ UnifPre.gFK (G := G') F ≫ (pG.pr i).left) → (∀ i, ri i ≫ (fst (TFK (R := V) F) ((Over.pullback (jK V)).obj G)).left = r ≫ (fst (TFK (R := V) F) ((Over.pullback (jK V)).obj G')).left) → ∀ (z : Z) (J J'), Good U.LG.L z J → Good U'.LG.L z J' → (bw PU.wL (r ≫ UnifPre.gFK (G := G') F) z (fun i => J ((r ≫ UnifPre.gFK (G := G') F) ≫ (pG.pr i).left)) (J' (r ≫ UnifPre.gFK (G := G') F)) ^ k).val * sval σ' r z J' = ∏ i, sval (σ i) (ri i) z J := by
  intro h₁ h₂ h₄ hT V _ _ _ _ j D D' A A' G G' _ _ _ _ pD pA pG U' U P F _ _ k hk t s t' S hE hS hE' Z r ri hr₁ hr₂
    z J J' hJ hJ'
  classical
  choose n c σ f hA hs hf using hE
  let e := (Fintype.equivFin (∀ i, Fin (n i))).symm
  let σ' := fun l => boxSecG pG P.wL P.wL_gen U.LG.isLB U'.LG.isLB k (fun i => σ i (e l i))
  obtain ⟨s', hs'⟩ := exists_secLin U'.LG.isLB (fst (TFK (R := V) F) ((Over.pullback (jK V)).obj G')).left
    (UnifPre.gFK (G := G') F) (fun _ : Fin 1 => UnifPre.gFK (G := G') F) (fun _ => (Category.comp_id _).symm) σ'
    (fun l => (1 : F) * ∏ i, c i (e l i))
  have hX : U'.ExpandsG F k s' ((1 : F) • S) := by
    refine ⟨_, _, σ', fun l => boxFamB pD k (fun i => f i (e l i)), fun l ee => ?_, hs', fun α' => ?_⟩
    · exact expandsAt_box' P k ee _ _ (fun i => hA i (e l i) ee) _ _
        (isBoxSecG_boxSecG pG P.wL P.wL_gen U.LG.isLB U'.LG.isLB k _) (isBoxFamB_boxFamB pD k _)
    · obtain ⟨hφ, hb⟩ := hS α'
      refine secLin_box e (1 : F) c D.toPre.P.isLB D'.toPre.P.isLB pD.w
        (p := prB pD F) (q := fun i => (pD.pw.pr i).left) (GC.famφ_eq D'.toPre F α') (fun i => ?_) (fun i => ?_)
        (S.s α') _ (fun i => (s i).s (pD.xe α' i)) (fun i a => f i a (pD.xe α' i)) _ (fun _ => rfl)
        (fun y J J' hJ hJ' => box_val pD.w hφ _ _ _ hb (𝟙 _) y hJ hJ') (fun l y J J' hJ hJ' => ?_)
        (fun i => hf i (pD.xe α' i))
      · exact congrArg (fun q => q.left) (whiskerLeft_snd (TF (R := V) F) (pD.pw.pr i)).symm
      · exact congrArg (fun q => q.left) (whiskerLeft_fst (TF (R := V) F) (pD.pw.pr i))
      · obtain ⟨hψ, H⟩ := isBoxFamB_boxFamB pD k (fun i => f i (e l i)) α'
        exact box_val pD.w hψ _ _ _ H _ y hJ hJ'
  rw [one_smul] at hX
  obtain rfl : t' = s' := ((_root_.GlobalTheory.expandsG_bijective_of_dvr h₁ h₂ h₄ hT V D' A' G' U' F k hk).2 S).unique hE' hX
  have a₂ := fun l => boxG_val (isBoxSecG_boxSecG pG P.wL P.wL_gen U.LG.isLB U'.LG.isLB k (fun i => σ i (e l i)))
    (r ≫ UnifPre.gFK (G := G') F) z hJ hJ'
  have a₃ : ∀ i, sval (t i) (ri i) z J = ∑ a, constHomVal (r ≫ (fst (TFK (R := V) F)
      ((Over.pullback (jK V)).obj G')).left) z (c i a) *
        sval (σ i a) ((r ≫ UnifPre.gFK (G := G') F) ≫ (pG.pr i).left) z J := fun i => by
    refine (secLin_val (hs i) (ri i) z hJ).trans (Finset.sum_congr rfl fun a _ => ?_)
    rw [hr₁ i, ← Category.assoc]
    exact congrArg (· * _) ((gs_scal _ _ z _).trans ((congrArg (fun q => constVal q z (c i a)) (hr₂ i)).trans
      (constVal_eq _ _ _)))
  have a₄ : sval t' r z J' = ∑ l, constHomVal (r ≫ (fst (TFK (R := V) F)
      ((Over.pullback (jK V)).obj G')).left) z (1 * ∏ i, c i (e l i)) *
        sval (σ' l) (r ≫ UnifPre.gFK (G := G') F) z J' := by
    refine (secLin_val hs' r z hJ').trans (Finset.sum_congr rfl fun a _ => ?_)
    exact congrArg (· * _) ((gs_scal _ _ z _).trans (constVal_eq _ _ _))
  have a₅ := prod_sum_reindex (constHomVal (r ≫ (fst (TFK (R := V) F)
      ((Over.pullback (jK V)).obj G')).left) z) e 1 c
      (fun i a => sval (σ i a) ((r ≫ UnifPre.gFK (G := G') F) ≫ (pG.pr i).left) z J)
  rw [map_one, _root_.one_mul] at a₅
  rw [Finset.prod_congr rfl fun i _ => a₃ i, ← a₅, a₄, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by rw [← a₂ l, mul_left_comm]

end GlobalTheory.BoxSectionValues
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsometricBesselCompare
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.BesselOrth

section L2

variable {X E : Type} [MeasurableSpace X] {ν : Measure X} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem inner_toLp {f g : X → E} (hf : MemLp f 2 ν) (hg : MemLp g 2 ν) :
    ⟪hf.toLp f, hg.toLp g⟫_ℂ = ∫ x, ⟪f x, g x⟫_ℂ ∂ν := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x h1 h2
  rw [h1, h2]

theorem integrable_inner {f g : X → E} (hf : MemLp f 2 ν) (hg : MemLp g 2 ν) :
    Integrable (fun x => ⟪f x, g x⟫_ℂ) ν := by
  refine (L2.integrable_inner (𝕜 := ℂ) (hf.toLp f) (hg.toLp g)).congr ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x h1 h2
  rw [h1, h2]

theorem norm_toLp_eq {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {f : X → E} (hf : MemLp f 2 ν)
    {a : H} (h : ∫ x, ⟪f x, f x⟫_ℂ ∂ν = ⟪a, a⟫_ℂ) : ‖hf.toLp f‖ = ‖a‖ := by
  rw [← inner_toLp hf hf] at h
  rw [@norm_eq_sqrt_re_inner ℂ, @norm_eq_sqrt_re_inner ℂ, h]

theorem norm_integral_inner_le {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] {f g : X → E} (hf : MemLp f 2 ν) (hg : MemLp g 2 ν)
    {a : H} {b : H'} (h : ∫ x, ⟪f x, f x⟫_ℂ ∂ν = ⟪a, a⟫_ℂ) (h' : ∫ x, ⟪g x, g x⟫_ℂ ∂ν = ⟪b, b⟫_ℂ) :
    ‖∫ x, ⟪f x, g x⟫_ℂ ∂ν‖ ≤ ‖a‖ * ‖b‖ := by
  rw [← inner_toLp hf hg, ← norm_toLp_eq hf h, ← norm_toLp_eq hg h']
  exact norm_inner_le_norm _ _

end L2

end GlobalTheory.BesselOrth

namespace GlobalTheory

open BesselOrth Formalism.FourierDecayAlt.P

theorem bessel_orth_of_param_ne : Hyps → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (mu' : Fin (2 * r + k + 1) → ℝ) (R R' : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (Bm : R.H → Wp) (Bm' : R'.H → Wp), R.IsDS ε mu → R'.IsDS ε mu' → mu ≠ mu' → SideG k r z π u μW μN μG νq → IsIsoB R z π νq Bm → IsIsoB R' z π νq Bm' → ∀ w ∈ R.sm, ∀ y ∈ R'.sm, ∫ x, ⟪Bm' (R'.σ (Matrix.of x) y), Bm (R.σ (Matrix.of x) w)⟫_ℂ ∂νq = 0 := by
  intro hH k r ε mu mu' R R' Wp _ _ _ _ z π u μW μN μG νq Bm Bm' hR hR' hne hS hB hB'
  have hK : PI.KFinSmooth := hH.1.2.2.1
  have hP : Poulsen := hH.2.2.2.2.2.1
  obtain ⟨hL, hI⟩ := GlobalTheory.T.isometric_bessel_memLp_and_integral_inner_eq hK k r ε mu R Wp z π u μW μN μG νq Bm hR hS hB
  obtain ⟨hL', hI'⟩ := GlobalTheory.T.isometric_bessel_memLp_and_integral_inner_eq hK k r ε mu' R' Wp z π u μW μN μG νq Bm' hR' hS hB'
  have hq := _root_.GlobalTheory.quot_integral_rmul k r Wp z π u μW μN μG νq
  obtain ⟨⟨ha, hs, he, hc⟩, -⟩ := hB
  obtain ⟨⟨ha', hs', he', hc'⟩, -⟩ := hB'
  have hco := GlobalTheory.T.frechetContinuous_continuousOn_orbit_hasDerivAt hK k r ε mu R hR Wp Bm ha hs hc
  have hco' := GlobalTheory.T.frechetContinuous_continuousOn_orbit_hasDerivAt hK k r ε mu' R' hR' Wp Bm' ha' hs' hc'
  have hae : ∀ᵐ x ∂νq, Matrix.of x ∈ GG k r := by
    obtain ⟨-, -, -, -, hW, hN, hG, hQ⟩ := hS
    exact DDSmoothness.ae_UH_of_quot hG.2.2.1 (DDSmoothness.muSof_facts hW hN).1 (DDSmoothness.muSof_facts hW hN).2 hQ
  have ht : ∀ w ∈ R.sm, ∀ g ∈ GG k r, R.σ g w ∈ R.sm := fun w hw g hg => TranslationBesselVanishing.smooth_translate hR.2 hw hg
  have ht' : ∀ w ∈ R'.sm, ∀ g ∈ GG k r, R'.σ g w ∈ R'.sm := fun w hw g hg => TranslationBesselVanishing.smooth_translate hR'.2 hw hg
  have hm : ∀ a ∈ GG k r, ∀ b ∈ GG k r, ∀ v, R.σ (a * b) v = R.σ a (R.σ b v) := fun a ha b hb v => by
    rw [TranslationBesselVanishing.sigma_mul hR.2 ha hb]; rfl
  have hm' : ∀ a ∈ GG k r, ∀ b ∈ GG k r, ∀ v, R'.σ (a * b) v = R'.σ a (R'.σ b v) := fun a ha b hb v => by
    rw [TranslationBesselVanishing.sigma_mul hR'.2 ha hb]; rfl
  have hform : IsInvForm R R' (fun w y =>
      ∫ x, ⟪Bm' (R'.σ (Matrix.of x) y), Bm (R.σ (Matrix.of x) w)⟫_ℂ ∂νq) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, 1, [[]], [[]], by simp, ?_⟩
    · intro w hw w' hw' y hy
      beta_reduce
      rw [← integral_add (integrable_inner (hL' y hy) (hL w hw)) (integrable_inner (hL' y hy) (hL w' hw'))]
      refine integral_congr_ae ?_
      filter_upwards [hae] with x hx
      rw [map_add (f := _), ha _ (ht w hw _ hx) _ (ht w' hw' _ hx), inner_add_right]
    · intro a w hw y hy
      beta_reduce
      rw [← integral_const_mul]
      refine integral_congr_ae ?_
      filter_upwards [hae] with x hx
      rw [map_smul, hs a _ (ht w hw _ hx), inner_smul_right]
    · intro w hw y hy y' hy'
      beta_reduce
      rw [← integral_add (integrable_inner (hL' y hy) (hL w hw)) (integrable_inner (hL' y' hy') (hL w hw))]
      refine integral_congr_ae ?_
      filter_upwards [hae] with x hx
      rw [map_add (f := _), ha' _ (ht' y hy _ hx) _ (ht' y' hy' _ hx), inner_add_left]
    · intro a w hw y hy
      beta_reduce
      rw [← integral_const_mul]
      refine integral_congr_ae ?_
      filter_upwards [hae] with x hx
      rw [map_smul, hs' a _ (ht' y hy _ hx), inner_smul_left]
      rfl
    · intro g hg w hw y hy
      beta_reduce
      have key := hq (fun x => ⟪Bm' (R'.σ x y), Bm (R.σ x w)⟫_ℂ) hS
        (ContinuousOn.inner (𝕜 := ℂ) (hco' y hy).1 (hco w hw).1) ?_ (integrable_inner (hL' y hy) (hL w hw)) g hg
      · rw [← key]
        refine integral_congr_ae ?_
        filter_upwards [hae] with x hx
        rw [hm _ hx _ hg, hm' _ hx _ hg]
      · rintro s ⟨h, hh, m, hmN, rfl⟩ x hx
        obtain ⟨-, hT, ⟨u₀, hπ⟩, -⟩ := hS
        have hsG : h * m ∈ GG k r := DDSmoothness.uh_mul hh.1 hmN.1
        have hiso : ∀ a b, ⟪π h a, π h b⟫_ℂ = ⟪a, b⟫_ℂ :=
          (LinearMap.norm_map_iff_inner_map_map ((π h : Wp →L[ℂ] Wp) : Wp →ₗ[ℂ] Wp)).1
            (MatrixMultiplicationContinuity.piW_unitary hT hπ h hh)
        have hψ := MatrixMultiplicationContinuity.psi_norm z Formalism.QuantumDeterminants.cStd m
        beta_reduce
        rw [hm _ hsG _ hx, hm' _ hsG _ hx, he h hh m hmN _ (ht w hw _ hx), he' h hh m hmN _ (ht' y hy _ hx),
          inner_smul_left, inner_smul_right, hiso, ← mul_assoc, Complex.conj_mul', hψ]
        simp
    · intro w hw y hy
      have := norm_integral_inner_le (hL' y hy) (hL w hw) (hI' y hy y hy) (hI w hw w hw)
      simpa [PI.UpqRep.dsigW, mul_comm] using this
  rcases (hP k r ε mu mu' R R' hR hR').2 _ hform with h | ⟨U, hU⟩
  · exact h
  · exact absurd (GlobalTheory.DSInequiv.param_eq_of_equiv hH k r ε mu mu' R R' hR hR' U hU) hne

end GlobalTheory

end
end

