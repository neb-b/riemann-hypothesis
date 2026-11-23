module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CmModelsSiegelFamilyComparison
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.OneAddZeta21PowSevenAddPowFourteenEqZero
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsCoprimeTwoSubRtTwoAddRt
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ToMatrixTrFormBaseChange
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0165
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0107
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0117
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0018
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0112
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0116
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0148
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0164
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ImInvIsHermitian
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPullbackDegenerationOfValuesIsoDvr
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.ThetaTowerRecognition
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0128
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SelfTorusExtensionCoordValuesEqOne
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0091
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationDegenerationDataUnique
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0116
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ToStkAInjective
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.CmModelsSiegelFamilyComparisonStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_models_siegel_family_comparison : Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (n N : ℕ) (T : Top Xo n N), ToroidalLevelCompatibility (H := H) (D := D) → ∀ p : ℕ, p.Prime → p ≠ n → n.Prime → (∃ e, N = n ^ e) → ∃ Ag : SiegelFamily (Module.finrank ℚ E / 2 * (D.p + D.q)) p N, ∀ (W : ValuationSubring ℂ) (l₀ : Level H) (B : BaseModel T l₀) (l l₁ : Level H) (c : Coeff l) (c₁ : Coeff l₁) (Y : Model (Xo l) c (c.V W).subtype) (Y₁ : Model (Xo l₁) c₁ (c₁.V W).subtype) (b : c.V W →+* c₁.V W) (z : ZP p N →+* c₁.V W) (π : Y₁.X ⟶ Y.X), (p : ℂ) ∈ W.nonunits → IsPrimeToPart l₀ l p → n.Coprime l.M → IsIncl b → (∀ x, (((z x : c₁.V W) : c₁.F) : ℂ) = (x : ℂ)) → l₁.M = l.M → l₁.Mb = l.Mb → l₁.A = Nat.lcm l.A N → c₁.F = c.F ⊔ IntermediateField.adjoin ℚ {zeta N} → Raises B Y → Raises B Y₁ → IsTransition Y Y₁ b π → SiegelCompare Y Y₁ b π Ag z := by
  first | exact @GlobalTheory.SiegelComparison.siegelCompare | exact GlobalTheory.SiegelComparison.siegelCompare | (intros; apply GlobalTheory.SiegelComparison.siegelCompare <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.E8SharpObjectFibreFromComplexCharZero
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.SharpFrom

private theorem countable_closure {K : Type} [Field K] (s : Set K) (hs : s.Countable) :
    Countable (Subfield.closure s) := by
  have hs' : Cardinal.mk s ≤ Cardinal.aleph0 := Cardinal.mk_le_aleph0_iff.2 hs.to_subtype
  rw [← Cardinal.mk_le_aleph0_iff]
  exact (Subfield.cardinalMk_closure_le_max s).trans (max_le hs' le_rfl)

private theorem countable_closure_union {K : Type} [Field K] (K₀ : Subfield K) [Countable K₀] (F : Finset K) :
    Countable (Subfield.closure ((K₀ : Set K) ∪ F)) := by
  have h₀ : (K₀ : Set K).Countable := Set.countable_coe_iff.1 ‹Countable K₀›
  exact countable_closure _ (h₀.union F.countable_toSet)

private theorem countable_of_finiteType (o : Type) [CommRing o] (h : Algebra.FiniteType ℤ o) : Countable o := by
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1 h
  have hP : Countable (MvPolynomial (Fin n) ℤ) := by
    rw [← Cardinal.mk_le_aleph0_iff]
    exact MvPolynomial.cardinalMk_le_max.trans
      (sup_le (sup_le Cardinal.mk_le_aleph0 Cardinal.mk_le_aleph0) le_rfl)
  exact hf.countable

private theorem sp_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R') (f' : R' →+* R'') :
    spMap f' ≫ spMap f = spMap (f'.comp f) := by
  simp only [spMap, ← Spec.map_comp]
  rfl

private theorem exists_sp {R R' : Type} [CommRing R] [CommRing R'] (y : Sp R' ⟶ Sp R) : ∃ f : R →+* R', y = spMap f := ⟨Spec.preimage y |>.hom, by simp [spMap]⟩

theorem fromC_sharpClass : Out.Laws → Out.Laws2 → ∀ (h g : ℕ) (W : Matrix (Fin 8) (Fin 8) ℤ) (J : Type) [Finite J] (a : J → Matrix (Fin 8) (Fin 8) ℤ) (w w' : J) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ))), IsE8 W → IsSharpBasis W bas → (W + W.transpose) * a w = W → (W + W.transpose) * a w' = W.transpose → (∀ u v, ∃ j, a j = Matrix.single u v 1) → ∀ (N' : ℕ) (o : Type) [CommRing o] (b : TBase o (N' ^ 2)) (em : o →+* ℂ), ArBase em → ∀ (S : Scheme.{0}) (s : S ⟶ Sp o) (t : TObj g (N' ^ 2) J b s) (c : SiegPre h (N' ^ 2) (b.ζ : o) s), c.Principal → IsSharp W a bas t c → ∀ (K : Type) [Field K] [CharZero K] (x : Sp K ⟶ S), FromC em (SharpClass (b := b) W a bas em) t x := by
  intro _ _ h g W J _ a _ _ bas _ _ _ _ _ N' o _ b em hem S s t c hc hsh K _ _ x
  obtain ⟨hded, hft, hinj⟩ := hem
  have : Countable o := countable_of_finiteType o hft

  obtain ⟨βK, hβK⟩ := exists_sp (x ≫ s)
  obtain ⟨tK, htK⟩ := _root_.GlobalTheory.tObj_pull o g (N' ^ 2) J b S (Sp K) s (spMap βK) x t hβK
  obtain ⟨cK, hcK, hshK⟩ := GlobalTheory.SharpPull.sharp_pull h g (N' ^ 2) W J a bas o b S (Sp K) s (spMap βK) x t tK c
    hβK htK hc hsh

  obtain ⟨K₀, β₀, t₀, hβ₀, hcount, -, ht₀⟩ := _root_.GlobalTheory.ThetaDescent.descends_to_fg_subfield o g (N' ^ 2) J b K βK tK
  subst hβ₀
  have : Countable K₀ := hcount ‹_›
  obtain ⟨F, hF⟩ := _root_.GlobalTheory.SiegDesc.siegPre_descends h (N' ^ 2) o (b.ζ : o) K K₀ (spMap β₀) (spMap (K₀.subtype.comp β₀)) cK
    (sp_comp _ _).symm hcK

  have hK : K₀ ≤ Subfield.closure ((K₀ : Set K) ∪ F) := fun z hz => Subfield.subset_closure (Or.inl hz)
  have hFK : (F : Set K) ⊆ Subfield.closure ((K₀ : Set K) ∪ F) := fun z hz => Subfield.subset_closure (Or.inr hz)
  obtain ⟨c₁, hc₁, hpb₁⟩ := hF _ hK hFK
  have : Countable (Subfield.closure ((K₀ : Set K) ∪ F)) := countable_closure_union K₀ F
  have move : ∀ s₁ : Sp (Subfield.closure ((K₀ : Set K) ∪ F)) ⟶ Sp o,
      s₁ = spMap ((Subfield.inclusion hK).comp β₀) → ∀ c₁ : SiegPre h (N' ^ 2) (b.ζ : o) s₁, c₁.Principal →
      SiegPB cK c₁ (spMap (Subfield.closure ((K₀ : Set K) ∪ F)).subtype) →
      ∃ c₂ : SiegPre h (N' ^ 2) (b.ζ : o) (spMap ((Subfield.inclusion hK).comp β₀)),
        c₂.Principal ∧ SiegPB cK c₂ (spMap (Subfield.closure ((K₀ : Set K) ∪ F)).subtype) := by
    rintro s₁ rfl c₂ h₁ h₂
    exact ⟨c₂, h₁, h₂⟩
  obtain ⟨c₁', hc₁', hpb₁'⟩ := move _ (sp_comp _ _) c₁ hc₁ hpb₁
  obtain ⟨t₁, ht₁⟩ := _root_.GlobalTheory.tObj_pull o g (N' ^ 2) J b (Sp K₀) (Sp (Subfield.closure ((K₀ : Set K) ∪ F)))
    (spMap β₀) (spMap ((Subfield.inclusion hK).comp β₀)) (spMap (Subfield.inclusion hK)) t₀ (sp_comp _ _)
  have hsub : (Subfield.closure ((K₀ : Set K) ∪ F)).subtype.comp (Subfield.inclusion hK) = K₀.subtype :=
    RingHom.ext fun _ => rfl
  have htK₁ : TMap tK t₁ (spMap (Subfield.closure ((K₀ : Set K) ∪ F)).subtype) := by
    refine ((_root_.GlobalTheory.ZM.tmap_id_comp_cancel o g (N' ^ 2) J b (Sp K₀) _ (Sp K) (spMap β₀) _ (spMap (K₀.subtype.comp β₀))
      t₀ t₁ tK).2 _ _ ht₁).2 ?_
    rw [sp_comp, hsub]
    exact ht₀
  have e₁ : spMap (K₀.subtype.comp β₀) =
      spMap (Subfield.closure ((K₀ : Set K) ∪ F)).subtype ≫ spMap ((Subfield.inclusion hK).comp β₀) := by
    rw [sp_comp]
    exact congrArg spMap (RingHom.ext fun _ => rfl)

  obtain ⟨F₂, β₂, t₂, c₂, e₂, ht₂, hc₂, hsh₂⟩ := GlobalTheory.SharpDescent.isSharp_descends h g (N' ^ 2) W J a bas o b K
    (Subfield.closure ((K₀ : Set K) ∪ F)) ((Subfield.inclusion hK).comp β₀) (spMap (K₀.subtype.comp β₀))
    tK cK t₁ c₁' e₁ htK₁ hpb₁' hc₁' hshK
  have : Countable (Subfield.closure ((Subfield.closure ((K₀ : Set K) ∪ F) : Set K) ∪ F₂)) :=
    countable_closure_union _ F₂

  obtain ⟨-, j, hj⟩ := _root_.GlobalTheory.exists_ringHom_complex_comp_eq_of_countable o em _ β₂ hded hft hinj
  have ej : spMap j ≫ spMap β₂ = spMap em := by rw [sp_comp, hj]
  obtain ⟨tc, htc⟩ := _root_.GlobalTheory.tObj_pull o g (N' ^ 2) J b _ (Sp ℂ) (spMap β₂) (spMap em) (spMap j) t₂ ej
  obtain ⟨cc, hcc, hshc⟩ := GlobalTheory.SharpPull.sharp_pull h g (N' ^ 2) W J a bas o b _ (Sp ℂ) (spMap β₂) (spMap em)
    (spMap j) t₂ tc c₂ ej htc hc₂ hsh₂

  obtain ⟨tx, htx⟩ := _root_.GlobalTheory.tObj_pull o g (N' ^ 2) J b S (Sp K) s (x ≫ s) x t rfl
  have htxK : TMap tx tK (𝟙 _) :=
    ((_root_.GlobalTheory.ZM.tmap_id_comp_cancel o g (N' ^ 2) J b S (Sp K) (Sp K) s _ _ t tK tx).2 x (𝟙 _) htK).2 (by rwa [Category.id_comp])
  have htx₂ : TMap tx t₂ (spMap (Subfield.subtype _)) := by
    have := ((_root_.GlobalTheory.ZM.tmap_id_comp_cancel o g (N' ^ 2) J b _ (Sp K) (Sp K) (spMap β₂) _ (x ≫ s) t₂ tK tx).2 _ (𝟙 _) ht₂).1 htxK
    rwa [Category.id_comp] at this
  exact ⟨_, inferInstance, β₂, Subfield.subtype _, j, t₂, tx, tc, hj, hβK.trans e₂, htx, htx₂, htc, cc, hcc, hshc⟩

end GlobalTheory.SharpFrom
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.EighthPowerThetaObjectOfUniformisation
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory

namespace SharpObj

theorem omegaStd_sum_smul {h : ℕ} {I : Type} [Fintype I] (x : Fin h ⊕ Fin h → ℤ) (c : I → ℤ)
    (y : I → Fin h ⊕ Fin h → ℤ) : omegaStd x (∑ v, c v • y v) = ∑ v, c v * omegaStd x (y v) := by
  simp only [omegaStd, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun i _ => ?_
  ring

theorem form_act {h : ℕ} (G A : Matrix (Fin 8) (Fin 8) ℤ) (x : Fin 8 → Fin h ⊕ Fin h → ℤ) :
    ∑ u, ∑ v, G u v * omegaStd (x u) (∑ v', A v v' • x v') = ∑ u, ∑ v, (G * A) u v * omegaStd (x u) (x v) := by
  refine Finset.sum_congr rfl fun u _ => ?_
  simp only [omegaStd_sum_smul, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul, _root_.mul_assoc]
  exact Finset.sum_comm

theorem exp_pi_I_int (n : ℤ) : Complex.exp (Real.pi * Complex.I * (n : ℂ)) = (-1) ^ n := by
  rw [_root_.mul_comm, Complex.exp_int_mul, Complex.exp_pi_mul_I]

theorem hermForm_eq_sum {g h : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (H₀ : Matrix (Fin h) (Fin h) ℂ)
    (G : Matrix (Fin 8) (Fin 8) ℤ) (R : Fin 8 → ((Fin g → ℂ) →ₗ[ℂ] (Fin h → ℂ))) (s : Set (Fin g → ℂ))
    (hs : Submodule.span ℝ s = ⊤)
    (h0 : ∀ z ∈ s, ∀ w ∈ s, (hermForm Hm z w).im = ∑ i, ∑ j, (G i j : ℝ) * (hermForm H₀ (R i z) (R j w)).im) (z w) :
    hermForm Hm z w = ∑ i, ∑ j, (G i j : ℂ) * hermForm H₀ (R i z) (R j w) := by
  refine sub_eq_zero.1 (form_ext s hs
    (fun z w => hermForm Hm z w - ∑ i, ∑ j, (G i j : ℂ) * hermForm H₀ (R i z) (R j w)) ?_ ?_ ?_ ?_ ?_ z w)
  · intro z z' w
    simp only [hermForm, map_add (f := _), add_dotProduct, mul_add, Finset.sum_add_distrib]
    ring
  · intro z w w'
    simp only [hermForm, map_add (f := _), star_add, Matrix.mulVec_add, dotProduct_add, mul_add, Finset.sum_add_distrib]
    ring
  · intro c z w
    simp only [hermForm, map_smul, smul_dotProduct, smul_eq_mul, mul_sub, Finset.mul_sum, mul_left_comm c]
  · intro c z w
    simp only [hermForm, map_smul, star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul, mul_sub,
      Finset.mul_sum, Complex.star_def, Complex.conj_ofReal, mul_left_comm (c : ℂ)]
  · intro z hz w hw
    simp [h0 z hz w hw, Complex.im_sum]

end SharpObj


open SharpObj in
theorem sharpClass_of_unif : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (em : o →+* ℂ) (w w' : J) (h : ℕ) (W : Matrix (Fin 8) (Fin 8) ℤ) (a : J → Matrix (Fin 8) (Fin 8) ℤ) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ))) (σ : Fin 8 × Fin h ≃ Fin g) (EF : LinearMap.BilinForm ℤ (Fin 8 → (Fin h ⊕ Fin h → ℤ))), IsE8 W → IsSharpBasis W bas → (W + W.transpose) * a w = W → (W + W.transpose) * a w' = W.transpose → (∀ x y, EF x y = ∑ u, ∑ v, (W + W.transpose) u v * omegaStd (x u) (y v)) → ∀ (t : TObj g k J b (spMap em)) (τ : Matrix (Fin h) (Fin h) ℂ) (m : (Fin h ⊕ Fin h → ℤ) →+ (Fin h ⊕ Fin h → ℤ)) (Q : (Fin 8 → (Fin h ⊕ Fin h → ℤ)) →+ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ), ((τ).IsSymm ∧ ((τ).map Complex.im).PosDef) → (∀ x y, Complex.exp (-(2 * Real.pi * Complex.I) * (omegaStd (m x) (m y) : ℂ) / k) = em (b.ζ : o) ^ omegaStd x y) → (∀ x u i, Q x (σ (u, i)) = (τ).mulVec (fun i' => (x u (.inl i') : ℂ)) i + (x u (.inr i) : ℂ)) → (Function.Injective Q ∧ DiscreteTopology (Q).range ∧ Submodule.span ℝ (Set.range Q) = ⊤ ∧ (Hm).IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧ ∀ x y, (hermForm Hm (Q x) (Q y)).im = EF x y) → (∃ (u : HolUnif t.A t.L g) (χ' : u.Λ → ℂ), u.IsAH Hm χ' ∧ (∀ z, z ∈ u.Λ ↔ z ∈ (Q).range) ∧ (∀ x (l : u.Λ), (l : Fin g → ℂ) = Q x → χ' l = (-1) ^ EF x ((fun j (x : (Fin 8 → (Fin h ⊕ Fin h → ℤ))) u => ∑ v, a j u v • x v) w x)) ∧ (∀ i₀, (t.pt i₀).left = (u.ex (((k : ℕ) : ℂ)⁻¹ • Q ((fun i u => m (bas (Pi.single i 1) u)) i₀))).left) ∧ ∀ j₀, ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), (∀ x, F (Q x) = Q ((fun j (x : (Fin 8 → (Fin h ⊕ Fin h → ℤ))) u => ∑ v, a j u v • x v) j₀ x)) ∧ ∀ z, u.ex (F z) = u.ex z ≫ t.act j₀) → SharpClass W a bas em t := by
  intro laws laws2 hc hT o _ g k J b em w w' h W a bas σ EF _ _ hw _ hEF t τ m Q Hm ⟨hs, hp⟩ hm hQ
    ⟨_, _, Qspan, _, _, hQim⟩ ⟨u, χ', hAH, hΛ, hχ, hpt, hact⟩
  obtain ⟨Ef₀, hEf₀, hbij⟩ := exists_form hs hp
  obtain ⟨P₀, u₀, χ₀, hg, hΛ₀, hAH₀, -, -⟩ := principalTorus_algebraic h _ (imInv τ) Ef₀ (per_lattice hs hp).2.1
    (per_lattice hs hp).2.2 (imInv_isHermitian hp) (imInv_pos hp) hEf₀ hbij
  subst hg
  let R : Fin 8 → (Fin g → ℂ) →ₗ[ℂ] (Fin P₀.g → ℂ) := fun i => LinearMap.funLeft ℂ ℂ fun j => σ (i, j)
  have hRQ : ∀ i x, R i (Q x) = per τ (x i) := fun i x => funext fun j => hQ x i j
  have hmem : ∀ x, per τ x ∈ u₀.Λ := fun x => hΛ₀ ▸ ⟨x, rfl⟩
  have hΛ' : ∀ z, z ∈ u.Λ ↔ ∀ i, (fun j => z (σ (i, j))) ∈ u₀.Λ := fun z => by
    rw [hΛ, hΛ₀]
    constructor
    · rintro ⟨x, rfl⟩ i
      exact ⟨x i, (hRQ i x).symm⟩
    · intro H
      choose x hx using H
      refine ⟨x, funext fun c => ?_⟩
      obtain ⟨⟨i, j⟩, rfl⟩ := σ.surjective c
      exact (hQ x i j).trans (congrFun (hx i) j)
  obtain ⟨pr, hpr, hpru, hprod⟩ := exists_proj laws laws2 hc hT t.pol P₀ u u₀ σ hΛ'
  change Fin 8 → (t.A ⟶ P₀.A) at pr
  change ∀ i, IsMonHom (pr i : t.A ⟶ P₀.A) at hpr
  change ∀ (T : Over (Sp ℂ)) (y : Fin 8 → (T ⟶ P₀.A)), ∃! x : T ⟶ t.A, ∀ i, x ≫ pr i = y i at hprod
  change ∀ i z, u₀.ex (R i z) = u.ex z ≫ pr i at hpru
  have hk : (k : ℂ) ≠ 0 := by simpa using (b.unit.map em).ne_zero
  have hk0 : 0 < k := Nat.pos_of_ne_zero fun e => hk (by simp [e])
  obtain ⟨Ef, hEf, -, -, -, -, -, -, hWeil⟩ := _root_.GlobalTheory.AnyAppellHumbert.isAH_properties laws laws2 hc hT P₀ u₀ _ χ₀ hAH₀
  obtain ⟨c, φ, hφ, hcP, ⟨wP, hwP⟩, hlev⟩ := _root_.GlobalTheory.exists_siegPre_of_polAV laws hc o ℂ em P₀.g k b.ζ (Units.map (em : o →* ℂ) b.ζ) P₀
    (fun x => u₀.ex ((k : ℂ)⁻¹ • per τ (m x))) rfl hk rfl
    (IsPrimitiveRoot.coe_units_iff.1 (b.prim ℂ em))
    (fun x y => by rw [map_add (f := _), map_add (f := _), smul_add, u₀.ex_add])
    (fun x => by
      rw [← ex_nsmul, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_inv_cancel₀ hk, one_smul, u₀.ker]
      exact hmem _)
    (fun x y => hWeil k ⟨_, hmem (m x)⟩ ⟨_, hmem (m y)⟩ _ hk0 (by
      have e : Ef ⟨_, hmem (m x)⟩ ⟨_, hmem (m y)⟩ = omegaStd (m x) (m y) := by
        have := hEf ⟨_, hmem (m x)⟩ ⟨_, hmem (m y)⟩
        rw [im_hermForm_per hs hp] at this
        exact_mod_cast this
      rw [e, hm]
      simp))
  have hform : ∀ z z', hermForm Hm z z' =
      ∑ i, ∑ j, ((W + W.transpose) i j : ℂ) * hermForm (imInv τ) (R i z) (R j z') :=
    hermForm_eq_sum Hm (imInv τ) (W + W.transpose) R _ Qspan (by
      rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
      simp only [hQim, hEF, hRQ, im_hermForm_per hs hp, Int.cast_sum, Int.cast_mul])
  have hchi : ∀ l : u.Λ, χ' l = Complex.exp (Real.pi * Complex.I *
      ∑ i, ∑ j, (W i j : ℂ) * ((hermForm (imInv τ) (R i l) (R j l)).im : ℂ)) := fun l => by
    obtain ⟨x, hx⟩ := (hΛ l).1 l.2
    rw [hχ x l hx.symm, hEF, form_act, hw, ← exp_pi_I_int, ← hx]
    simp [hRQ, im_hermForm_per hs hp]
  have hL := GlobalTheory.T.lbIso_linComb_lam_of_appellHumbert_alt laws laws2 hc hT W t.pol u Hm χ' P₀ u₀ _ χ₀ pr R hAH hAH₀ hpru hform hchi
  letI := P₀.isAb.comm
  haveI := hpr
  refine ⟨c, hcP, fun i => pr i ≫ φ.inv, fun i => inferInstanceAs (IsMonHom (pr i ≫ φ.inv)), fun T y => ?_, ?_, fun j i => ?_, fun i v => ?_⟩
  · simp only [← Category.assoc, Iso.comp_inv_eq]
    exact hprod T fun i => y i ≫ φ.hom
  · have hLam : (abelian₂ P₀.A P₀.L).IsLB := DVR.linComb_isLB _ P₀.isLB _ _
    refine LBIso.trans t.isLB (DVR.linComb_isLB _ hLam _ _) (DVR.linComb_isLB _ c.isLB _ _) hL (LBIso.symm ?_)
    have := iso_linComb ((isGen_iff wP).1 hwP) (K := Fin 8 × Fin 8)
      (fun uv => (lift (pr uv.1 ≫ φ.inv) (pr uv.2 ≫ φ.inv)).left) (fun uv => W uv.1 uv.2)
    simp only [← Over.comp_left, comp_lift, lift_fst_assoc, lift_snd_assoc, Category.assoc, Iso.inv_hom_id,
      Category.comp_id] at this
    exact this
  · obtain ⟨F, hF, hFa⟩ := hact j
    haveI := t.hom j
    have hRF : ∀ z, R i (F z) = ∑ v, a j i v • R v z := fun z => by
      have : ((R i ∘ₗ F).restrictScalars ℝ) = (∑ v, a j i v • R v).restrictScalars ℝ :=
        LinearMap.ext_on_range Qspan fun x => by
          rw [LinearMap.restrictScalars_apply, LinearMap.restrictScalars_apply, LinearMap.comp_apply, hF, hRQ,
            LinearMap.sum_apply]
          simp only [LinearMap.smul_apply, hRQ]
          exact (map_sum (per τ) _ _).trans (Finset.sum_congr rfl fun v _ => map_zsmul (per τ) _ _)
      simpa using LinearMap.congr_fun this z
    have e1 : ∀ z, u₀.ex (R i (F z)) = u.ex z ≫ t.act j ≫ pr i := fun z => by
      rw [hpru, hFa, Category.assoc]
    have e2 : ∀ z, u₀.ex (R i (F z)) = u.ex z ≫ ∏ v, pr v ^ a j i v := fun z => by
      rw [hRF, ex_sum, PowMatrixLinear.comp_prod]
      simp only [ex_zsmul, hpru, GrpObj.comp_zpow]
    have e : t.act j ≫ pr i = ∏ v, pr v ^ a j i v :=
      hom_ext_of_lin laws laws2 hc hT t.pol P₀ u u₀ (R i ∘ₗ F) _ _ e1 e2
        (inferInstanceAs (IsMonHom (t.act j ≫ pr i)))
    rw [← Category.assoc, e, PowMatrixLinear.prod_comp]
    simp only [GrpObj.zpow_comp]
    exact (List.prod_ofFn).symm
  · rw [Over.comp_left, hpt, ← Over.comp_left, ← Category.assoc, ← hpru, map_smul, hRQ, ← hlev, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPullbackDegenerationOfValuesIsoDvrStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pullbackDegeneration_of_values_iso_dvr : Laws → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D D' : DegPre V) (F : Type) [Field F] [Algebra (FractionRing V) F] (N N' : NumD F) (ν : NumOf D F N) (ν' : NumOf D' F N') (J : NumD.Iso N N') (Ψ : D.P.A ≅ D'.P.A), IsMonHom Ψ.hom → LBIso D.P.L (D'.P.L.pull Ψ.hom.left) → ∀ (φ : TF (R := V) F ⊗ D.P.A ≅ TF (R := V) F ⊗ D'.P.A) (w : AbPartIso.BunIso φ), φ.hom ≫ fst _ _ = fst _ _ → φ.hom ≫ snd _ _ = snd _ _ ≫ Ψ.hom → w.IsGen → (∀ x, AbPartIso.Carries ν ν' φ x (J.φ x)) → (∀ x, (J.h x : F) * AbPartIso.wVal ν ν' w J.φ 1 = AbPartIso.wVal ν ν' w J.φ x) → ∃ e : IsPullDeg (RingHom.id V) D D', ∀ (k : ℕ) (p : QkPt D F k) (p' : QkPt D' F k) (q : N.QT k) (q' : N'.QT k), ν.QPt p q → ν'.QPt p' q' → q'.1.1.toAdd = J.e q.1.1.toAdd → J.Rel q.1.2 q'.1.2 → GlobalTheory.IndefiniteRowSideFullHecke.ThetaTowerRecognition.Carries e p p' := by
  first | exact @GlobalTheory.ValuesIdent.exists_isPullDeg_of_values | exact GlobalTheory.ValuesIdent.exists_isPullDeg_of_values | (intros; apply GlobalTheory.ValuesIdent.exists_isPullDeg_of_values <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfUnifOfSubsingleton
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZM

noncomputable section

namespace GlobalTheory.NoTorus

theorem pmaps_id {X Y : Scheme.{0}} {L : LB X} {F : X ⟶ X} (hF : F = 𝟙 X) {K : Type} [Fintype K]
    (φ : K → (Y ⟶ X)) (ε : K → ℤ) {t : LB.Gen (LB.LinComb L φ ε)} (ht : t.IsGen) :
    PMaps (isoPullId (Geo.Tor.idIso L) hF) φ φ ε t t (𝟙 Y) := by
  intro Z r z p q hp hq
  subst hF
  have hp' : ∀ k, φ k (r z) ∈ L.U (p k) := hp
  rw [Category.comp_id]
  refine (gen_trans ht r z (Set.mem_iInter.2 hp') (Set.mem_iInter.2 hq)).trans
    (congrArg (· * _) (Finset.prod_congr rfl fun k _ => ?_))
  change _ = (gm (r ≫ φ k) z _ (res _ (L.g (p k) (q k)))) ^ ε k
  have hm : (r ≫ φ k) z ∈ (L.pull (𝟙 X)).U (fun _ => p k) ⊓ L.U (q k) := ⟨mem_pull.2 (hp' k), hq k⟩
  exact congrArg (fun u => u ^ ε k) (gm_res (r ≫ φ k) z _ hm (L.g (p k) (q k))).symm

theorem nonempty_isPullDeg_self {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} (hR : AdmBase R I)
    (D : DegData R I) : Nonempty (IsPullDeg (RingHom.id R) D.toPre D.toPre) := by
  have hgen {F : D.toPre.P.A.left ⟶ D.toPre.P.A.left} (hF : F = 𝟙 _) : PGen (isoPullId (Geo.Tor.idIso D.toPre.P.L) hF) := by
    subst F
    intro Y f y j j' k k' hj hj' hk hk'
    have hgw : ∀ a b, f y ∈ D.toPre.P.L.U a → f y ∈ D.toPre.P.L.U b →
        gw (isoPullId (Geo.Tor.idIso D.toPre.P.L) rfl) f y a b =
          gm f y _ (D.toPre.P.L.g a b) := by
      intro a b ha hb
      have hm : f y ∈ (D.toPre.P.L.pull (𝟙 _)).U (fun _ => a) ⊓ D.toPre.P.L.U b := ⟨mem_pull.2 ha, hb⟩
      exact gm_res f y _ hm _
    rw [hgw j k hj hk, hgw j' k' hj' hk', Category.comp_id]
    have hV : f y ∈ (D.toPre.P.L.U j ⊓ D.toPre.P.L.U k) ⊓ (D.toPre.P.L.U j' ⊓ D.toPre.P.L.U k') := ⟨⟨hj, hk⟩, ⟨hj', hk'⟩⟩
    have hw' : res (inf_le_left : (D.toPre.P.L.U j ⊓ D.toPre.P.L.U k) ⊓ (D.toPre.P.L.U j' ⊓ D.toPre.P.L.U k') ≤ D.toPre.P.L.U j ⊓ D.toPre.P.L.U k) (D.toPre.P.L.g j k) =
      res (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left) :
        (D.toPre.P.L.U j ⊓ D.toPre.P.L.U k) ⊓ (D.toPre.P.L.U j' ⊓ D.toPre.P.L.U k') ≤ D.toPre.P.L.U j ⊓ D.toPre.P.L.U j') (D.toPre.P.L.g j j') *
      (res (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right) :
        (D.toPre.P.L.U j ⊓ D.toPre.P.L.U k) ⊓ (D.toPre.P.L.U j' ⊓ D.toPre.P.L.U k') ≤ D.toPre.P.L.U k ⊓ D.toPre.P.L.U k') (D.toPre.P.L.g k k'))⁻¹ *
      res (inf_le_right : (D.toPre.P.L.U j ⊓ D.toPre.P.L.U k) ⊓ (D.toPre.P.L.U j' ⊓ D.toPre.P.L.U k') ≤ D.toPre.P.L.U j' ⊓ D.toPre.P.L.U k') (D.toPre.P.L.g j' k') :=
      (idIso_isGen D.toPre.P.isLB) (j, k) (j', k')
    have key := congrArg (gm f y ((D.toPre.P.L.U j ⊓ D.toPre.P.L.U k) ⊓ (D.toPre.P.L.U j' ⊓ D.toPre.P.L.U k'))) hw'
    simp only [map_mul, map_inv, gm_res f y _ hV] at key
    exact key
  have : IsMonHom (Iso.refl D.toPre.P.A).hom := inferInstanceAs (IsMonHom (𝟙 D.toPre.P.A))
  have gp : IsGrpPullback D.toPre.P.A D.toPre.P.A (specOf (RingHom.id R)) (Iso.refl D.toPre.P.A).hom.left :=
    (isGrpPullback_of_iso (Iso.refl D.toPre.P.A)).congr (specOf_id R).symm rfl
  obtain ⟨e, me, hF⟩ := grpPullback_iso gp (isGrpPullback_pullback D.toPre.P.A (specOf (RingHom.id R)))
  have hF' : e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R)) = 𝟙 _ := hF
  obtain ⟨W, hW, ⟨ψW⟩⟩ := psiOnExists R I hR D
  obtain ⟨hD, -⟩ := UnifUniq.exists_isPullDeg_id D.toPre D.toPre W hW ψW e me
    (isoPullId (Geo.Tor.idIso D.toPre.P.L) hF') ((isGen_iff _).2 (hgen hF'))
    ((congrArg (_ ≫ ·) hF').trans (Category.comp_id _))
    (pmaps_id hF' (K := PUnit) (fun _ => eSec D.toPre.P.A) (fun _ => 1) D.toPre.rig_gen) (AddEquiv.refl _)
    (fun x => (congrArg (_ ≫ ·) hF').trans (Category.comp_id _))
    (fun x => pmaps_id hF' (K := PUnit) (fun _ => D.toPre.xK x) (fun _ => -1) (D.toPre.psi_gen x))
  exact ⟨hD⟩

end GlobalTheory.NoTorus

namespace GlobalTheory

theorem isAbelianScheme_of_unif_of_subsingleton : Laws → Laws2 → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (IsLocalRing.maximalIdeal V) V → ∀ (D : DegData V (IsLocalRing.maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → Unif (IsLocalRing.maximalIdeal V) D A G → Subsingleton D.toPre.X → IsAbelianScheme G := by
  intro hL hL₂ V _ _ _ _ hc D A G _ hG hsa U hX
  have hR : AdmBase V (IsLocalRing.maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hc⟩
  obtain ⟨A', eA, hA, hw⟩ := GoodReductionUnif.exists_baseChange hL.polBaseChange (jK V) D.toPre.P
  obtain ⟨hD⟩ := NoTorus.nonempty_isPullDeg_self hR D
  have hsemi : IsSemiAbelian D.toPre.P.A := by
    let B := D.toPre.P.A
    have hB := D.toPre.P.isAb
    have := hB.proper
    refine ⟨hB.comm, hB.smooth, inferInstance, inferInstance, hB.geomConnected, ?_⟩
    intro Ω _ _ p
    have hAb : IsAbelianScheme ((Over.pullback p).obj B) := by
      have := hB.comm
      have := hB.smooth
      have := hB.proper
      have := hB.geomConnected
      refine ⟨inferInstance, ?_, ?_, ?_⟩
      · change Smooth (pullback.snd B.hom p); infer_instance
      · change IsProper (pullback.snd B.hom p); infer_instance
      · change GeometricallyConnected (pullback.snd B.hom p); infer_instance
    let A := (Over.pullback p).obj B
    have : IsIso (toUnit (splitTorus (Sp Ω) PUnit)) := by
      have h : 𝟙 (splitTorus (Sp Ω) PUnit) = 1 := by
        rw [← Diag.diagMap_id, ← Diag.diagMap_zero]
        congr 1
      exact ⟨η, h.symm, toUnit_unique _ _⟩
    exact ⟨{
      X := PUnit
      B := A
      isAbelian := hAb
      q := 𝟙 A
      q_hom := inferInstance
      q_flat := by rw [Over.id_left]; infer_instance
      q_surjective := by rw [Over.id_left]; infer_instance
      q_quasiCompact := by rw [Over.id_left]; infer_instance
      i := toUnit _ ≫ η
      i_hom := by have := hAb.comm; infer_instance
      isKernel := IsPullback.of_vert_isIso ⟨Category.comp_id _⟩ }⟩
  obtain ⟨ψ, -⟩ := _root_.GlobalTheory.exists_iso_isPullUnif_of_isPullDeg hL hL₂ V _ hR rfl D D A A' G D.toPre.P.A hsa
    hsemi U
    ⟨SelfUnif.selfPre D A' eA hA hw, fun k _ =>
      SelfUnif.expBij D A' eA hA hw hL.globalFns (IsAdicComplete.le_jacobson_bot _) k⟩ hD
  have e : G.hom = ψ.inv.left ≫ D.toPre.P.A.hom := (Over.w ψ.inv).symm
  have := D.toPre.P.isAb.proper
  have : IsIso ψ.inv.left := inferInstanceAs (IsIso ((Over.forget _).map ψ.inv))
  exact ⟨hG, hsa.smooth, by rw [e]; infer_instance, hsa.geomConnected⟩

end GlobalTheory

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleFormBundlePowerOfPosDefStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relAmple_formBundle_power_of_posDef : Out.GlobalFnsSt → ∀ (h k n : ℕ) (B : Type) [CommRing B] (ζ : B) (S : Scheme.{0}) (s : S ⟶ Sp B) (c : SiegPre h k ζ s) (G : Over S) [GrpObj G] (pr : Fin n → (G ⟶ c.A)) (W : Matrix (Fin n) (Fin n) ℤ), (∀ u, IsMonHom (pr u)) → (∀ (T : Over S) (y : Fin n → (T ⟶ c.A)), ∃! x : T ⟶ G, ∀ u, x ≫ pr u = y u) → Out.RelAmple c.A c.diag → ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → Out.RelAmple G (LB.LinComb c.P (K := Fin n × Fin n) (fun uv => (lift (pr uv.1) (pr uv.2)).left) (fun uv => W uv.1 uv.2)) := by
  first | exact @GlobalTheory.PosDefAmple.relAmple_linComb_of_posDef | exact GlobalTheory.PosDefAmple.relAmple_linComb_of_posDef | (intros; apply GlobalTheory.PosDefAmple.relAmple_linComb_of_posDef <;> assumption)
end

