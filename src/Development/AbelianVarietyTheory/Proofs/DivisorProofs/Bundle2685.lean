module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0095
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TestFieldFiniteOverPadic
public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.UniformityLowerBounds
public import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2660
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.OLinBaseChangeSt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0676
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDivPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2108
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0425
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2215
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2285
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2642
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2603
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2644
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2649
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2632
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2417
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0821
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2659
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0086
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0362
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonCompleteDvrPadicAlgClosureUnitBalls
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.UnifField

open GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds

variable {p : ℕ} [Fact p.Prime]

theorem exists_field (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [Algebra (FractionRing V) (PadicAlgCl p)] (hc : IsAdicComplete (maximalIdeal V) V)
    (hn : ∀ x : FractionRing V, ‖algebraMap _ (PadicAlgCl p) x‖ ≤ 1 ↔
      x ∈ Set.range (algebraMap V (FractionRing V))) :
    ∃ K : IntermediateField ℚ_[p] (PadicAlgCl p), FiniteDimensional ℚ_[p] K ∧
      (K : Set (PadicAlgCl p)) = Set.range (algebraMap (FractionRing V) (PadicAlgCl p)) := by
  haveI := hc
  obtain ⟨K, hK, e⟩ := GlobalTheory.ZH.FieldOfTest.exists_finiteDimensional_of_isComplete p
    (algebraMap (FractionRing V) (PadicAlgCl p)).fieldRange
    (by rw [RingHom.coe_fieldRange]; exact GlobalTheory.ZH.FieldOfTest.isComplete_range_fractionRing V (PadicAlgCl p) hn)
  exact ⟨K, hK, by rw [e, RingHom.coe_fieldRange]⟩

def secK (K : IntermediateField ℚ_[p] (PadicAlgCl p)) : K →+* FractionRing (intRing K) :=
  (IsLocalization.algEquiv (nonZeroDivisors (intRing K)) (FractionRing (intRing K)) K).symm.toRingHom

theorem comp_secK (K : IntermediateField ℚ_[p] (PadicAlgCl p)) :
    (algebraMap (FractionRing (intRing K)) (PadicAlgCl p)).comp (secK K) = algebraMap K (PadicAlgCl p) := by
  have h : algebraMap (FractionRing (intRing K)) (PadicAlgCl p) = (algebraMap K (PadicAlgCl p)).comp
      (IsLocalization.algEquiv (nonZeroDivisors (intRing K)) (FractionRing (intRing K)) K).toRingHom := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors (intRing K)) (RingHom.ext fun w => ?_)
    rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply]
    refine (IsFractionRing.lift_algebraMap (intRing_injective K) w).trans ?_
    have := (IsLocalization.algEquiv (nonZeroDivisors (intRing K)) (FractionRing (intRing K)) K).commutes w
    simp only [AlgEquiv.coe_toRingEquiv, RingEquiv.toRingHom_eq_coe, AlgEquiv.toRingEquiv_toRingHom,
      RingHom.coe_coe, this]
    rfl
  rw [h, RingHom.comp_assoc]
  ext x
  show algebraMap K (PadicAlgCl p) ((IsLocalization.algEquiv (nonZeroDivisors (intRing K)) (FractionRing (intRing K)) K)
    ((IsLocalization.algEquiv (nonZeroDivisors (intRing K)) (FractionRing (intRing K)) K).symm x)) = _
  rw [AlgEquiv.apply_symm_apply]

theorem exists_map (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (V : Type) [CommRing V] [IsDomain V]
    [IsLocalRing V] [Algebra (FractionRing V) (PadicAlgCl p)]
    (hn : ∀ x : FractionRing V, ‖algebraMap _ (PadicAlgCl p) x‖ ≤ 1 ↔
      x ∈ Set.range (algebraMap V (FractionRing V)))
    (hK : Set.range (algebraMap (FractionRing V) (PadicAlgCl p)) ⊆ K) :
    ∃ (φ : V →+* intRing K) (φK : FractionRing V →+* FractionRing (intRing K)),
      φK.comp (algebraMap V _) = (algebraMap (intRing K) _).comp φ ∧
      (maximalIdeal V).map φ ≤ maximalIdeal (intRing K) ∧
      (algebraMap (FractionRing (intRing K)) (PadicAlgCl p)).comp φK =
        algebraMap (FractionRing V) (PadicAlgCl p) := by
  let jF := algebraMap (FractionRing V) (PadicAlgCl p)
  let ρK : FractionRing V →+* K := jF.codRestrict K (fun x => hK ⟨x, rfl⟩)
  have hle : ∀ v : V, ‖jF (algebraMap V _ v)‖ ≤ 1 := fun v => (hn _).2 ⟨v, rfl⟩
  let φ : V →+* intRing K := (ρK.comp (algebraMap V (FractionRing V))).codRestrict (intRing K) (fun v => by
    rw [ValuationSubring.mem_comap, mem_OO_iff]
    exact hle v)
  have h3 : (algebraMap (FractionRing (intRing K)) (PadicAlgCl p)).comp ((secK K).comp ρK) = jF := by
    rw [← RingHom.comp_assoc, comp_secK]
    rfl
  refine ⟨φ, (secK K).comp ρK, ?_, ?_, h3⟩
  · refine RingHom.ext fun v => (algebraMap (FractionRing (intRing K)) (PadicAlgCl p)).injective ?_
    have e1 := RingHom.congr_fun h3 (algebraMap V _ v)
    simp only [RingHom.comp_apply] at e1 ⊢
    rw [e1]
    exact ((IsFractionRing.lift_algebraMap (intRing_injective K) (φ v)).trans rfl).symm
  · refine Ideal.map_le_iff_le_comap.2 fun m hm => ?_
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    refine (IsLocalRing.mem_maximalIdeal _).1 hm ?_
    obtain ⟨y, hy⟩ := hu.exists_right_inv
    have h1 : jF (algebraMap V _ m) * ((y : K) : PadicAlgCl p) = 1 := by
      have := congrArg (fun w : intRing K => ((w : K) : PadicAlgCl p)) hy
      simpa [φ, ρK] using this
    have h2 : ((y : K) : PadicAlgCl p) = jF (algebraMap V _ m)⁻¹ := by
      rw [map_inv₀]; exact eq_inv_of_mul_eq_one_right h1
    have hy1 : ‖((y : K) : PadicAlgCl p)‖ ≤ 1 := by
      have := y.2
      rw [ValuationSubring.mem_comap, mem_OO_iff] at this
      exact this
    obtain ⟨z, hz⟩ := (hn (algebraMap V _ m)⁻¹).1 (h2 ▸ hy1)
    have h0 : algebraMap V (FractionRing V) m ≠ 0 := fun h => by simp [h] at h1
    refine IsUnit.of_mul_eq_one z (IsFractionRing.injective V (FractionRing V) ?_)
    rw [map_mul, hz, map_one, mul_inv_cancel₀ h0]

end GlobalTheory.UnifField
end

noncomputable section
namespace GlobalTheory.UnifField
open GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds

theorem exists_common_ring : ∀ (p : ℕ) [Fact p.Prime] (V V' : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CommRing V'] [IsDomain V'] [IsDiscreteValuationRing V'] [Algebra (FractionRing V) (PadicAlgCl p)] [Algebra (FractionRing V') (PadicAlgCl p)], IsAdicComplete (maximalIdeal V) V → IsAdicComplete (maximalIdeal V') V' → (∀ x : FractionRing V, ‖algebraMap _ (PadicAlgCl p) x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap V (FractionRing V))) → (∀ x : FractionRing V', ‖algebraMap _ (PadicAlgCl p) x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap V' (FractionRing V'))) → ∀ s : Finset (PadicAlgCl p), ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W) (_ : Algebra (FractionRing W) (PadicAlgCl p)), IsAdicComplete (maximalIdeal W) W ∧ (∀ x : FractionRing W, ‖algebraMap _ (PadicAlgCl p) x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap W (FractionRing W))) ∧ (↑s ⊆ Set.range (algebraMap (FractionRing W) (PadicAlgCl p))) ∧ (∀ z : PadicAlgCl p, ∃ f : Polynomial (FractionRing W), f ≠ 0 ∧ Polynomial.eval₂ (algebraMap (FractionRing W) (PadicAlgCl p)) z f = 0) ∧ (∃ (φ : V →+* W) (φK : FractionRing V →+* FractionRing W), φK.comp (algebraMap V _) = (algebraMap W _).comp φ ∧ (maximalIdeal V).map φ ≤ maximalIdeal W ∧ (algebraMap (FractionRing W) (PadicAlgCl p)).comp φK = algebraMap (FractionRing V) (PadicAlgCl p)) ∧ (∃ (φ : V' →+* W) (φK : FractionRing V' →+* FractionRing W), φK.comp (algebraMap V' _) = (algebraMap W _).comp φ ∧ (maximalIdeal V').map φ ≤ maximalIdeal W ∧ (algebraMap (FractionRing W) (PadicAlgCl p)).comp φK = algebraMap (FractionRing V') (PadicAlgCl p)) := by
  intro p _ V V' _ _ _ _ _ _ _ _ hc hc' hn hn' s
  obtain ⟨K₁, h₁, e₁⟩ := exists_field V hc hn
  obtain ⟨K₂, h₂, e₂⟩ := exists_field V' hc' hn'
  let K₃ := IntermediateField.adjoin ℚ_[p] (s : Set (PadicAlgCl p))
  have h₃ : FiniteDimensional ℚ_[p] K₃ :=
    IntermediateField.finiteDimensional_adjoin (fun x _ => Algebra.IsIntegral.isIntegral x)
  let K := K₁ ⊔ K₂ ⊔ K₃
  have hK : FiniteDimensional ℚ_[p] K := inferInstance
  obtain ⟨hdvr, hcW, hnW⟩ := _root_.GlobalTheory.intRing_complete_dvr p K hK
  have l₁ : K₁ ≤ K := le_sup_left.trans le_sup_left
  have l₂ : K₂ ≤ K := le_sup_right.trans le_sup_left
  have l₃ : K₃ ≤ K := le_sup_right
  refine ⟨intRing K, inferInstance, inferInstance, hdvr, fracAlgebra K, hcW, hnW, ?_, ?_,
    exists_map K V (fun x => hn x) (fun x hx => l₁ (show x ∈ (K₁ : Set (PadicAlgCl p)) by rw [e₁]; exact hx)),
    exists_map K V' (fun x => hn' x) (fun x hx => l₂ (show x ∈ (K₂ : Set (PadicAlgCl p)) by rw [e₂]; exact hx))⟩
  · intro x hx
    have hxK : x ∈ K := l₃ (IntermediateField.subset_adjoin ℚ_[p] _ hx)
    exact ⟨secK K ⟨x, hxK⟩, (RingHom.congr_fun (comp_secK K) ⟨x, hxK⟩).trans rfl⟩
  · intro z
    have hz : IsIntegral ℚ_[p] z := Algebra.IsIntegral.isIntegral z
    refine ⟨(minpoly ℚ_[p] z).map ((secK K).comp (algebraMap ℚ_[p] K)),
      Polynomial.map_ne_zero (minpoly.ne_zero hz), ?_⟩
    rw [Polynomial.eval₂_map, ← RingHom.comp_assoc, comp_secK, ← IsScalarTower.algebraMap_eq,
      ← Polynomial.aeval_def]
    exact minpoly.aeval ℚ_[p] z

end GlobalTheory.UnifField
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompatibleInverseSystemLatticeMaps
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct
open scoped TensorProduct

namespace GlobalTheory.InvSys

theorem exists_nsmul_of_basis {M κ : Type} [AddCommGroup M] (b : Module.Basis κ ℤ M) (f : M →ₗ[ℤ] M) (n : ℕ)
    (hb : ∀ i, ∃ z, f (b i) = n • z) (x : M) : ∃ z, f x = n • z := by
  have hx : x ∈ Submodule.span ℤ (Set.range b) := by rw [b.span_eq]; exact Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy => obtain ⟨i, rfl⟩ := hy; exact hb i
  | zero => exact ⟨0, by simp⟩
  | add y w _ _ hy hw =>
    obtain ⟨z1, h1⟩ := hy; obtain ⟨z2, h2⟩ := hw
    exact ⟨z1 + z2, by rw [map_add (f := _), h1, h2, smul_add]⟩
  | smul a y _ hy =>
    obtain ⟨z, h⟩ := hy
    exact ⟨a • z, by rw [map_smul, h, smul_comm]⟩

theorem invSys : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (g : ℕ → D.La →+ D.La), (∀ n m : ℕ, 0 < n → 0 < m → (n * m).Coprime p → ∀ x, ∃ z, g (n * m) x = g n x + n • z) → (∀ n, 0 < n → n.Coprime p → ∀ x, ∃ y z, g n y = x + n • z) → (∀ n, 0 < n → n.Coprime p → ∀ x z, g n x = n • z → ∃ w, x = n • w) → ∃ g' : ℕ → D.La →+ D.La, (∀ n m : ℕ, 0 < n → 0 < m → (n * m).Coprime p → ∀ x, ∃ z, g' (n * m) x = g' n x + n • z) ∧ (∀ n, 0 < n → n.Coprime p → ∀ x, ∃ z, g n (g' n x) = x + n • z) ∧ (∀ n, 0 < n → n.Coprime p → ∀ x, ∃ z, g' n (g n x) = x + n • z) := by
  intro p _ D g htow hsurj hinj
  haveI := D.freeLa
  let b := Module.Free.chooseBasis ℤ D.La
  choose y z hyz using hsurj
  let g' : ℕ → D.La →+ D.La := fun n =>
    if h : 0 < n ∧ n.Coprime p then (b.constr ℤ (fun i => y n h.1 h.2 (b i))).toAddMonoidHom else 0
  have sec : ∀ n, 0 < n → n.Coprime p → ∀ x, ∃ z, g n (g' n x) = x + n • z := by
    intro n hn hc x
    have hg' : g' n = (b.constr ℤ (fun i => y n hn hc (b i))).toAddMonoidHom := by
      simp only [g', dif_pos (And.intro hn hc)]
    obtain ⟨w, hw⟩ := exists_nsmul_of_basis b
      ((g n).toIntLinearMap ∘ₗ b.constr ℤ (fun i => y n hn hc (b i)) - LinearMap.id) n
      (fun i => ⟨z n hn hc (b i), by simp [Module.Basis.constr_basis, hyz]⟩) x
    refine ⟨w, ?_⟩
    rw [hg']
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, AddMonoidHom.coe_toIntLinearMap, LinearMap.id_apply] at hw
    simp only [LinearMap.toAddMonoidHom_coe]
    rw [← hw]; abel
  refine ⟨g', ?_, sec, ?_⟩
  · intro n m hn hm hc x
    have hcn : n.Coprime p := Nat.Coprime.coprime_dvd_left (Dvd.intro m rfl) hc
    obtain ⟨z1, h1⟩ := htow n m hn hm hc (g' (n * m) x)
    obtain ⟨z2, h2⟩ := sec (n * m) (Nat.mul_pos hn hm) hc x
    obtain ⟨z3, h3⟩ := sec n hn hcn x
    obtain ⟨w, hw⟩ := hinj n hn hcn (g' (n * m) x - g' n x) (m • z2 - z1 - z3) (by
      rw [map_sub, smul_sub, smul_sub]
      rw [h2] at h1
      have : g n (g' (n * m) x) = x + (n * m) • z2 - n • z1 := by rw [h1]; abel
      rw [this, h3]
      rw [mul_smul]; abel)
    exact ⟨w, by rw [← hw]; abel⟩
  · intro n hn hc x
    obtain ⟨z1, h1⟩ := sec n hn hc (g n x)
    obtain ⟨w, hw⟩ := hinj n hn hc (g' n (g n x) - x) z1 (by rw [map_sub, h1]; abel)
    exact ⟨w, by rw [← hw]; abel⟩

end GlobalTheory.InvSys
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoproductThickeningAffineLiftPoincare
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.PDForm.CopPoincare

theorem isNilpotent_of_isNilDP {B : Type} [CommRing B] {J : Ideal B} {δ : DividedPowers J} (h : IsNilDP δ) :
    IsNilpotent J := by
  obtain ⟨N, hN⟩ := (isDPNilpotent_iff_exists_isLevel δ).1 h
  have key : ∀ (m : ℕ), ∀ x ∈ J ^ m, ∀ l : List (ℕ × B), (∀ p ∈ l, p.2 ∈ J) → N ≤ m + (l.map Prod.fst).sum →
      x * (l.map fun p ↦ δ.dpow p.1 p.2).prod = 0 := by
    intro m
    induction m with
    | zero =>
      intro x _ l hl hs
      rw [(isLev_iff_prod δ N).1 hN l hl (by simpa using hs), mul_zero]
    | succ m ih =>
      intro x hx l hl hs
      rw [pow_succ] at hx
      refine Submodule.mul_induction_on hx (fun a ha b hb ↦ ?_) (fun a b ha hb ↦ by rw [add_mul, ha, hb, add_zero])
      have := ih a ha ((1, b) :: l) (by
        intro p hp
        rcases List.mem_cons.1 hp with rfl | hp
        · exact hb
        · exact hl p hp) (by simp only [List.map_cons, List.sum_cons]; omega)
      simpa [δ.dpow_one hb, mul_assoc] using this
  refine ⟨N, ?_⟩
  rw [Ideal.zero_eq_bot, eq_bot_iff]
  intro x hx
  simpa using key N x hx [] (by simp) (by simp)

theorem exists_cop_qAt : ∀ (D : Data) (Λ : Lift D) (n : ℕ) (U : AffOp D.X) (T : Thick D.κ D.t), IsLev T.δ (n + 1) → ⊤ ≤ (T.x ≫ D.i) ⁻¹ᵁ U.unop.1 → ∃ (G : Thick D.κ D.t) (l : T ⟶ G) (r : Λ.L.obj U ⟶ G), IsCop (n + 1) l r ∧ (KK D.κ D.t).QAt l := by
  intro D Λ n U T hT hU
  obtain ⟨F, G, u, q, r, hu, hF, hq, hJ, hc⟩ := _root_.GlobalTheory.CopEx.exists_cop D Λ n U T hT hU
  obtain ⟨h1, -, -, -⟩ := _root_.GlobalTheory.PDForm.Lift.hom_spec D Λ
  refine ⟨G, u ≫ q, r, hc, ?_⟩
  haveI := D.sec_smooth U.unop
  have hker : RingHom.ker (q.φ : F.B →+* G.B) ≤ F.J := fun b hb ↦ hJ b (by
    rw [show q.φ b = 0 from hb]; exact G.J.zero_mem)
  have hnil : IsNilpotent (RingHom.ker (q.φ : F.B →+* G.B)) := by
    obtain ⟨N, hN⟩ := isNilpotent_of_isNilDP F.nil
    refine ⟨N, ?_⟩
    rw [Ideal.zero_eq_bot, eq_bot_iff, ← Ideal.zero_eq_bot, ← hN]
    exact Ideal.pow_right_mono hker N
  let y : Sec D.s U.unop.1 →ₐ[D.R] G.B := r.φ.comp (Λ.e U : Sec D.s U.unop.1 →ₐ[D.R] (Λ.L.obj U).B)
  let y' : Sec D.s U.unop.1 →ₐ[D.R] F.B := Algebra.FormallySmooth.liftOfSurjective y q.φ hq hnil
  have hy' : ∀ a, q.φ (y' a) = y a := fun a ↦ Algebra.FormallySmooth.liftOfSurjective_apply y q.φ hq hnil a
  have hbij : Function.Bijective q.φ₀ := by
    refine ⟨(injective_iff_map_eq_zero _).2 fun b hb ↦ ?_, fun c ↦ ?_⟩
    · obtain ⟨b, rfl⟩ := F.surj b
      rw [q.comm, G.ker] at hb
      exact (F.ker b).2 (hJ b hb)
    · obtain ⟨c, rfl⟩ := G.surj c
      obtain ⟨b, rfl⟩ := hq c
      exact ⟨F.π b, q.comm b⟩
  haveI : IsIso (spMap q.φ₀) :=
    (inferInstance : IsIso (Spec.map (RingEquiv.ofBijective q.φ₀ hbij).toCommRingCatIso.hom))
  have hy := (h1 U G y).2 ⟨r, fun _ ↦ rfl⟩
  have hpt : spMap (F.π.comp (y' : Sec D.s U.unop.1 →+* F.B)) ≫ affPt D.s U.unop = F.x ≫ D.i := by
    rw [← cancel_epi (spMap q.φ₀), ← Category.assoc, ← Cris.spMap_comp, ← Category.assoc, q.pt, ← hy]
    congr 2
    ext a
    exact (q.comm _).trans (congrArg G.π (hy' a))
  obtain ⟨b', hb'⟩ := (h1 U F y').1 hpt
  obtain ⟨s, ⟨hs1, hs2⟩, -⟩ := hc.2 F hF u b'
  have hbq : b' ≫ q = r := by
    have hφ : (b' ≫ q).φ = r.φ := AlgHom.ext fun b ↦ by
      obtain ⟨a, rfl⟩ := (Λ.e U).surjective b
      change q.φ (b'.φ ((Λ.e U) a)) = r.φ ((Λ.e U) a)
      rw [hb', hy']; rfl
    have extHom : ∀ {f g : Thick.Hom (Λ.L.obj U) G}, f.φ = g.φ → f = g := by
      intro f g h
      rcases f with ⟨φ, φ₀, comm, dp, pt⟩
      rcases g with ⟨ψ, ψ₀, comm', dp', pt'⟩
      obtain rfl : φ = ψ := h
      obtain rfl : φ₀ = ψ₀ := RingHom.ext fun c ↦ by
        obtain ⟨b, rfl⟩ := (Λ.L.obj U).surj c
        rw [comm, comm']
      rfl
    exact extHom hφ
  have hsq : s ≫ q = 𝟙 G := by
    obtain ⟨c, -, huniq⟩ := hc.2 G hc.1 (u ≫ q) r
    refine (huniq _ ⟨?_, ?_⟩).trans (huniq _ ⟨Category.comp_id _, Category.comp_id _⟩).symm
    · rw [← Category.assoc, hs1]
    · rw [← Category.assoc, hs2, hbq]
  exact (GlobalTheory.CxCoh.QAtFormal.qAt_formal _ (KK D.κ D.t)).2.2 T G F (u ≫ q) s q hsq (by rw [hs1]; exact hu)

end GlobalTheory.PDForm.CopPoincare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorisationThroughAbelianSubvariety
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem exists_factor_abelianSubvariety : ∀ (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B),
    ∃ (C : AbVar K) (p : A ⟶ C) (i : C ⟶ B), Surjective p.hom.left ∧ IsClosedImmersion i.hom.left ∧ p ≫ i = f := by
  intro K _ A B f
  obtain ⟨Z, p, i, hpi, hp, hi, hg⟩ := GlobalTheory.T.exists_geometricallyIntegral_image_of_hom K A B f
  obtain ⟨hG, hpm, him⟩ := GlobalTheory.T.exists_subgroupScheme_of_geometricallyIntegral_image K A B f Z p i hpi hp hi hg
  letI := hG
  have hmono : Mono i := by
    have : Mono i.left := inferInstance
    exact Over.mono_of_mono_left i
  have hcomm : IsCommMonObj Z := ⟨by
    apply (cancel_mono i).1
    rw [Category.assoc, IsMonHom.mul_hom, ← BraidedCategory.braiding_naturality_assoc,
      IsCommMonObj.mul_comm]⟩
  have hw : i.left ≫ B.X.hom = Z.hom := Over.w i
  have hB := B.ab
  have : Smooth B.X.hom := hB.smooth
  have : IsProper B.X.hom := hB.proper
  have hlft : LocallyOfFiniteType Z.hom := by rw [← hw]; infer_instance
  have hpr : IsProper Z.hom := by rw [← hw]; infer_instance
  have hsm : Smooth Z.hom := GlobalTheory.grpObj_smooth_of_geometricallyReduced K Z hlft inferInstance
  have hgc : GeometricallyConnected Z.hom := ⟨fun L _ y W fst snd h => by
    have : IsIntegral W := hg.geometrically_isIntegral y fst snd h
    infer_instance⟩
  have hab : IsAbelianScheme Z := ⟨hcomm, hsm, hpr, hgc⟩
  obtain ⟨g, hd⟩ := GlobalTheory.T.abelianScheme_field_smoothOfRelativeDimension_exists K Z hab
  let C : AbVar K := { X := Z, ab := hab, dim := g, smooth := hd }
  refine ⟨C, Hom.mk (B := C) p, Hom.mk (A := C) i, hp, hi, ?_⟩
  exact Subtype.ext hpi

end GlobalTheory.AV.AbVar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteMarkedLatticePeriodRepresentatives
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix

namespace GlobalTheory.PELU

variable {O : Type} [Ring O] {bar : O → O}

theorem isPeriod_comp_symm {g : ℕ} {ρ : O →+* Matrix (Fin g) (Fin g) ℂ} {D D' : PLat O bar}
    {P : D.La →+ (Fin g → ℂ)} (hP : IsPeriod D ρ P) (w : D.La ≃ₗ[O] D'.La) (hw : IsIsom D D' w) :
    IsPeriod D' ρ (P.comp w.symm.toAddEquiv.toAddMonoidHom) := by
  obtain ⟨h1, h2, h3, h4, Hm, hH, hpos, hEF⟩ := hP
  have hr : (P.comp w.symm.toAddEquiv.toAddMonoidHom).range = P.range := by
    ext z
    simp only [AddMonoidHom.mem_range, AddMonoidHom.coe_comp, Function.comp_apply]
    constructor
    · rintro ⟨x, rfl⟩; exact ⟨_, rfl⟩
    · rintro ⟨x, rfl⟩; exact ⟨w x, by simp⟩
  refine ⟨fun a x => ?_, ?_, ?_, ?_, Hm, hH, hpos, fun x y => ?_⟩
  · simp [h1]
  · exact h2.comp w.symm.injective
  · rw [hr]; exact h3
  · have : Set.range (P.comp w.symm.toAddEquiv.toAddMonoidHom) = Set.range P := by
      rw [← AddMonoidHom.coe_range, hr, AddMonoidHom.coe_range]
    rw [this]; exact h4
  · simp only [AddMonoidHom.coe_comp, Function.comp_apply]
    rw [hEF, ← hw]
    simp

def unifClass {Λ : Type} {g : ℕ} (F : Fam ℂ O Λ g) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (N : ℕ)
    (C : ∀ D' : PLat O bar, (Λ → D'.La) → Prop) (y : Sp ℂ ⟶ F.X) : Set ((D' : PLat O bar) × (Λ → D'.La)) :=
  {p | C p.1 p.2 ∧ ∃ P e, UnifAt F (RingHom.id ℂ) ρ N p.1 p.2 P y e}

theorem unifClass_eq {Λ : Type} {g : ℕ} (F : Fam ℂ O Λ g) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) {N : ℕ}
    (C : ∀ D' : PLat O bar, (Λ → D'.La) → Prop) (hN : 0 < N) {y : Sp ℂ ⟶ F.X} {D₀ : PLat O bar}
    {t₀ : Λ → D₀.La} {P₀ : D₀.La →+ (Fin g → ℂ)} {e₀ : (Fin g → ℂ) → (Over.mk y ⟶ F.A)}
    (hU : UnifAt F (RingHom.id ℂ) ρ N D₀ t₀ P₀ y e₀) :
    unifClass F ρ N C y = {p | C p.1 p.2 ∧ ∃ w, IsMarkedIsom N D₀ p.1 t₀ p.2 w} := by
  ext ⟨D', t'⟩
  constructor
  · rintro ⟨hC, P, e, hU'⟩
    obtain ⟨w, -, hw, -⟩ := _root_.GlobalTheory.PELU.unifAt_cmp O bar g ρ ℂ (RingHom.id ℂ) Λ F N D₀ D' t₀ t' P₀ P y e₀ e hN hU hU'
    exact ⟨hC, w, hw⟩
  · rintro ⟨hC, w, hw⟩
    exact ⟨hC, P₀.comp w.symm.toAddEquiv.toAddMonoidHom, _,
      _root_.GlobalTheory.PELU.unifAt_transport O bar g ρ ℂ (RingHom.id ℂ) Λ F N D₀ D' t₀ t' P₀ (P₀.comp w.symm.toAddEquiv.toAddMonoidHom) y e₀ w
        (LinearEquiv.refl ℂ _) hN hU hw (fun x => by simp) (isPeriod_comp_symm hU.2.1 w hw.1)⟩

theorem exists_finite_representatives : ∀ (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (Λ : Type) (F : Fam ℂ O Λ g) (N : ℕ) (C : ∀ D' : PLat O bar, (Λ → D'.La) → Prop) (d : ℕ), 0 < N → (∀ a, F.eta a ^ N = 1) → SmoothOfRelativeDimension d F.s → QuasiCompact F.s → FineAt F (RingHom.id ℂ) ρ N C → ∃ (n : ℕ) (Di : Fin n → PLat O bar) (t : ∀ i, Λ → (Di i).La), (∀ i, C (Di i) (t i) ∧ ∃ P, IsPeriod (Di i) ρ P) ∧ (∀ D' t', C D' t' → (∃ P, IsPeriod D' ρ P) → ∃ i w, IsMarkedIsom N D' (Di i) t' (t i) w) ∧ ∀ i j w, IsMarkedIsom N (Di i) (Di j) (t i) (t j) w → i = j := by
  intro O _ bar g ρ Λ F N C d hN heta hsm hqc hF
  have : Smooth F.s := SmoothOfRelativeDimension.smooth d F.s
  have hlft : LocallyOfFiniteType F.s := inferInstance

  have hloc : ∀ (B : Set (Fin d → ℂ)) (y : (Fin d → ℂ) → (Sp ℂ ⟶ F.X)), IsOpen B →
      (∀ b ∈ B, y b ≫ F.s = spMap (RingHom.id ℂ)) → IsHolTo B y → ∀ b₀ ∈ B,
      ∀ᶠ b in nhds b₀, unifClass F ρ N C (y b) = unifClass F ρ N C (y b₀) := by
    intro B y hB hy hhol b₀ hb₀
    obtain ⟨D₀, t₀, P₀, e₀, -, hU₀⟩ := hF.pts (y b₀) (hy b₀ hb₀)
    obtain ⟨B', P, e, hB', hb₀', -, -, -, -, hU⟩ :=
      _root_.GlobalTheory.PELU.holomorphic_map_lifts_to_periods O bar g ρ Λ F N D₀ t₀ d B y b₀ P₀ e₀ hN heta hlft hB hb₀ hy hhol hU₀
    filter_upwards [hB'.mem_nhds hb₀'] with b hb
    rw [unifClass_eq F ρ C hN (hU b hb), unifClass_eq F ρ C hN hU₀]
  have hfin := GlobalTheory.FiniteClasses.finite_image_of_locally_constant_on_holomorphic_families
    GlobalTheory.SubfieldChart.exists_holomorphic_chart ℂ (RingHom.id ℂ) F.X F.s d _ (unifClass F ρ N C) hsm hqc hloc
  set T := unifClass F ρ N C '' {x | x ≫ F.s = spMap (RingHom.id ℂ)} with hT
  haveI := hfin.fintype
  let E := (Fintype.equivFin T).symm
  have hch : ∀ c : T, ∃ (p : (D' : PLat O bar) × (Λ → D'.La)) (y : Sp ℂ ⟶ F.X), unifClass F ρ N C y = c.1 ∧ p ∈ unifClass F ρ N C y := by
    rintro ⟨c, y, hy, rfl⟩
    obtain ⟨D', t', P, e, hC, hU⟩ := hF.pts y hy
    exact ⟨⟨D', t'⟩, y, rfl, hC, P, e, hU⟩
  choose p y hcls hmem using hch
  refine ⟨Fintype.card T, fun i => (p (E i)).1, fun i => (p (E i)).2, fun i => ?_, ?_, ?_⟩
  · obtain ⟨hC, P, e, hU⟩ := hmem (E i)
    exact ⟨hC, P, hU.2.1⟩
  · rintro D' t' hC ⟨P, hP⟩
    obtain ⟨y', e', hU'⟩ := hF.occ D' t' P hC hP
    let c : T := ⟨unifClass F ρ N C y', y', hU'.1, rfl⟩
    refine ⟨E.symm c, ?_⟩
    have h1 : p (E (E.symm c)) ∈ unifClass F ρ N C y' := by
      have := hmem (E (E.symm c))
      have h2 : ((E (E.symm c)) : Set ((D' : PLat O bar) × (Λ → D'.La))) = unifClass F ρ N C y' :=
        congrArg Subtype.val (E.apply_symm_apply c)
      rwa [hcls, h2] at this
    rw [unifClass_eq F ρ C hN hU'] at h1
    exact h1.2
  · intro i j w hw
    apply E.injective
    apply Subtype.ext
    obtain ⟨hCi, Pi, ei, hUi⟩ := hmem (E i)
    obtain ⟨hCj, Pj, ej, hUj⟩ := hmem (E j)
    have hj' : p (E j) ∈ unifClass F ρ N C (y (E i)) := by
      rw [unifClass_eq F ρ C hN hUi]
      exact ⟨hCj, w, hw⟩
    obtain ⟨-, Pj', ej', hUj'⟩ := hj'
    rw [← hcls, ← hcls, unifClass_eq F ρ C hN hUj', unifClass_eq F ρ C hN hUj]

end GlobalTheory.PELU
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHodgeFiltrationToPDivOmegaLinearMapStatement
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.exists_hodgeFiltration_to_pDivOmega_linearMap
    (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (N : ℕ) (hN : (p : R) ^ N = 0)
    (A : Over (Sp R)) [GrpObj A] (hA : IsAbelianScheme A) (G : PDivGroup p R)
    (t : G.TorsionTower A) :
    ∃ ψ : PrimitiveSubmodule A →ₗ[R] G.omega,
      ∀ c : PrimitiveSubmodule A, GlobalTheory.PtExt.IsCan t c.1 (G.rigOfOmega (ψ c)) :=
  GlobalTheory.PtExt.exists_hodge_to_omega p R N hN A hA G t
end

