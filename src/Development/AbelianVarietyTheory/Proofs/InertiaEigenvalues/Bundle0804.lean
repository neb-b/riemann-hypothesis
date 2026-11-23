module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0666
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0787
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0684
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0192
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0451
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0164
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilRepresentationVacuumCosetVectorsGrid
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1288
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0093
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIsScalar
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0031
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0102
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeightZeroSectionValueOnMarkedPeriodSpace
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1656
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0109

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaShapeRelationDropSplitPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.DownLift.SplitCoef

noncomputable section
namespace GlobalTheory.DownLift.SplitRel
open GlobalTheory.SplitScalar
variable {D : D7}

theorem psi_ne_zero (ψ : AddChar (AF D.host.F) ℂ) (z : AF D.host.F) : ψ z ≠ 0 := by
  intro h
  have h1 := AddChar.map_zero_eq_one ψ
  rw [← add_neg_cancel z, AddChar.map_add_eq_mul, h, zero_mul] at h1
  exact zero_ne_one h1

theorem idem_E {a E : AE D} (ha : IsSplitIdem D a) (hE : a + cA D a = E) : E * E = E := by
  obtain ⟨h1, h2, -⟩ := ha
  have h3 : cA D a * cA D a = cA D a := by rw [← map_mul, h1]
  have h4 : cA D a * a = 0 := by rw [mul_comm, h2]
  rw [← hE]; linear_combination h1 + h3 + h2 + h4

theorem one_sub_mul_self {a E : AE D} (ha : IsSplitIdem D a) (hE : a + cA D a = E) : (1 - E) * a = 0 := by
  obtain ⟨h1, h2, -⟩ := ha
  rw [← hE]; linear_combination (-1 : AE D) * h1 - h2

theorem one_sub_mul_conj {a E : AE D} (ha : IsSplitIdem D a) (hE : a + cA D a = E) : (1 - E) * cA D a = 0 := by
  obtain ⟨h1, h2, -⟩ := ha
  have h3 : cA D a * cA D a = cA D a := by rw [← map_mul, h1]
  rw [← hE]; linear_combination (-1 : AE D) * h3 - h2

theorem cA_E {a E : AE D} (hE : a + cA D a = E) : cA D E = E := by
  rw [← hE, map_add (f := _), GlobalTheory.DualPairCheck.cA_cA, add_comm]

theorem smul_half_zero {m n : ℕ} {a E : AE D} (h : (1 - E) * a = 0) {y : Mx D m n} (hy : IsHalf a y) :
    (1 - E) • y = 0 := by
  ext i j
  show (1 - E) * y i j = 0
  rw [← hy i j, ← mul_assoc, h, zero_mul]

theorem half_conj {m n : ℕ} {a : AE D} (ha : IsSplitIdem D a) (u : Mx D m n) : IsHalf (cA D a) (cA D a • u) := by
  intro i j
  show cA D a * (cA D a * u i j) = cA D a * u i j
  rw [← mul_assoc, ← map_mul, ha.1]

theorem half_add {m n : ℕ} {a : AE D} (ha : IsSplitIdem D a) {x : Mx D m n} (hx : IsHalf a x) (u : Mx D m n) :
    IsHalf a (x + a • u) := by
  intro i j
  show a * (x i j + a * u i j) = x i j + a * u i j
  rw [mul_add, hx i j, ← mul_assoc, ha.1]

theorem heisO_off_comm (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} {E : AE D} (hcE : cA D E = E) (u y : WO S T)
    (hy : (1 - E) • y = 0) (f : WO S T → ℂ) :
    heisO ψ S T ((1 - E) • u) (heisO ψ S T y f) = heisO ψ S T y (heisO ψ S T ((1 - E) • u) f) := by
  rw [heisO_comm, symplO_smul, map_sub, map_one, hcE, hy, symplO_zero_right, AddChar.map_zero_eq_one, one_smul]

theorem invForm_comp {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D} {a E : AE D}
    (ha : IsSplitIdem D a) (hE : a + cA D a = E) {ℓ : (WO S T → ℂ) →ₗ[ℂ] ℂ} (hℓ : InvForm ψ S T a ℓ) (u : WO S T) :
    InvForm ψ S T a (ℓ ∘ₗ heisL ψ S T ((1 - E) • u)) := by
  intro w hw f hf
  simp only [LinearMap.comp_apply, heisL_apply]
  rw [heisO_off_comm ψ (cA_E hE) u w (smul_half_zero (one_sub_mul_conj ha hE) hw)]
  exact hℓ w hw _ (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf _)

theorem shape_ratio {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {a : AE D} {Φ g : WO S T → ℂ}
    (hs : HasShape ψ S T a Φ g) {x₀ : WO S T} (hx₀ : IsHalf a x₀) (h0 : Φ x₀ ≠ 0) {ℓ : (WO S T → ℂ) →ₗ[ℂ] ℂ}
    (hℓ : InvForm ψ S T a ℓ) {y : WO S T} (hy : IsHalf a y) :
    ℓ (heisO ψ S T y g) = Φ y * (Φ x₀)⁻¹ * ℓ (heisO ψ S T x₀ g) := by
  obtain ⟨c, hc⟩ := hs ℓ hℓ
  rw [hc y hy, hc x₀ hx₀]
  have : (Φ x₀)⁻¹ * Φ x₀ = 1 := inv_mul_cancel₀ h0
  linear_combination (-(c * Φ y)) * this

theorem shape_off {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D} {a E : AE D}
    (ha : IsSplitIdem D a) (hE : a + cA D a = E) {Φ g : WO S T → ℂ} (hs : HasShape ψ S T a Φ g) {x₀ : WO S T}
    (hx₀ : IsHalf a x₀) (h0 : Φ x₀ ≠ 0) {ℓ : (WO S T → ℂ) →ₗ[ℂ] ℂ} (hℓ : InvForm ψ S T a ℓ) (u : WO S T)
    {y : WO S T} (hy : IsHalf a y) :
    ℓ (heisO ψ S T y (heisO ψ S T ((1 - E) • u) g)) =
      Φ y * (Φ x₀)⁻¹ * ℓ (heisO ψ S T x₀ (heisO ψ S T ((1 - E) • u) g)) := by
  have h1 := shape_ratio hs hx₀ h0 (invForm_comp hψ ha hE hℓ u) hy
  simp only [LinearMap.comp_apply, heisL_apply] at h1
  rw [← heisO_off_comm ψ (cA_E hE) u y (smul_half_zero (one_sub_mul_self ha hE) hy),
    ← heisO_off_comm ψ (cA_E hE) u x₀ (smul_half_zero (one_sub_mul_self ha hE) hx₀)]
  exact h1

theorem heisO_factor (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) {a E : AE D} (hE : a + cA D a = E) (x u : WO S T) :
    ∃ p : ℂ, ∀ g, heisO ψ S T x (heisO ψ S T u g) =
      p • heisO ψ S T (cA D a • u) (heisO ψ S T (x + a • u) (heisO ψ S T ((1 - E) • u) g)) := by
  have hsum : cA D a • u + ((x + a • u) + (1 - E) • u) = x + u := by
    rw [← hE]; ext i j; simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]; ring
  obtain ⟨q, hq0, hq⟩ : ∃ q : ℂ, q ≠ 0 ∧ ∀ g, heisO ψ S T (cA D a • u)
      (heisO ψ S T (x + a • u) (heisO ψ S T ((1 - E) • u) g)) = q • heisO ψ S T (x + u) g := by
    refine ⟨ψ (symplOH S T (x + a • u) ((1 - E) • u)) * ψ (symplOH S T (cA D a • u) ((x + a • u) + (1 - E) • u)),
      mul_ne_zero (psi_ne_zero _ _) (psi_ne_zero _ _), fun g => ?_⟩
    rw [heisO_heisO ψ S T (x + a • u), heisO_smul, heisO_heisO, hsum, smul_smul]
  refine ⟨ψ (symplOH S T x u) * q⁻¹, fun g => ?_⟩
  rw [hq, smul_smul, inv_mul_cancel_right₀ hq0, heisO_heisO]

theorem form_sum (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} (ℓ : (WO S T → ℂ) →ₗ[ℂ] ℂ) (y : WO S T)
    (c : WO S T →₀ ℂ) (F : WO S T → ℂ → (WO S T → ℂ)) :
    ℓ (heisO ψ S T y (c.sum F)) = c.sum fun u z => ℓ (heisO ψ S T y (F u z)) := by
  rw [← heisL_apply, map_finsuppSum, map_finsuppSum]
  rfl

theorem sum_map_single (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} (c : WO S T →₀ ℂ) (k : WO S T → ℂ)
    (τ : WO S T → WO S T) (g : WO S T → ℂ) :
    ((c.sum fun u z => Finsupp.single (τ u) (z * k u)).sum fun u z => z • heisO ψ S T u g) =
      c.sum fun u z => (z * k u) • heisO ψ S T (τ u) g := by
  rw [Finsupp.sum_sum_index (h := fun u z => z • heisO ψ S T u g) (fun _ => zero_smul ℂ _) (fun _ _ _ => add_smul _ _ _)]
  exact Finsupp.sum_congr fun u _ => Finsupp.sum_single_index (zero_smul ℂ _)

theorem mem_support_sum_single {X : Type} (c : X →₀ ℂ) (k : X → ℂ) (τ : X → X) {u : X}
    (hu : u ∈ (c.sum fun u z => Finsupp.single (τ u) (z * k u)).support) : ∃ u₀ ∈ c.support, u = τ u₀ := by
  classical
  obtain ⟨u₀, h₀, h⟩ := Finset.mem_biUnion.1 (Finsupp.support_sum hu)
  exact ⟨u₀, h₀, Finset.mem_singleton.1 (Finsupp.support_single_subset h)⟩

theorem rel_extend {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D} {a E : AE D}
    (ha : IsSplitIdem D a) (hE : a + cA D a = E) {Φ g₁ g₂ : WO S T → ℂ}
    (ht₁ : IsThetaFunO ψ S T g₁) (ht₂ : IsThetaFunO ψ S T g₂)
    (hs₁ : HasShape ψ S T a Φ g₁) (hs₂ : HasShape ψ S T a Φ g₂) (Q Q' : WO S T → Prop)
    (hQ : ∀ u, Q' u → Q ((1 - E) • u))
    (hrel : ∀ c : WO S T →₀ ℂ, (∀ u ∈ c.support, Q u) → (c.sum fun u z => z • heisO ψ S T u g₁) = 0 →
      (c.sum fun u z => z • heisO ψ S T u g₂) = 0)
    (c : WO S T →₀ ℂ) (hc : ∀ u ∈ c.support, Q' u) (h1 : (c.sum fun u z => z • heisO ψ S T u g₁) = 0) :
    (c.sum fun u z => z • heisO ψ S T u g₂) = 0 := by
  have hsep := GlobalTheory.T.splitPlace_invariantForms_separate_thetaFunctions D ψ S T hψ a ha
  have hz : ∀ x, heisO ψ S T x (0 : WO S T → ℂ) = 0 := fun x => (heisL ψ S T x).map_zero
  have hlc : ∀ (k : WO S T → ℂ) (τ : WO S T → WO S T) (g : WO S T → ℂ), IsThetaFunO ψ S T g →
      IsThetaFunO ψ S T (c.sum fun u z => (z * k u) • heisO ψ S T (τ u) g) := fun k τ g hg =>
    theta_sum c.support _ g hg fun u _ => theta_smul _ (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hg _)
  have hlc0 : ∀ g, IsThetaFunO ψ S T g → IsThetaFunO ψ S T (c.sum fun u z => z • heisO ψ S T u g) := fun g hg =>
    theta_sum c.support _ g hg fun u _ => theta_smul _ (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hg _)
  by_cases hΦ : ∀ x, IsHalf a x → Φ x = 0
  · have hg2 : g₂ = 0 := hsep g₂ ht₂ fun ℓ hℓ x hx => by
      obtain ⟨k, hk⟩ := hs₂ ℓ hℓ
      rw [hk x hx, hΦ x hx, mul_zero]
    subst hg2
    unfold Finsupp.sum
    refine Finset.sum_eq_zero fun u _ => ?_
    show c u • heisO ψ S T u 0 = 0
    rw [hz, smul_zero]
  push_neg at hΦ
  obtain ⟨x₀, hx₀, h0⟩ := hΦ
  choose p hp using fun x u => heisO_factor ψ S T hE x u
  have key : ∀ g, IsThetaFunO ψ S T g → HasShape ψ S T a Φ g → ∀ ℓ, InvForm ψ S T a ℓ → ∀ x, IsHalf a x →
      ℓ (heisO ψ S T x (c.sum fun u z => z • heisO ψ S T u g)) =
        ℓ (heisO ψ S T x₀ (c.sum fun u z => (z * (p x u * Φ (x + a • u) * (Φ x₀)⁻¹)) •
          heisO ψ S T ((1 - E) • u) g)) := by
    intro g hg hsg ℓ hℓ x hx
    rw [form_sum, form_sum]
    refine Finsupp.sum_congr fun u _ => ?_
    have ht : IsThetaFunO ψ S T (heisO ψ S T (x + a • u) (heisO ψ S T ((1 - E) • u) g)) :=
      GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hg _) _
    rw [heisO_smul, heisO_smul, map_smul, map_smul, smul_eq_mul, smul_eq_mul, hp x u g, map_smul,
      smul_eq_mul, hℓ _ (half_conj ha u) _ ht, shape_off hψ ha hE hsg hx₀ h0 hℓ u (half_add ha hx u)]
    ring
  have shp : ∀ g, HasShape ψ S T a Φ g → ∀ ℓ, InvForm ψ S T a ℓ → ∀ (k : WO S T → ℂ) y, IsHalf a y →
      ℓ (heisO ψ S T y (c.sum fun u z => (z * k u) • heisO ψ S T ((1 - E) • u) g)) =
        Φ y * (Φ x₀)⁻¹ * ℓ (heisO ψ S T x₀ (c.sum fun u z => (z * k u) • heisO ψ S T ((1 - E) • u) g)) := by
    intro g hsg ℓ hℓ k y hy
    rw [form_sum, form_sum, Finsupp.mul_sum]
    refine Finsupp.sum_congr fun u _ => ?_
    rw [heisO_smul, heisO_smul, map_smul, map_smul, smul_eq_mul, smul_eq_mul,
      shape_off hψ ha hE hsg hx₀ h0 hℓ u hy]
    ring
  have hA : ∀ x, IsHalf a x → (c.sum fun u z => (z * (p x u * Φ (x + a • u) * (Φ x₀)⁻¹)) •
      heisO ψ S T ((1 - E) • u) g₁) = 0 := by
    intro x hx
    refine hsep _ (hlc _ _ g₁ ht₁) fun ℓ hℓ y hy => ?_
    rw [shp g₁ hs₁ ℓ hℓ _ y hy, ← key g₁ ht₁ hs₁ ℓ hℓ x hx, h1, hz, map_zero, mul_zero]
  have hB : ∀ x, IsHalf a x → (c.sum fun u z => (z * (p x u * Φ (x + a • u) * (Φ x₀)⁻¹)) •
      heisO ψ S T ((1 - E) • u) g₂) = 0 := by
    intro x hx
    have h := hrel (c.sum fun u z => Finsupp.single ((1 - E) • u) (z * (p x u * Φ (x + a • u) * (Φ x₀)⁻¹)))
      (fun u hu => by
        obtain ⟨u₀, h₀, rfl⟩ := mem_support_sum_single c _ (fun u => (1 - E) • u) hu
        exact hQ u₀ (hc u₀ h₀))
      (by rw [sum_map_single]; exact hA x hx)
    rwa [sum_map_single] at h
  exact hsep _ (hlc0 g₂ ht₂) fun ℓ hℓ x hx => by rw [key g₂ ht₂ hs₂ ℓ hℓ x hx, hB x hx, hz, map_zero]

theorem offPl_step {S T' : HSp D} {Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))} {v : HeightOneSpectrum (𝓞 D.host.F)}
    {ε : AF D.host.F} {a : AE D} (ha : IsSplitIdem D a) (hε : IsPlaceIdem D v ε)
    (hE : a + cA D a = algebraMap (AF D.host.F) (AE D) ε) (u : WO S T') (hu : OffPl (dropPl Sb v) u) :
    OffPl Sb ((1 - algebraMap (AF D.host.F) (AE D) ε) • u) := by
  obtain ⟨hinf, hpl⟩ := hu
  refine ⟨?_, fun w hw ε' hε' i j => ?_⟩
  · ext i j
    have h := congrFun (congrFun hinf i) j
    simp only [Matrix.map_apply, Matrix.zero_apply] at h ⊢
    rw [Matrix.smul_apply, smul_eq_mul, map_mul, h, mul_zero]
  · rw [Matrix.smul_apply, smul_eq_mul]
    by_cases hwv : w = v
    · rw [hwv] at hε'
      rw [GlobalTheory.PlaceDatum.placeIdem_eq hε' hε, ← mul_assoc, mul_sub, mul_one, idem_E ha hE, sub_self, zero_mul]
    · have h := hpl w (by classical unfold dropPl; convert Finset.mem_erase.2 ⟨hwv, hw⟩) ε' hε' i j
      rw [mul_left_comm, h, mul_zero]

theorem likeOff_dropPl : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), IsStdChar D R.ψ (-1) → ∀ (i : Fin D.R.m) (t : T) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))) (v : HeightOneSpectrum (𝓞 D.host.F)) (ε : AF D.host.F) (a : AE D), IsSplitIdem D a → IsPlaceIdem D v ε → a + cA D a = algebraMap (AF D.host.F) (AE D) ε → IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.vP i t) → ∀ Φ f : WO (Vc D i) (Wc D i) → ℂ, HasShape R.ψ (Vc D i) (Wc D i) a Φ (R.vP i t) → HasShape R.ψ (Vc D i) (Wc D i) a Φ f → LikeOff R i t Sb f → LikeOff R i t (dropPl Sb v) f := by
  intro D G _ _ Pl0 T A Ks _ _ _ R hψ i t Sb v ε a ha hε hE hvP Φ f hsP hsf hL
  exact ⟨hL.1, fun c hc h1 => rel_extend hψ ha hE hvP hL.1 hsP hsf (OffPl Sb) (OffPl (dropPl Sb v))
    (fun u hu => offPl_step ha hε hE u hu) hL.2 c hc h1⟩

end GlobalTheory.DownLift.SplitRel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaWeilTwist
section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.WeilTwistSeries

theorem twist_val_mem {D : D7} {pd : ℕ} {k : Type} [Field k] {σ : k →+* ℂ} {δ : Formalism.L2.Host.HChar D.host.E}
    {δc : (AE D)ˣ →* Circle} (h : IsTwist pd σ δ δc) (x : (AE D)ˣ) : ((δc x : Circle) : ℂ) ∈ σ.fieldRange := by
  obtain ⟨hE, ⟨n, hn, ho⟩, -, ht, -, hv⟩ := h
  have : IsTotallyComplex D.host.E := D.sp.cm.cmUnram.1
  have hfin := (GlobalTheory.Mem.UnrAe.unr_ae_and_level _ δ).1
  have hu : ∀ v, v ∉ hfin.toFinset → δ.UnrAt v := fun v hv' => by
    by_contra hc
    exact hv' (hfin.mem_toFinset.2 hc)
  refine GlobalTheory.TwistValues.char_mem δc δ hE hn ho σ.fieldRange (fun P k => ?_) x
  exact GlobalTheory.TwistValues.locK_mem δ (GlobalTheory.RationalValues.unitsIn σ.fieldRange) hfin.toFinset ht
    (GlobalTheory.TypeValues.inf_eq_one δ hn ho) hu
    (fun v hv' => by
      obtain ⟨y, hy⟩ := hv v (hu v hv')
      show ((δ.val v : ℂˣ) : ℂ) ∈ σ.fieldRange
      refine ⟨y, ?_⟩
      rw [hy, Formalism.L2.Host.HChar.valTw]
      simp) P k

theorem theta_weil_twist : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
    (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec),
    LawsJ T → R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ →
    ∀ (i : Fin D.R.m) (hV : T.V ((i : ℕ) + 1) T.σ₀ = Wc D i), GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin T R i T.σ₀ hV →
    ∀ gramR c0R c0L, Bridge.FamTie R.B R.pl (R.Sb : Set (Formalism.L2.DIV.Pl D.host.E)) R.Q (labLL D)
        (fun τ => Bridge.lamRdef (Ptw D) τ) (fun i τ => Bridge.lamLdef (Vc D i).rank ((i : ℕ) + 1) τ) gramR c0R c0L →
    ∀ u : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ, (∀ ρ, (u ρ : (R.MW i (sg0 D A)).sm ρ) = v₀ i (sg0 D A) ρ) →
      ∀ C : Cover T ((i : ℕ) + 1) T.σ₀, GoodCover T R i C (κ i).n →
      ∀ (δ : Formalism.L2.Host.HChar D.host.E) (δc : (AE D)ˣ →* Circle), IsTwist C.d.pd C.σ₂ δ δc →
      ∀ om : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (WO (Vc D i) (Wc D i) → ℂ),
        IsWeilDatumO R.ψ (Vc D i) (Wc D i) (Lift.chrTh (Lift.tup R.mu0 δc) R.eta ((i : ℕ) + 1)).1
          (Lift.chrTh (Lift.tup R.mu0 δc) R.eta ((i : ℕ) + 1)).2 om →
      ∀ s ∈ GfC (Vc D i), ∀ f : WO (Vc D i) (Wc D i) → ℂ,
        IsLevDatum R.ψ (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) (T.Q.l.M * C.d.pd) C.σ₂.fieldRange (R.vacP i) f →
      ∀ w ∈ ratVec R i (c0L i) C.σ₂.fieldRange,
        ∃ c ∈ C.σ₂.fieldRange, ∃ dd : GA D (Wc D i) → ℂ, (MuVal (Wc D i) δc dd ∨ MuVal (Wc D i) δc⁻¹ dd) ∧
          ∀ g, thetaKO om s g (harmVec R i u w f) = c * (dd g * thetaKO (R.ωP i A.μ0) s g (harmVec R i u w f)) := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hJ hL hG hFam hMod hP hT i hV hpin gramR c0R c0L hB u hu C hC δ δc hδ om hom s hs
    f hf w hw
  have hψ : IsStdChar D R.ψ (-1) := (hP.ωP i A.μ0).std
  have hvac := (hP.vP i A.μ0).1
  have hθ : IsInfFam R.θ := hvac.2.inf
  have hf0 : IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.vacP i) := GlobalTheory.OneMapRef.isThetaFunO_of_isVacO hvac
  obtain ⟨P, e, Φ, -, -, -, -, -, hTh⟩ := hf
  have hft : IsThetaFunO R.ψ (Vc D i) (Wc D i) f := GlobalTheory.VecTheta.isThetaFunO_of_thetaAt hψ hθ hTh hf0
  have hH : IsThetaFunO R.ψ (Vc D i) (Wc D i) (harmVec R i u w f) :=
    GlobalTheory.Chain.InnerSteps.theta_pureTensorO hψ hθ _ _ _ _ hft _
  have hxi : R.xi A.μ0 = 1 :=
    MonoidHom.ext (GlobalTheory.TwistFactorCompare.eq_one_of_chrEq_one (hL.xi_base ▸ hL.xi A.μ0))
  have hmu : R.toLevCh.mu A.μ0 = Lift.tup R.mu0 (1 : (AE D)ˣ →* Circle) := by
    unfold LevCh.mu
    rw [hxi]
  have hω : IsWeilDatumO R.ψ (Vc D i) (Wc D i) (Lift.chrTh R.mu0 R.eta ((i : ℕ) + 1)).1
      (Lift.chrTh R.mu0 R.eta ((i : ℕ) + 1)).2 (R.ωP i A.μ0) := by
    have h := hP.ωP i A.μ0
    rw [hmu, GlobalTheory.SplitChange.chrTh_tup] at h
    simpa only [mul_one] using h
  rw [GlobalTheory.SplitChange.chrTh_tup] at hom
  have hδH : IsHeckeChar D δc := hδ.1.1
  have hδF : ∀ a, δc (idF D a) = 1 := GlobalTheory.GridWeil.triv_base hδ.1 hδ.2.2.1
  obtain ⟨nV, hnV, -⟩ := GlobalTheory.Member.exists_muVal D (Vc D i) δc hδH hδF
  obtain ⟨nW, hnW, -⟩ := GlobalTheory.Member.exists_muVal D (Wc D i) δc hδH hδF
  obtain ⟨x, hx⟩ := hnV.1 s
  refine ⟨(nV s)⁻¹, ?_, nW, Or.inl hnW, fun g => ?_⟩
  · rw [hnV.2 s x hx]
    exact inv_mem (twist_val_mem hδ x)
  · rw [GlobalTheory.SplitChange.thetaKO_twist hω hδH hδF hom hnV hnW s g hH]
    ring

end GlobalTheory.WeilTwistSeries
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistingCharacterLadicGaloisCharacterEqHecke
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab toAb IsGlobalArtin)
open Formalism.L2.Host (embLL0)
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeriesTie

theorem charOf_psiAt_chrEq : ∀ (D : D7) (a : Recip D D.nd.Om) (i : D.ntw.Tw) (κ : FractionRing (D.ntw.O0 i) →+* Qbar (D.ntw.l i)) (ι : Qbar (D.ntw.l i) ≃+* ℂ) (χ : Formalism.L2.Host.HChar D.host.E) (r : G D.host.E D.nd.Om →* (D.ntw.O0 i)ˣ) (b : Bool), a.Good → IsOpen (r.ker : Set (G D.host.E D.nd.Om)) → GlobalTheory.GalChar.IsGal a.art κ ι χ (fun _ => 0) (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b r) → ∀ (f : D.ntw.O0 i →+* ℂ), (∀ y, IsIntegral ℤ y → f y = ι (κ (algebraMap (D.ntw.O0 i) (FractionRing (D.ntw.O0 i)) y))) → ∀ (ch : Set (Pl D.host.E)) (Q : Finset (Pl D.host.E)), ChrEq (twistOf a f ch Q (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b r)).chi χ := by
  intro D a i κ ι χ r b ha hr hg f hf ch Q
  set ψ := Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b r with hψdef
  have hker : ψ.ker = r.ker := by
    cases b
    · ext σ
      simp [hψdef, Formalism.MainNotions.BlochKatoReduction.Gen.psiAt]
    · simp [hψdef, Formalism.MainNotions.BlochKatoReduction.Gen.psiAt]
  have hop : IsOpen (ψ.ker : Set (G D.host.E D.nd.Om)) := hker ▸ hr
  have hfi : ψ.ker.FiniteIndex := by
    let H : OpenNormalSubgroup (G D.host.E D.nd.Om) := { toSubgroup := ψ.ker, isOpen' := hop, isNormal' := inferInstance }
    exact inferInstanceAs (OpenNormalSubgroup.toFiniteIndexNormalSubgroup H).toSubgroup.FiniteIndex
  have hn : ψ.ker.index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
  have hpow : ∀ σ, ψ σ ^ ψ.ker.index = 1 := fun σ => by
    rw [← map_pow]
    exact ψ.mem_ker.1 (Subgroup.pow_index_mem _ σ)
  have key : ∀ (x : (AE D)ˣ) (σ : G D.host.E D.nd.Om), a.sym x = toAb D.host.E D.nd.Om σ →
      ((charOf a f ψ x : Circle) : ℂ) = ((χ.1 (Units.map a.κ.toMonoidHom x) : ℂˣ) : ℂ) := by
    intro x σ hx
    rw [charOf_eq a f hop hx hn (hpow σ)]
    have hint : IsIntegral ℤ ((ψ σ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i) :=
      IsIntegral.of_pow (Nat.pos_of_ne_zero hn) (by
        rw [← Units.val_pow_eq_pow_val, hpow σ, Units.val_one]
        exact isIntegral_one)
    rw [hf _ hint]
    have h1 := hg.2.2 (Units.map a.κ.toMonoidHom x) σ hx
    simp [GlobalTheory.GalChar.inQ, GlobalTheory.GalChar.toQ, GlobalTheory.HeckeGal.infPow, GlobalTheory.HeckeGal.lPow, GlobalTheory.HeckeGal.locPow] at h1
    rw [h1]
    simp

  have hsymc : Continuous a.sym :=
    ha.artin.quot.continuous.comp (Continuous.units_map _ ha.cont)
  have hdesc : IsOpen (((descend ψ : Gab D.host.E D.nd.Om →* (D.ntw.O0 i)ˣ).ker : Set (Gab D.host.E D.nd.Om))) := by
    have hpre : (toAb D.host.E D.nd.Om) ⁻¹' ((descend ψ).ker : Set (Gab D.host.E D.nd.Om)) = (ψ.ker : Set _) := by
      ext σ
      simp [descend_toAb hop]
    have hs : Function.Surjective (toAb D.host.E D.nd.Om) := QuotientGroup.mk'_surjective _
    rw [← Set.image_preimage_eq ((descend ψ).ker : Set (Gab D.host.E D.nd.Om)) hs, hpre]
    exact QuotientGroup.isOpenMap_coe _ hop
  have hpullo : IsOpen (((a.pull ψ).ker : Set (AE D)ˣ)) := by
    have : ((a.pull ψ).ker : Set (AE D)ˣ) = a.sym ⁻¹' ((descend ψ).ker : Set _) := by
      ext x
      simp [Recip.pull]
    rw [this]
    exact hdesc.preimage hsymc
  refine ⟨⟨?_, fun k => ?_⟩, fun P e he k x hx => ?_⟩
  · refine continuous_of_continuousAt_one (charOf a f ψ) ?_
    refine ContinuousAt.congr (continuousAt_const (y := (1 : Circle))) (Filter.eventuallyEq_of_mem (hpullo.mem_nhds (map_one _)) fun x hx => ?_)
    change (1 : Circle) = charOf a f ψ x
    rw [charOf, MonoidHom.comp_apply, MonoidHom.comp_apply, (a.pull ψ).mem_ker.1 hx, map_one, map_one]
  · have hs : a.sym (Units.map (incA D).toMonoidHom k) = 1 := by
      change a.art (Units.map a.κ.toMonoidHom (Units.map (incA D).toMonoidHom k)) = 1
      rw [← MonoidHom.mem_ker, ha.artin.ker]
      apply Subgroup.le_topologicalClosure
      apply Subgroup.mem_sup_left
      exact ⟨k, Units.ext (ha.rat k).symm⟩
    change unitPart (Units.map f.toMonoidHom (descend ψ (a.sym (Units.map (incA D).toMonoidHom k)))) = 1
    rw [hs, map_one, map_one, map_one]
  · obtain ⟨σ, hσ⟩ := a.exists_sym x
    have hy : Units.map a.κ.toMonoidHom x =
        Neutral.B1.localIdele D.host.E P (Formalism.L2.Host.atFin P k) :=
      Units.ext ((congrArg a.κ hx).trans (ha.loc P e he k))
    change ((charOf a f ψ x : Circle) : ℂ) = _
    rw [key x σ hσ, hy]
    rfl
end GlobalTheory.SeriesTie

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UpperLeftBlockEqOneIffOfMemBlockTri
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PrincipalLevel

theorem upperLeftBlock_eq_one_iff_of_mem_blockTri {κ : Type} [CommRing κ] {n r : ℕ} (hr : r ≤ n) (h : r = n) (g : GL (Fin n) κ) :
    upperLeftBlock hr g = 1 ↔ g = 1 := by
  subst h
  have hg : g ∈ blockTri (κ := κ) (blk2 r) := fun i j hij => by
    simp [blk2, i.2, j.2] at hij
  constructor
  · intro h1
    apply Units.ext
    ext i j
    have := congrArg (fun u : GL (Fin r) κ => (u : Matrix (Fin r) (Fin r) κ) i j) h1
    simp only [upper_block_val_submatrix hr hg, Matrix.submatrix_apply] at this
    have ei : Fin.castLE hr i = i := Fin.ext rfl
    have ej : Fin.castLE hr j = j := Fin.ext rfl
    rw [ei, ej] at this
    simpa using this
  · rintro rfl
    exact blockDiagonalExtendByOnePrimeField_one _ _

theorem mem_lev_whole {D : D7} {n : ℕ} (J : Matrix (Fin n) (Fin n) D.host.E) (β : GL (Fin n) (Lev.EAf D))
    (L : LevDat D.host.E ℂ n) (hr : L.r = n) (hQ : L.Q = ∅) (hP : L.P.H = ⊥) (x : GL (Fin n) (Lev.EAf D)) :
    x ∈ lev D.sp.cm J β L ↔ x ∈ UA D.sp.cm J ∧ x ∈ St β ∧ ∀ PP ∈ L.Pg, redFn β PP x = 1 := by
  have h0 : ∀ a : Fin n, blkOf L.r L.t a = 0 := fun a => by
    unfold blkOf
    rw [if_pos (by rw [hr]; exact a.2)]
  rw [mem_lev, mem_parLev, hP, Subgroup.mem_bot]
  constructor
  · rintro ⟨⟨h1, h2, -, -⟩, h3⟩
    exact ⟨h1, h2, fun PP hPP => (upperLeftBlock_eq_one_iff_of_mem_blockTri L.hr hr _).1 (congrFun h3 ⟨PP, hPP⟩)⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨⟨h1, h2, fun PP _ i j hij => ?_, fun PP hPP => ?_⟩, funext fun PP => (upperLeftBlock_eq_one_iff_of_mem_blockTri L.hr hr _).2 (h3 PP.1 PP.2)⟩
    · rw [h0, h0] at hij
      exact absurd hij (lt_irrefl 0)
    · rw [hQ] at hPP
      exact absurd hPP (Finset.notMem_empty _)

theorem levK_eq_levG : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {Rl : RealDat3 D A3 Ks} {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd} {ρ : GlobalTheory.SeriesTie.Setup D.ntw}, GlobalTheory.SeriesTie.RealPin Rl cG ρ → ∀ (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool), ρ.levK i j b = Formalism.IndefR.Lev.levG (Wc D j) (Rl.βW j) (Rl.datWp j Rl.triv) := by
  intro D Γ _ _ Pl0 I0 T A3 Ks _ _ _ Rl cG ρ hpin i j b
  show Lev.levG (Wc D j) (ρ.B i j b).F.βT (Lev.flag1L (ρ.B i j b).G.levT) = _
  rw [hpin.frT i j b]
  unfold Lev.levG
  congr 1
  ext x
  rw [mem_lev_whole _ _ _ rfl rfl rfl, mem_lev_whole _ _ _ (FWT.rank_Wc j).symm rfl rfl]
  have hg : (Lev.flag1L (ρ.B i j b).G.levT).Pg = (Rl.datWp j Rl.triv).Pg := hpin.Pg i j b
  rw [hg]

end GlobalTheory.PrincipalLevel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeightZeroSectionValueOnMarkedPeriodSpaceStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weightZeroSection_value_on_markedPeriodSpace : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → Nonempty (FWTie T R κ v₀) → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (M : OMDat T.toCore R i Tp tup), M.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) M.s0) → ∀ (a : Tp) (C : GlobalTheory.Member.Ctx (M.dδ a).Xo₂ (M.dδ a).c₂ ((inC M.c').comp ((M.dδ a).eF.symm : (M.dδ a).c₂.F →+* M.c'.F)) (Wc D i) D.R.r), C.OK → C.ι = iotaW T i → C.x₀ = T.x₀ ((i : ℕ) + 1) M.s0 → ∀ (f : Rul (M.dδ a).Xo₂ (M.dδ a).c₂) (xi : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ) (c0 : ℂ), f ∈ sec (M.dδ a).Xo₂ (M.dδ a).c₂ 0 0 → (∀ u : GA D (Wc D i), gLat (Wc D i) u = latHat (Wc D i) → (∃ w ∈ GlobalTheory.AdLat.hat1 D.host.F (Set.range (algebraMap (𝓞 D.host.E) D.host.E)), ((Matrix.GeneralLinearGroup.det (finHom (Wc D i) u) : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) : (Af D.host.F ⊗[D.host.F] D.host.E)) - 1 = ((M.dδ a).l₂.M : ℕ) • w) → xi (Matrix.GeneralLinearGroup.det (finHom (Wc D i) u)) = 1) → (∀ γ ∈ GQ (Wc D i), xi (Matrix.GeneralLinearGroup.det (finHom (Wc D i) γ)) = 1) → GlobalTheory.OneMapAll.CXiAt (Wc D i) (rank_Wc i) (inC M.c') { M.dδ a with cδ := f } (M.U₂ a) (M.dict₂ a) (iotaW T i) (T.x₀ ((i : ℕ) + 1) M.s0) xi c0 → ∀ (y : FrPt (M.dδ a).Xo₂ (M.dδ a).c₂ (CAt ((inC M.c').comp ((M.dδ a).eF.symm : (M.dδ a).c₂.F →+* M.c'.F)))) (k : Fin C.F.n) P, IsPeriod (C.F.Di k) (fun j => relab (M.dδ a).c₂ ((inC M.c').comp ((M.dδ a).eF.symm : (M.dδ a).c₂.F →+* M.c'.F)) (C.e j).1) P → y.x = C.F.u k P → ∀ h γ : GA D (Wc D i), C.Mark h k γ → toC (evR (M.dδ a).Xo₂ (M.dδ a).c₂ f y) = c0 * ((xi (Matrix.GeneralLinearGroup.det (finHom (Wc D i) (γ * h))) : ℂˣ) : ℂ) := by
  first | exact @GlobalTheory.MarkVal.val_on_marked_space | exact GlobalTheory.MarkVal.val_on_marked_space | (intros; apply GlobalTheory.MarkVal.val_on_marked_space <;> assumption)
end

