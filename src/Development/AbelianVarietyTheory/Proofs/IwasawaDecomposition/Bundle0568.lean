module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0554
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0139
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0110
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0108
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0131
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0525
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0548
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0553
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0559
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0552
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0551
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0492
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0142
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PushInvertibleModelOfIso
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0560
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0534
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1380
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0561
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0544

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNonnegCombOfMemPsdCone
section
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan

noncomputable section

namespace GlobalTheory.PolFan.ConeSpan

theorem exists_margin {ι : Type} [Fintype ι] (M : ι → ι → ℝ)
    (hM : ∀ c : ι → ℝ, c ≠ 0 → 0 < ∑ i, ∑ j, c i * c j * M i j) :
    ∃ η : ℝ, 0 < η ∧ ∀ E : ι → ι → ℝ, (∀ i j, |E i j| ≤ η) → ∀ c : ι → ℝ, c ≠ 0 →
      0 < ∑ i, ∑ j, c i * c j * (M i j + E i j) := GlobalTheory.T.exists_margin_quadForm_pos_of_perturbation M hM

theorem exists_rat_span {L : Type} [AddCommGroup L] [Module.Free ℤ L] [Module.Finite ℤ L]
    (B : L →ₗ[ℤ] L →ₗ[ℤ] ℝ) : ∃ (n : ℕ) (w : Fin n → ℝ) (Q : Fin n → LinearMap.BilinForm ℤ L),
      B = ∑ j, w j • toReal (Q j) ∧ ∀ j, ∃ g : ℝ →+ ℝ, ∀ y z, (Q j y z : ℝ) = g (B y z) := _root_.GlobalTheory.PolFan.exists_sum_toReal_additive_images B

theorem free_finite_int (O : Type) [CommRing O] [IsDomain O] [CharZero O] [Module.Finite ℤ O] (X₁ : Type)
    [AddCommGroup X₁] [Module O X₁] [Module.Finite O X₁] [Module.Projective O X₁] :
    Module.Free ℤ X₁ ∧ Module.Finite ℤ X₁ := by
  have : Module.Finite ℤ X₁ := Module.Finite.trans O X₁
  refine ⟨?_, this⟩
  have : Module.IsTorsionFree O X₁ := Module.Flat.isTorsionFree
  have : Module.IsTorsionFree ℤ X₁ :=
    Module.IsTorsionFree.comap (S := O) (Int.castRingHom O)
      (fun r hr => IsRegular.of_ne_zero (by
        intro h0
        have : r = 0 := by simpa using h0
        subst this
        exact (not_isRegular_zero (R := ℤ)) hr))
      (fun r m => Int.cast_smul_eq_zsmul O r m)
  exact Module.free_of_finite_type_torsion_free'

theorem nonneg_of_near {ι L : Type} [Fintype ι] [AddCommGroup L] (b : Module.Basis ι ℤ L)
    {B₁ : L →ₗ[ℤ] L →ₗ[ℤ] ℝ} (h : IsPosDef B₁) : ∃ η : ℝ, 0 < η ∧ ∀ (P : LinearMap.BilinForm ℤ L) (D : ℝ), 0 < D →
      (∀ i j, |(P (b i) (b j) : ℝ) / D - B₁ (b i) (b j)| ≤ η) → ∀ x, 0 ≤ P x x := by
  obtain ⟨η, hη, hE⟩ := exists_margin (fun i j => B₁ (b i) (b j)) ((isPosDef_iff_basis b B₁).1 h)
  refine ⟨η, hη, fun P D hD hP x => ?_⟩
  have hP' : IsPosDef (toReal P) := (isPosDef_iff_basis b _).2 fun c hc => by
    have h1 := hE (fun i j => (P (b i) (b j) : ℝ) / D - B₁ (b i) (b j)) hP c hc
    simp only [add_sub_cancel] at h1
    simp only [toReal_apply]
    have e : ∑ i, ∑ j, c i * c j * ((P (b i) (b j) : ℝ) / D) = (∑ i, ∑ j, c i * c j * (P (b i) (b j) : ℝ)) / D := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [e] at h1
    exact (div_pos_iff_of_pos_right hD).1 h1
  have := hP'.nonneg x
  simpa using this

theorem exists_nonneg_comb_of_mem_psdCone (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O]
    (bar : O → O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] (B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ)
    (hB : B ∈ psdCone (bar := bar) (X := X)) : ∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (c : Fin m → ℝ),
      (∀ i, γ i ∈ balForms bar X) ∧ (∀ i y, 0 ≤ γ i y y) ∧ (∀ i, 0 ≤ c i) ∧ B = ∑ i, c i • toReal (γ i) := by
  obtain ⟨X₁, _, _, _, r, B₁, hr, hB₁, hpos, hBr⟩ := hB
  have : Module.Finite O X₁ := Module.Finite.of_surjective r hr
  obtain ⟨_, _⟩ := free_finite_int O X₁
  let b := Module.Free.chooseBasis ℤ X₁
  obtain ⟨η, hη, hnear⟩ := nonneg_of_near b hpos
  obtain ⟨n, w, Q, hw, hg⟩ := exists_rat_span B₁
  have hwv : ∀ y z, B₁ y z = ∑ k, w k * (Q k y z : ℝ) := fun y z => by
    simpa [LinearMap.sum_apply] using LinearMap.congr_fun₂ hw y z
  have hQ : ∀ k, Q k ∈ balForms bar X₁ := fun k => by
    obtain ⟨g, hg⟩ := hg k
    refine ⟨fun y z => ?_, fun a y z => ?_⟩
    · exact_mod_cast (hg y z).trans ((congrArg g (hB₁.1 y z)).trans (hg z y).symm)
    · exact_mod_cast (hg _ _).trans ((congrArg g (hB₁.2 a y z)).trans (hg _ _).symm)
  set K : ℝ := ∑ k, ∑ i, ∑ j, |(Q k (b i) (b j) : ℝ)| with hK
  have hKsum : ∀ i j, ∑ k, |(Q k (b i) (b j) : ℝ)| ≤ K := fun i j => Finset.sum_le_sum fun k _ =>
    (Finset.single_le_sum (f := fun j => |(Q k (b i) (b j) : ℝ)|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ j)).trans (Finset.single_le_sum (f := fun i => ∑ j, |(Q k (b i) (b j) : ℝ)|)
      (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i))
  have hKle : ∀ k i j, |(Q k (b i) (b j) : ℝ)| ≤ K := fun k i j =>
    (Finset.single_le_sum (f := fun k => |(Q k (b i) (b j) : ℝ)|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ k)).trans (hKsum i j)
  have hK0 : 0 ≤ K := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  obtain ⟨D, hD⟩ := exists_nat_gt (2 * (n + 1) * K / η)
  have hDpos : (0 : ℝ) < D := lt_of_le_of_lt (by positivity) hD
  have hDK : 2 * (n + 1) * K ≤ D * η := by rw [div_lt_iff₀ hη] at hD; linarith
  set a : Fin n → ℤ := fun k => ⌊(D : ℝ) * w k⌋ with ha
  set δ : Fin n → ℝ := fun k => D * w k - a k with hδ
  have hδ0 : ∀ k, 0 ≤ δ k := fun k => sub_nonneg.2 (Int.floor_le _)
  have hδ1 : ∀ k, δ k ≤ 1 := fun k => by
    have := Int.lt_floor_add_one ((D : ℝ) * w k)
    simp only [hδ, ha]; linarith
  set R : LinearMap.BilinForm ℤ X₁ := ∑ k, a k • Q k with hR
  have hRv : ∀ y z, (R y z : ℝ) = D * B₁ y z - ∑ k, δ k * (Q k y z : ℝ) := fun y z => by
    simp only [hR, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, Int.cast_sum, Int.cast_mul, hwv,
      Finset.mul_sum, ← Finset.sum_sub_distrib, hδ]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hSb : ∀ i j, |∑ k, δ k * (Q k (b i) (b j) : ℝ)| ≤ K := fun i j =>
    (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun k _ => by
      rw [abs_mul, abs_of_nonneg (hδ0 k)]
      exact mul_le_of_le_one_left (abs_nonneg _) (hδ1 k)).trans (hKsum i j))
  have hRnn : ∀ x, 0 ≤ R x x := hnear R D hDpos fun i j => by
    rw [hRv, show (D * B₁ (b i) (b j) - ∑ k, δ k * (Q k (b i) (b j) : ℝ)) / D - B₁ (b i) (b j) =
      -(∑ k, δ k * (Q k (b i) (b j) : ℝ)) / D by field_simp; ring, abs_div, abs_neg, abs_of_pos hDpos,
      div_le_iff₀ hDpos]
    nlinarith [hSb i j]
  let N : ℤ := n + 1
  have hQnn : ∀ k x, 0 ≤ (R + N • Q k) x x := fun k => hnear _ D hDpos fun i j => by
    have e : ((R + N • Q k) (b i) (b j) : ℝ) / D - B₁ (b i) (b j) =
        (N * (Q k (b i) (b j) : ℝ) - ∑ l, δ l * (Q l (b i) (b j) : ℝ)) / D := by
      simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, Int.cast_add, Int.cast_mul, hRv]
      field_simp; ring
    rw [e, abs_div, abs_of_pos hDpos, div_le_iff₀ hDpos]
    have h1 := abs_sub (N * (Q k (b i) (b j) : ℝ)) (∑ l, δ l * (Q l (b i) (b j) : ℝ))
    rw [abs_mul] at h1
    have h2 : |(N : ℝ)| = n + 1 := by simp [N]; positivity
    rw [h2] at h1
    nlinarith [hSb i j, hKle k i j]
  let γ₁ : Fin (n + 1) → LinearMap.BilinForm ℤ X₁ := Fin.cons R fun k => R + N • Q k
  let c : Fin (n + 1) → ℝ := Fin.cons ((1 + ∑ k, (1 - δ k)) / (N * D)) fun k => δ k / (N * D)
  have hN : (0 : ℝ) < N := by simp [N]; positivity
  refine ⟨n + 1, fun i => pull r (γ₁ i), c, fun i => pull_mem r ?_, fun i y => ?_, fun i => ?_, ?_⟩
  · refine Fin.cases ?_ (fun k => ?_) i
    · exact (Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hQ k) : R ∈ _)
    · show R + N • Q k ∈ _
      exact Submodule.add_mem _ (Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hQ k))
        (Submodule.smul_mem _ _ (hQ k))
  · simp only [pull_apply]
    refine Fin.cases ?_ (fun k => ?_) i
    · exact hRnn _
    · exact hQnn k _
  · refine Fin.cases ?_ (fun k => ?_) i
    · refine div_nonneg (add_nonneg zero_le_one (Finset.sum_nonneg fun k _ => sub_nonneg.2 (hδ1 k))) (by positivity)
    · exact div_nonneg (hδ0 k) (by positivity)
  · refine LinearMap.ext₂ fun y z => ?_
    simp only [hBr, LinearMap.sum_apply, LinearMap.smul_apply, toReal_apply, pull_apply, smul_eq_mul,
      Fin.sum_univ_succ, γ₁, c, Fin.cons_zero, Fin.cons_succ, LinearMap.add_apply, Int.cast_add, Int.cast_mul]
    rw [hRv]
    set u := B₁ (r y) (r z)
    set S := ∑ k, δ k * (Q k (r y) (r z) : ℝ)
    have e1 : ∑ k, δ k / (N * D) * (D * u - S + N * (Q k (r y) (r z) : ℝ)) =
        (∑ k, δ k) * (D * u - S) / (N * D) + S / D := by
      rw [Finset.sum_mul, Finset.sum_div, Finset.sum_div, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      field_simp
    have e2 : ∑ k, (1 - δ k) = n - ∑ k, δ k := by
      rw [Finset.sum_sub_distrib]; simp
    rw [e1, e2]
    have hN' : (N : ℝ) = n + 1 := by simp [N]
    rw [hN']
    field_simp
    ring

end GlobalTheory.PolFan.ConeSpan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSemiAbelianPolarized
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory.GenFan.Tri

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l}
  {c : Coeff l}

theorem isOpenImmersion_j_id (Y : Model Xo c (RingHom.id c.F)) : IsOpenImmersion Y.j := by
  unfold Model.j
  have : IsIso (pullback.fst Y.s (spMap (RingHom.id c.F))) := by
    have : IsIso (spMap (RingHom.id c.F)) := by
      show IsIso (Spec.map (CommRingCat.ofHom (RingHom.id c.F)))
      rw [show CommRingCat.ofHom (RingHom.id c.F) = 𝟙 (CommRingCat.of c.F) from rfl, Spec.map_id]
      infer_instance
    infer_instance
  have := Y.jQ_open
  infer_instance

theorem range_j_subset_abLocus {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β) :
    Set.range Y.j ⊆ abLocus Y.t.G := by
  rintro _ ⟨w, rfl⟩
  have h : Y.jQ w ∈ pullback.fst Y.s (spMap β) ⁻¹' abLocus Y.t.G := by rw [Y.ab_gen]; exact ⟨w, rfl⟩
  exact h

end GlobalTheory.GenFan.Tri
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSncCoordinatesComplexPointSmoothVariety
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory
namespace SncChart

theorem linearIndependent_fderiv_params (k : Type) [Field k] [CharZero k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) (n : ℕ) (σ : k →+* ℂ)
    [SmoothOfRelativeDimension n p] (c : AlgChart p σ n) (x₀ : CxPts p σ) (hx : x₀ ∈ c.e.source)
    (U : Y.affineOpens) (hy : x₀.1 (IsLocalRing.closedPoint ℂ) ∈ U.1) (m : ℕ) (f : Fin m → Γ(Y, U.1))
    (hR : ReciprocityTheory.AnForm.R.FinalTheorems.Rsp (Y.presheaf.stalk (x₀.1 (IsLocalRing.closedPoint ℂ))) m
      (fun i => Y.presheaf.germ U.1 _ hy (f i))) :
    LinearIndependent ℂ (fun i => fderiv ℂ (CxPts.ev p σ U.1 (f i) ∘ c.e.symm) (c.e x₀)) := by
  rw [Fintype.linearIndependent_iff]
  intro l hl
  by_contra hne
  push_neg at hne
  have hl0 : l ≠ 0 := fun h => by obtain ⟨i, hi⟩ := hne; exact hi (congrFun h i)
  obtain ⟨δ, hc0, hlb, hne'⟩ := _root_.GlobalTheory.PtDerivSep.exists_ptDer_sep k Y p n σ inferInstance x₀ U hy m f hR l hl0
  obtain ⟨v, hv⟩ := _root_.GlobalTheory.PointDer.exists_eq_fderiv k Y p n σ c x₀ hx U (CxPts.mem_ptsIn.2 hy) δ hc0 hlb
  apply hne'
  have := congrArg (fun F => F v) hl
  simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.coe_smul',
    Pi.smul_apply, smul_eq_mul, ContinuousLinearMap.zero_apply] at this
  simpa [hv] using this

theorem exists_chart_of_fderiv (k : Type) [CommRing k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) (n : ℕ) (σ : k →+* ℂ)
    (c : AlgChart p σ n) (x₀ : CxPts p σ) (hx : x₀ ∈ c.e.source) (W : Y.Opens)
    (hW : x₀ ∈ CxPts.ptsIn p σ W) (a : ℕ) (g : Fin a → Γ(Y, W))
    (h0 : ∀ i, CxPts.ev p σ W (g i) x₀ = 0)
    (hli : LinearIndependent ℂ (fun i => fderiv ℂ (CxPts.ev p σ W (g i) ∘ c.e.symm) (c.e x₀))) :
    ∃ e : OpenPartialHomeomorph (CxPts p σ) (Fin n → ℂ), x₀ ∈ e.source ∧ e.source ⊆ CxPts.ptsIn p σ W ∧
      e x₀ = 0 ∧ (∀ j, HolAlong e.source fun x => e x j) ∧ IsHolTo e.target (fun z => (e.symm z).1) ∧
      ∀ x ∈ e.source, ∀ (j : Fin n) (hj : (j : ℕ) < a), e x j = CxPts.ev p σ W (g ⟨j, hj⟩) x := by
  let c' := c.restr (CxPts.ptsIn p σ W) (CxPts.isOpen_ptsIn W)
  have hx' : x₀ ∈ c'.e.source := ⟨hx, hW⟩
  let G : Fin a → ReciprocityTheory.L2DbarEstimates.V n → ℂ := fun i => CxPts.ev p σ W (g i) ∘ c.e.symm
  have hv0 : c.e x₀ ∈ c'.e.target := c'.e.map_source hx'
  have hG : ∀ i, DifferentiableOn ℂ (G i) c'.e.target := fun i =>
    (c.holo W (g i)).mono (fun v hv => ⟨hv.1, hv.2⟩)
  have hG0 : ∀ i, G i (c.e x₀) = 0 := by
    intro i
    simp only [G, Function.comp_apply, c.e.left_inv hx, h0]
  obtain ⟨ψ, h1, h2, h3, h4, h5, h6⟩ := _root_.GlobalTheory.CompleteCoords.complete_coords n a (c.e x₀) c'.e.target G c'.e.open_target hv0 hG hG0 hli
  obtain ⟨hh, hs⟩ := _root_.GlobalTheory.ShFam.Hor.LogCh.chart_change k Y p n σ c' ψ h4 h5
  refine ⟨c'.e.trans ψ, ⟨hx', h1⟩, fun x hx => hx.1.2, h3, hh, hs, fun x hx j hj => ?_⟩
  have := h6 _ hx.2 j hj
  simp only [OpenPartialHomeomorph.coe_trans, Function.comp_apply] at this ⊢
  refine this.trans ?_
  simp only [G, Function.comp_apply]
  exact congrArg _ (c'.e.left_inv hx.1)

theorem exists_coords : ∀ (k : Type) [Field k] [CharZero k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) (n : ℕ) (D : TopologicalSpace.Closeds Y) (σ : k →+* ℂ), SmoothOfRelativeDimension n p → ReciprocityTheory.AnForm.R.FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal D) → ∀ x₀ : CxPts p σ, ∃ (a : ℕ) (e : OpenPartialHomeomorph (CxPts p σ) (Fin n → ℂ)), x₀ ∈ e.source ∧ e x₀ = 0 ∧ (∀ j, HolAlong e.source fun x => e x j) ∧ IsHolTo e.target (fun z => (e.symm z).1) ∧ ∀ x ∈ e.source, (x.1 (IsLocalRing.closedPoint ℂ) ∉ D ↔ ∀ j : Fin n, (j : ℕ) < a → e x j ≠ 0) := by
  intro k _ _ Y p n D σ hsm hsnc x₀
  haveI := hsm
  obtain ⟨-, U, hy, m, f, J, hR, hD⟩ := hsnc (x₀.1 (IsLocalRing.closedPoint ℂ))
  obtain ⟨c, hc⟩ := AlgChart.exists_mem_source (D := n) (p := p) (σ := σ) x₀
  have hli := linearIndependent_fderiv_params k Y p n σ c x₀ hc U hy m f hR
  let ix : Fin J.card → Fin m := fun i => (J.equivFin.symm i).1
  have hix : Function.Injective ix := fun i j h => J.equivFin.symm.injective (Subtype.ext h)
  have hxU : x₀ ∈ CxPts.ptsIn p σ U.1 := CxPts.mem_ptsIn.2 hy
  have h0 : ∀ i, CxPts.ev p σ U.1 (f (ix i)) x₀ = 0 := by
    intro i
    by_contra hne
    have hb := CxPts.mem_ptsIn.1 ((CxPts.mem_ptsIn_basicOpen hxU (f (ix i))).2 hne)
    rw [Scheme.mem_basicOpen _ _ _ hy] at hb
    have hmem : Y.presheaf.germ U.1 _ hy (f (ix i)) ∈ IsLocalRing.maximalIdeal _ := by
      rw [← hR.1]; exact Ideal.subset_span ⟨ix i, rfl⟩
    exact hmem hb
  have hli' := hli.comp ix hix
  have hcard : J.card ≤ n := by
    have := hli'.fintype_card_le_finrank
    rw [← (LinearMap.toContinuousLinearMap (𝕜 := ℂ) (E := ReciprocityTheory.L2DbarEstimates.V n) (F' := ℂ)).finrank_eq,
      Module.finrank_linearMap, Module.finrank_self, _root_.mul_one] at this
    simpa [ReciprocityTheory.L2DbarEstimates.V] using this
  obtain ⟨e, hx0, hsub, he0, hhol, hsymm, hev⟩ :=
    exists_chart_of_fderiv k Y p n σ c x₀ hc U.1 hxU J.card (fun i => f (ix i)) h0 hli'
  refine ⟨J.card, e, hx0, he0, hhol, hsymm, fun x hx => ?_⟩
  rw [_root_.GlobalTheory.ShFam.mem_iff_exists_ev_eq_zero_of_ideal_eq_span_prod k Y p σ D U m f J hD x (hsub hx)]
  constructor
  · intro h j hj he
    exact h ⟨ix ⟨j, hj⟩, (J.equivFin.symm _).2, by rw [← hev x hx j hj]; exact he⟩
  · rintro h ⟨i, hi, hi0⟩
    have ht : ix (J.equivFin ⟨i, hi⟩) = i := by simp [ix]
    have hlt : ((J.equivFin ⟨i, hi⟩ : Fin J.card) : ℕ) < n := lt_of_lt_of_le (Fin.isLt _) hcard
    refine h ⟨_, hlt⟩ (J.equivFin ⟨i, hi⟩).isLt ?_
    rw [hev x hx ⟨_, hlt⟩ (J.equivFin ⟨i, hi⟩).isLt]
    simpa [ht] using hi0

end SncChart
end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniformisationBaseChangeWithCoordinates
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.LN GlobalTheory
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.UnifCoordPull

theorem exists_unif_psiCoord : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN R → IsCN V → ∀ ψ : R →+* V, IsLocalHom ψ → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (W : Set (Sp R)), IsOpen W → (∀ y, PsiUnitOn D.toPre y W) → (⟨RingHom.ker ψ, RingHom.ker_isPrime ψ⟩ : PrimeSpectrum R) ∈ W → ∀ (G' : Over (Sp V)) [GrpObj G'] [IsCommMonObj G'] (β : G'.left ⟶ G.left), IsGrpPullback G' G (spMap ψ) β → IsAbelianScheme ((Over.pullback (jK V)).obj G') → Rigidified ((Over.pullback (jK V)).obj G') (U.LG.L.pull (pullback.fst G'.hom (jK V) ≫ β)) → Out.Sym ((Over.pullback (jK V)).obj G') (U.LG.L.pull (pullback.fst G'.hom (jK V) ≫ β)) → RelAmple ((Over.pullback (jK V)).obj G') (U.LG.L.pull (pullback.fst G'.hom (jK V) ≫ β)) → KTriv ((Over.pullback (jK V)).obj G') (U.LG.L.pull (pullback.fst G'.hom (jK V) ≫ β)) → ∃ (D' : DegData V (maximalIdeal V)) (A' : PolAV (Sp (FractionRing V))) (U' : Unif (maximalIdeal V) D' A' G') (ε : D'.toPre.X ≃+ D.toPre.X), LBIso (U.LG.L.pull (pullback.fst G'.hom (jK V) ≫ β)) (U'.LG.L.pull (pullback.fst G'.hom (jK V))) ∧ ∀ y r, PsiCoord D.toPre (ε y) r → ∃ u : Vˣ, PsiCoord D'.toPre y (u * ψ r) := by
  intro R _ _ _ V _ _ _ hR hV ψ hψl G _ _ hG D A U W hWo hψ hker G' _ _ β hpb hab hrig hsym hamp hkt
  obtain ⟨-, -, -, h4, -⟩ := GlobalTheory.firstFiveLaws
  have aR := admissibleBase_of_completeNormalLocalCharZero hR
  have aV := admissibleBase_of_completeNormalLocalCharZero hV
  have hI : (maximalIdeal R).map ψ ≤ maximalIdeal V :=
    Ideal.map_le_iff_le_comap.2 fun a ha => (map_mem_nonunits_iff ψ a).2 ha
  obtain ⟨bc, mbc, hbc⟩ := grpPullback_iso hpb (isGrpPullback_pullback G (spMap ψ))
  subst hbc

  have := hG.smooth
  have := hG.geomConnected
  have : ConnectedSpace (Sp R) := inferInstanceAs (ConnectedSpace (PrimeSpectrum R))
  have : ConnectedSpace G.left := GeometricallyConnected.connectedSpace G.hom G.hom.isOpenMap
  obtain ⟨d, hd⟩ := exists_dim_of_preconnected G.hom (Classical.arbitrary _)
  have hgA := GlobalTheory.ThetaBaseChange.grp_generic U.toUnifPre
  have hgK := (isGrpPullback_pullback G' (jK V)).comp hpb
  have dA : d = A.g := H1.dim_unique _ ((smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hgA.1 hd)
    A.smoothDim (eSec A.A (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (FractionRing R)))
  have hdK : SmoothOfRelativeDimension A.g ((Over.pullback (jK V)).obj G').hom :=
    dA ▸ (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hgK.1 hd
  have he := GlobalTheory.PolBaseChange.eSec_comm hpb
  let A' : PolAV (Sp (FractionRing V)) :=
    { A := (Over.pullback (jK V)).obj G'
      isAb := hab
      g := A.g
      smoothDim := hdK
      L := U.LG.L.pull (pullback.fst G'.hom (jK V) ≫ bc.hom.left ≫ pullback.fst G.hom (spMap ψ))
      isLB := pull_isLB U.LG.isLB _
      rigid := hrig
      sym := hsym
      ample := hamp
      ktriv := hkt }
  have eAm : IsMonHom (Iso.refl A'.A).hom := show IsMonHom (𝟙 A'.A) from inferInstance
  have wA : ∃ wA : LB.Iso (A'.L.pull (Iso.refl A'.A).hom.left)
      (U.LG.L.pull (pullback.fst G'.hom (jK V) ≫ bc.hom.left ≫ pullback.fst G.hom (specOf ψ))), wA.IsGen := by
    have k : LBIso (A'.L.pull (𝟙 _)) (U.LG.L.pull (𝟙 _ ≫ pullback.fst G'.hom (jK V) ≫ bc.hom.left ≫
        pullback.fst G.hom (specOf ψ))) :=
      ⟨GlobalTheory.Proof.TautologicalModel.taut U.LG.L _ (𝟙 _), GlobalTheory.Proof.TautologicalModel.taut_isGen U.LG.isLB _ _⟩
    rw [Category.id_comp] at k
    exact k
  let L' : RigLB G' := ⟨U.LG.L.pull (bc.hom.left ≫ pullback.fst G.hom (spMap ψ)),
    rigPullOf (G' := G') (G := G) (bc.hom.left ≫ pullback.fst G.hom (spMap ψ)) (spMap ψ) he U.LG.L U.LG.rig, pull_isLB U.LG.isLB _,
    GlobalTheory.Proof.TautologicalModel.rigPullOf_isGen (G' := G') (G := G) (bc.hom.left ≫ pullback.fst G.hom (spMap ψ)) (spMap ψ) he U.LG.L U.LG.rig U.LG.rigGen⟩
  obtain ⟨wL, gL, rL⟩ := GlobalTheory.Unif.RigidifyIso.exists_rigidified_iso _ _ (spMap ψ) G G' _ he U.LG L'
    (GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB U.LG.isLB _))
  have hgen : (specOf ψ).base (genericPoint (Spec (CommRingCat.of V))) ∈ (⟨W, hWo⟩ : (Sp R).Opens) := by
    have : (specOf ψ).base (genericPoint (Spec (CommRingCat.of V))) =
        (⟨RingHom.ker ψ, RingHom.ker_isPrime ψ⟩ : PrimeSpectrum R) := by
      rw [genericPoint_eq_bot_of_affine]
      exact PrimeSpectrum.ext rfl
    rw [this]; exact hker
  obtain ⟨D', hD, U', hLG, -, -⟩ := h4.unifBaseChange R V _ _ aR aV ψ hI D A G hG U ⟨W, hWo⟩
    (GlobalTheory.PelCoordPull.nonempty_psiOn D.toPre ⟨W, hWo⟩ ⟨_, hker⟩ hψ) hgen G' bc mbc A' rfl (Iso.refl _) eAm wA
    L' wL he gL rL
  refine ⟨D', A', U', hD.xe, ?_, fun y r hr => GlobalTheory.PelCoordPull.psiCoord_pull hD y r hr⟩
  rw [hLG]
  exact LBIso.symm ⟨GlobalTheory.Proof.TautologicalModel.taut U.LG.L _ _, GlobalTheory.Proof.TautologicalModel.taut_isGen U.LG.isLB _ _⟩

end GlobalTheory.UnifCoordPull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitCoefOpen
section
open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries

noncomputable section

namespace GlobalTheory.KeyOpen

theorem glue_units {Z : Scheme.{0}} [IsReduced Z] (V : Z.Opens) (P : Z.Opens → Prop)
    (hP : ∀ p ∈ V, ∃ W : Z.Opens, IsAffineOpen W ∧ W ≤ V ∧ P W ∧ p ∈ W)
    (R : ∀ (L : Type) [Field L], (Sp L ⟶ Z) → L → Prop)
    (uniq : ∀ (L : Type) [Field L] (z : Sp L ⟶ Z), ⊤ ≤ z ⁻¹ᵁ V → ∀ x y, R L z x → R L z y → x = y)
    (loc : ∀ W : Z.Opens, IsAffineOpen W → W ≤ V → P W → ∃ a : Γ(Z, W)ˣ,
      ∀ (L : Type) [Field L] (z : Sp L ⟶ Z) (hz : ⊤ ≤ z ⁻¹ᵁ W), R L z (ev z W hz a.val)) :
    ∃ a : Γ(Z, V)ˣ, ∀ (L : Type) [Field L] (z : Sp L ⟶ Z) (hz : ⊤ ≤ z ⁻¹ᵁ V), R L z (ev z V hz a.val) := by
  let I := {W : Z.Opens // IsAffineOpen W ∧ W ≤ V ∧ P W}
  choose a ha using fun i : I => loc i.1 i.2.1 i.2.2.1 i.2.2.2
  have hc : ∀ p ∈ V, ∃ i : I, p ∈ i.1 := fun p hp => by
    obtain ⟨W, hW, hWV, hPW, hpW⟩ := hP p hp
    exact ⟨⟨W, hW, hWV, hPW⟩, hpW⟩
  have hcov : V ≤ iSup fun i : I => i.1 := fun p hp => TopologicalSpace.Opens.mem_iSup.2 (hc p hp)
  have key : ∀ (i j : I) (L : Type) [Field L] (z : Sp L ⟶ Z) (hz : ⊤ ≤ z ⁻¹ᵁ (i.1 ⊓ j.1)),
      ev z _ hz (resG Z inf_le_left (a i).val) = ev z _ hz (resG Z inf_le_right (a j).val) := by
    intro i j L _ z hz
    have hi := GlobalTheory.FlagMod.le_preimage_mono inf_le_left hz
    have hj := GlobalTheory.FlagMod.le_preimage_mono inf_le_right hz
    rw [GlobalTheory.FlagMod.ev_res z _ hz hi, GlobalTheory.FlagMod.ev_res z _ hz hj]
    exact uniq L z (GlobalTheory.FlagMod.le_preimage_mono i.2.2.1 hi) _ _ (ha i L z hi) (ha j L z hj)
  obtain ⟨s, hs, -⟩ := Z.sheaf.existsUnique_gluing' (fun i : I => i.1) V (fun i => homOfLE i.2.2.1)
    hcov (fun i => (a i).val) (fun i j =>
      GlobalTheory.FlagMod.ext_ev_field (a := resG Z inf_le_left (a i).val) (b := resG Z inf_le_right (a j).val)
        fun L _ z hz => key i j L z hz)
  obtain ⟨t, ht, -⟩ := Z.sheaf.existsUnique_gluing' (fun i : I => i.1) V (fun i => homOfLE i.2.2.1)
    hcov (fun i => (a i)⁻¹.val) (fun i j =>
      GlobalTheory.FlagMod.ext_ev_field (a := resG Z inf_le_left (a i)⁻¹.val) (b := resG Z inf_le_right (a j)⁻¹.val)
        fun L _ z hz => by
          have e := key i j L z hz
          have e₁ := map_units_inv (((ev z _ hz).comp (resG Z inf_le_left)) : Γ(Z, i.1) →+* L) (a i)
          have e₂ := map_units_inv (((ev z _ hz).comp (resG Z inf_le_right)) : Γ(Z, j.1) →+* L) (a j)
          simp only [RingHom.coe_comp, Function.comp_apply] at e₁ e₂
          rw [e₁, e₂, e])
  obtain ⟨s, t, hs, ht⟩ : ∃ s t : Γ(Z, V), (∀ i : I, resG Z i.2.2.1 s = (a i).val) ∧
      ∀ i : I, resG Z i.2.2.1 t = (a i)⁻¹.val := ⟨s, t, hs, ht⟩
  have hval : ∀ (L : Type) [Field L] (z : Sp L ⟶ Z) (hz : ⊤ ≤ z ⁻¹ᵁ V), ∃ i : I, ∃ hi : ⊤ ≤ z ⁻¹ᵁ i.1,
      ev z V hz s = ev z i.1 hi (a i).val ∧ ev z V hz t = ev z i.1 hi (a i)⁻¹.val := by
    intro L _ z hz
    obtain ⟨i, hi⟩ := hc (z (IsLocalRing.closedPoint L)) (hz (Set.mem_univ _))
    have hi' : ⊤ ≤ z ⁻¹ᵁ i.1 := ((IsLocalRing.closed_point_mem_iff (U := z ⁻¹ᵁ i.1)).1 hi).ge
    exact ⟨i, hi', (GlobalTheory.FlagMod.ev_res z i.2.2.1 hi' hz s).symm.trans (congrArg _ (hs i)),
      (GlobalTheory.FlagMod.ev_res z i.2.2.1 hi' hz t).symm.trans (congrArg _ (ht i))⟩
  have hst : s * t = 1 := GlobalTheory.FlagMod.ext_ev_field fun L _ z hz => by
    obtain ⟨i, hi, e₁, e₂⟩ := hval L z hz
    rw [map_mul, map_one, e₁, e₂, ← map_mul, Units.mul_inv, map_one]
  refine ⟨⟨s, t, hst, by rw [mul_comm, hst]⟩, fun L _ z hz => ?_⟩
  obtain ⟨i, hi, e₁, -⟩ := hval L z hz
  show R L z (ev z V hz s)
  rw [e₁]
  exact ha i L z hi

end GlobalTheory.KeyOpen

namespace GlobalTheory.KeyOpen

end GlobalTheory.KeyOpen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaConstantUniformisedChartFibreEqFamilyConstaStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaConstant_uniformisedChartFibre_eq_familyConstant : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (V : ValuationSubring c.F) (Y : Model Xo c V.subtype) (a : ArcIn Dw l V.subtype ℂ (σ.comp V.subtype)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : GlobalTheory.ArcQ.Wit Y a χ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (Ha : HolArc Y σ a χ W Fu) (th : a.D₀.P.L.Sec) (Θ : GlobalTheory.ArcQ.ThetaDat Ha th) (M : GChart Y), Formalism.L2.PjFree.GoodEmb c σ → IsTypeFn H Dw.p Dw.q ty → PushInvertible Y.t.G Y.t.PP.L → χ ≫ Y.s = spMap (PowerSeries.C (R := ℂ)) ≫ spMap (σ.comp V.subtype) → (∀ x : Sp (PowerSeries ℂ), PowerSeries.X ∉ x.asIdeal → χ x ∈ Set.range Y.j) → ⊤ ≤ χ ⁻¹ᵁ M.U → ∀ (w : ℂ), Ha.T < w.im → ∀ (w₀ : LB.Iso Y.oF.t.PP.L (Xo.univ.t.PP.L.pull Y.m0.toSABMap.φ)) (w₁ : LB.Iso Y.oF.t.PP.L (Y.t.PP.L.pull Y.m.φ)), IsRigIso Y.m0.toSABMap.cm Y.oF.t.PP Xo.univ.t.PP w₀ → IsRigIso Y.m.cm Y.oF.t.PP Y.t.PP w₁ → ∀ K : ℂ, (∀ fr, IsThetaFrameAt Xo.univ.t.PP (Fu.u Ha.i (Ha.Pw w)) (fun z => (Fu.ex Ha.i (Ha.Pw w) z).left) (fun z => thetaChar (Θ.τ w) Θ.c₁ Θ.c₂ (Θ.h.mulVec z)) fr → ∀ (z : Fin g → ℂ) (x : Sp ℂ ⟶ Y.oF.t.G.left) (j : Y.t.PP.L.ι) (k : Y.oF.t.PP.L.ι) (j₀ : Xo.univ.t.PP.L.ι), x ≫ Y.m0.toSABMap.φ = (Fu.ex Ha.i (Ha.Pw w) z).left → x ≫ Y.oF.t.G.hom ≫ pullback.snd _ _ = spMap σ → ⊤ ≤ x ⁻¹ᵁ (LB.div (Y.t.PP.L.pull Y.m.φ) Y.oF.t.PP.L).U (fun _ => j, k) → ⊤ ≤ x ⁻¹ᵁ (LB.div (Xo.univ.t.PP.L.pull Y.m0.toSABMap.φ) Y.oF.t.PP.L).U (fun _ => j₀, k) → valAt' x _ (w₀.s (fun _ => j₀, k)).val * valAt' (x ≫ Y.m.φ) _ (M.θ j) = valAt' x _ (w₁.s (fun _ => j, k)).val * (K * thetaChar (Θ.τ w) Θ.c₁ Θ.c₂ (Θ.h.mulVec z) * fr j₀ z)) → ∀ yF : Sp ℂ ⟶ Xo.XF c, yF ≫ pullback.fst _ _ = Fu.u Ha.i (Ha.Pw w) → yF ≫ pullback.snd _ _ = spMap σ → ∀ (hz : ⊤ ≤ (yF ≫ Y.j) ⁻¹ᵁ M.U) (x : KeyIn ℂ) (φ : x.P.A.left ⟶ Y.t.G.left), GlobalTheory.ArcNormal.KeyAtVia M (yF ≫ Y.j) hz x φ → ∀ (u : HolUnif x.P.A x.P.L g) (c₀ : ℂ), u.IsRig x.rig → GlobalTheory.ArcNormal.ArcFib Y σ Fu Ha.i (Ha.Pw w) x φ u → u.IsFn x.th (fun z => c₀ * thetaChar (Θ.τ w) Θ.c₁ Θ.c₂ (Θ.h.mulVec z)) → c₀ = K := by
  first | exact @GlobalTheory.ArcThetaFib.const_eq | exact GlobalTheory.ArcThetaFib.const_eq | (intros; apply GlobalTheory.ArcThetaFib.const_eq <;> assumption)
end

