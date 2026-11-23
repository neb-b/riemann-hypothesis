module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0611
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0620
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0592
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0618
public import ReciprocityTheory.L2DbarEstimates.Imports
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0609
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0578
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0608
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0610
public import Formalism.PadicSubsetSums.CentralIdempotents.Bundle0002
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0597
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0485
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0612
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologyContinuousCofilteredAffineLimit
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC

abbrev isoSpecSp (X : Scheme.{0}) [IsAffine X] : sch.obj X ⟶ sp Γ(X, ⊤) := sch.map X.isoSpec.hom

theorem pull_isoSpecSp_inv (R : Type) [CommRing R] (F : Shv R) (n : ℤ) (X : Scheme.{0}) [IsAffine X]
    (x : H R (sch.obj X) F n) : pull R (isoSpecSp X) F n (pull R (sch.map X.isoSpec.inv) F n x) = x := by
  rw [← pull_comp, ← sch.map_comp, Iso.hom_inv_id, sch.map_id, pull_id]

theorem pull_isoSpecSp_inv' (R : Type) [CommRing R] (F : Shv R) (n : ℤ) (X : Scheme.{0}) [IsAffine X]
    (x : H R (sp Γ(X, ⊤)) F n) : pull R (sch.map X.isoSpec.inv) F n (pull R (isoSpecSp X) F n x) = x := by
  rw [← pull_comp, ← sch.map_comp, Iso.inv_hom_id, sch.map_id, pull_id]

theorem isoSpecSp_naturality {X Y : Scheme.{0}} [IsAffine X] [IsAffine Y] (f : X ⟶ Y) :
    isoSpecSp X ≫ spMap f.appTop.hom = sch.map f ≫ isoSpecSp Y := by
  simp only [isoSpecSp, spMap, CommRingCat.ofHom_hom, ← sch.map_comp, Scheme.isoSpec_hom_naturality]

theorem pull_isoSpecSp_naturality (R : Type) [CommRing R] (F : Shv R) (n : ℤ) {X Y : Scheme.{0}} [IsAffine X] [IsAffine Y]
    (f : X ⟶ Y) (z : H R (sp Γ(Y, ⊤)) F n) :
    pull R (sch.map f) F n (pull R (isoSpecSp Y) F n z) = pull R (isoSpecSp X) F n (pull R (spMap f.appTop.hom) F n z) := by
  rw [← pull_comp, ← pull_comp, isoSpecSp_naturality]

theorem contCone_of_affine_limit : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F → ∀ (I : Type) [SmallCategory I] [IsCofiltered I] (G : I ⥤ Scheme.{0}) (c : Cone G), IsLimit c → (∀ i, IsAffine (G.obj i)) → ContCone R F (sch.mapCone c) := by
  intro R _ F hF I _ _ G c hc hG
  haveI : IsAffine c.pt := Scheme.isAffine_of_isLimit c hc
  let c' : Cocone (G ⋙ Scheme.Γ.rightOp).leftOp := coconeLeftOpOfCone (Scheme.Γ.rightOp.mapCone c)
  have hc' : IsColimit c' := isColimitCoconeLeftOpOfCone _ (isLimitOfPreserves Scheme.Γ.rightOp hc)
  have hb := GlobalTheory.T.etaleCohomology_filteredColimit_rings_finitary R F hF Iᵒᵖ _ c' hc'
  intro n
  obtain ⟨h1, h2⟩ := hb n
  refine ⟨fun x => ?_, fun i y hy => ?_⟩
  · obtain ⟨j, y', hy'⟩ := h1 (pull R (sch.map c.pt.isoSpec.inv) F n x)
    refine ⟨j.unop, pull R (isoSpecSp (G.obj j.unop)) F n y', ?_⟩
    change pull R (sch.map (c.π.app j.unop)) F n _ = x
    refine (pull_isoSpecSp_naturality R F n (X := c.pt) (Y := G.obj j.unop) (c.π.app j.unop) y').trans ?_
    change pull R (isoSpecSp c.pt) F n (pull R (spMap (c'.ι.app j).hom) F n y') = x
    rw [hy', pull_isoSpecSp_inv]
  · change pull R (sch.map (c.π.app i)) F n y = 0 at hy
    let y' : H R (sp Γ(G.obj i, ⊤)) F n := pull R (sch.map (G.obj i).isoSpec.inv) F n y
    have hyy : y = pull R (isoSpecSp (G.obj i)) F n y' := (pull_isoSpecSp_inv R F n _ y).symm
    have hz : pull R (spMap (c'.ι.app (op i)).hom) F n y' = 0 := by
      have e : pull R (isoSpecSp c.pt) F n (pull R (spMap (c.π.app i).appTop.hom) F n y') = 0 := by
        rw [← pull_isoSpecSp_naturality R F n (X := c.pt) (Y := G.obj i) (c.π.app i) y', ← hyy]
        exact hy
      have e2 := congrArg (pull R (sch.map c.pt.isoSpec.inv) F n) e
      rw [pull_isoSpecSp_inv', map_zero] at e2
      exact e2
    obtain ⟨k, f, hk⟩ := h2 (op i) y' hz
    refine ⟨k.unop, f.unop, ?_⟩
    change pull R (sch.map (G.map f.unop)) F n y = 0
    rw [hyy]
    refine (pull_isoSpecSp_naturality R F n (X := G.obj k.unop) (Y := G.obj i) (G.map f.unop) y').trans ?_
    change pull R (isoSpecSp (G.obj k.unop)) F n (pull R (spMap ((G ⋙ Scheme.Γ.rightOp).leftOp.map f).hom) F n y') = 0
    rw [hk]
    exact AddMonoidHom.map_zero _

end GlobalTheory.EtC
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantCoeffIterateInvariantDerivationCongr
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer

set_option autoImplicit false

namespace GlobalTheory.LawDer.IterateLocal

open MvPowerSeries in
set_option autoImplicit false in
private lemma iterate_invDer_sub (R : Type) [CommRing R] (d : ℕ)
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (hμ : ∀ i, constantCoeff (μ i) = 0)
    (u : Fin d → R) :
    ∀ (m : ℕ) (F G : MvPowerSeries (Fin d) R),
      (_root_.GlobalTheory.LawDer.invDer μ u)^[m] F - (_root_.GlobalTheory.LawDer.invDer μ u)^[m] G =
        (_root_.GlobalTheory.LawDer.invDer μ u)^[m] (F - G) := by
  have hadd := (_root_.GlobalTheory.LawDer.Linear.invDer_linear R d μ hμ u).1
  intro m
  induction m with
  | zero => intro F G; rfl
  | succ m ih =>
    intro F G
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, Function.iterate_succ_apply, ih]
    congr 1
    rw [sub_eq_iff_eq_add, ← hadd, sub_add_cancel]

open MvPowerSeries in
set_option autoImplicit false in
private lemma coeff_iterate_invDer_eq_zero_of_degree_lt (R : Type) [CommRing R] (d : ℕ)
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (hμ : ∀ i, constantCoeff (μ i) = 0)
    (u : Fin d → R) (N : ℕ) :
    ∀ (m : ℕ) (H : MvPowerSeries (Fin d) R), (∀ α : Fin d →₀ ℕ, α.degree < N + m → coeff α H = 0) →
      ∀ α : Fin d →₀ ℕ, α.degree < N →
        coeff α ((_root_.GlobalTheory.LawDer.invDer μ u)^[m] H) = 0 := by
  intro m
  induction m with
  | zero => intro H hH α hα; exact hH α (by simpa using hα)
  | succ m ih =>
    intro H hH α hα
    rw [Function.iterate_succ_apply]
    refine ih _ (fun β hβ => ?_) α hα
    exact _root_.GlobalTheory.invDer_coeff_eq_zero_of_degree_lt R d μ hμ u H (N + m)
      (fun γ hγ => hH γ (by omega)) β hβ


open MvPowerSeries in
set_option autoImplicit false in
theorem _root_.GlobalTheory.LawDer.IterateLocal.constantCoeff_iterate_invDer_congr : ∀ (R : Type) [CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R), (∀ i, constantCoeff (μ i) = 0) → ∀ (u : Fin d → R) (n : ℕ) (F G : MvPowerSeries (Fin d) R), (∀ α : Fin d →₀ ℕ, α.degree ≤ n → coeff α F = coeff α G) → constantCoeff ((_root_.GlobalTheory.LawDer.invDer μ u)^[n] F) = constantCoeff ((_root_.GlobalTheory.LawDer.invDer μ u)^[n] G) := by
  intro R _ d μ hμ u n F G hFG
  rw [← sub_eq_zero, ← map_sub, iterate_invDer_sub R d μ hμ u,
    ← coeff_zero_eq_constantCoeff_apply]
  refine coeff_iterate_invDer_eq_zero_of_degree_lt R d μ hμ u 1 n (F - G) (fun α hα => ?_) 0
    (by simp)
  rw [map_sub, hFG α (by omega), sub_self]

end GlobalTheory.LawDer.IterateLocal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantCoeffIteratePInvariantDerivationMul
section
set_option autoImplicit false

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer

namespace GlobalTheory.LawDer

open MvPowerSeries in
set_option autoImplicit false in
private lemma iterate_mul_eq_sum_antidiagonal_choose {A : Type} [CommRing A] (D : A → A)
    (hadd : ∀ a b, D (a + b) = D a + D b) (hmul : ∀ a b, D (a * b) = D a * b + a * D b) (n : ℕ)
    (a b : A) :
    D^[n] (a * b) = ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n, n.choose ij.1 • (D^[ij.1] a * D^[ij.2] b) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hsum : ∀ (s : Finset (ℕ × ℕ)) (f : ℕ × ℕ → A), D (∑ x ∈ s, f x) = ∑ x ∈ s, D (f x) :=
      fun s f => map_sum (AddMonoidHom.mk' D hadd) f s
    have hns : ∀ (m : ℕ) (x : A), D (m • x) = m • D x :=
      fun m x => map_nsmul (AddMonoidHom.mk' D hadd) m x
    have hc := Finset.sum_antidiagonal_choose_succ_nsmul (fun i j => D^[i] a * D^[j] b) n
    beta_reduce at hc
    rw [Function.iterate_succ_apply', ih, hsum, hc, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ij hij => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hij
    rw [← Nat.choose_symm_of_eq_add hij.symm, hns, hmul, ← smul_add]
    simp only [Function.iterate_succ_apply']
    rw [add_comm]


open MvPowerSeries in
set_option autoImplicit false in
theorem _root_.GlobalTheory.LawDer.constantCoeff_iterate_invDer_mul : ∀ (p : ℕ) [Fact p.Prime] (R : Type)
    [CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R),
    (∀ i, constantCoeff (μ i) = 0) →
    _root_.GlobalTheory.Katz.op μ (fun i => (X i : MvPowerSeries (Fin d) R)) (fun _ => 0) =
      (fun i => X i) →
    ∀ (u : Fin d → R) (F G : MvPowerSeries (Fin d) R), constantCoeff F = 0 → constantCoeff G = 0 →
      ∃ r : R, constantCoeff ((_root_.GlobalTheory.LawDer.invDer μ u)^[p] (F * G)) = p * r := by
  intro p hp R _ d μ hμ hid u F G hF hG
  have hlin := _root_.GlobalTheory.LawDer.Linear.invDer_linear R d μ hμ u
  set_option synthInstance.maxHeartbeats 100000 in
    rw [iterate_mul_eq_sum_antidiagonal_choose _ hlin.1
    (_root_.GlobalTheory.LawDer.invDer_mul R d μ hμ hid u), map_sum]
  refine Finset.dvd_sum fun ij hij => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hij
  rw [map_nsmul, map_mul, nsmul_eq_mul]
  rcases Nat.eq_zero_or_pos ij.1 with h1 | h1
  · rw [h1, Function.iterate_zero, id, hF]; simp
  rcases Nat.eq_zero_or_pos ij.2 with h2 | h2
  · rw [h2, Function.iterate_zero, id, hG]; simp
  have hdvd : p ∣ p.choose ij.1 := hp.out.dvd_choose_self h1.ne' (by omega)
  exact Dvd.dvd.mul_right (Nat.cast_dvd_cast hdvd) _

end GlobalTheory.LawDer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffAtPsiOfNotMemZeroSet
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.OTY

theorem contDiffAt_psi_of_notMem_zeroSet : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (L : La) (s : Fin n → ι → Y → ℂ), (∀ k, A.IsSec L (s k)) → ∀ y, y ∉ A.zeroSet s → ∀ i, y ∈ (A.chart i).source → ContDiffAt ℝ ∞ (psi A L s ∘ (A.chart i).symm) (A.chart i y) := by
  intro n Y _ _ _ _ _ ι La _ A L s hs y hy i hi
  have hv : A.chart i y ∈ (A.chart i).target := (A.chart i).map_source hi
  have hU : (A.chart i).target ∈ 𝓝 (A.chart i y) := (A.chart i).open_target.mem_nhds hv
  have hsk : ∀ k, ContDiffAt ℝ ∞ (s k i ∘ (A.chart i).symm) (A.chart i y) := fun k =>
    hyq_contDiffAt_of_holo (A.chart i).open_target (by simpa using (hs k).1 i) hv
  have hph : ContDiffAt ℝ ∞ (A.ph L i ∘ (A.chart i).symm) (A.chart i y) :=
    (A.smooth_ph L i).contDiffAt hU
  have h1 : ContDiffAt ℝ ∞ (fun v => ∑ k, ‖(s k i ∘ (A.chart i).symm) v‖ ^ 2 *
      Real.exp (-(A.ph L i ∘ (A.chart i).symm) v)) (A.chart i y) :=
    ContDiffAt.sum fun k _ => ((hsk k).norm_sq ℂ).mul hph.neg.exp
  have h2 : ContDiffAt ℝ ∞ (A.sqn L s ∘ (A.chart i).symm) (A.chart i y) := by
    refine h1.congr_of_eventuallyEq ?_
    filter_upwards [hU] with v hv'
    simp only [Function.comp, WeightedAtlas.sqn]
    exact Finset.sum_congr rfl fun k _ =>
      WeightedAtlas.nsq_eq_chart A (hs k) ((A.chart i).map_target hv')
  have hpos : 0 < A.sqn L s y := by
    obtain ⟨k, hk⟩ : ∃ k, s k (A.pick y) y ≠ 0 := by
      by_contra h
      exact hy fun k => by_contra fun hk => h ⟨k, hk⟩
    unfold WeightedAtlas.sqn WeightedAtlas.nsq
    refine Finset.sum_pos' (fun _ _ => by positivity) ⟨k, Finset.mem_univ _, ?_⟩
    have := norm_pos_iff.2 hk
    positivity
  have h3 : (A.sqn L s ∘ (A.chart i).symm) (A.chart i y) ≠ 0 := by
    simp only [Function.comp, (A.chart i).left_inv hi]
    exact hpos.ne'
  exact contDiffAt_const.mul (h2.log h3)

end GlobalTheory.OTY
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CounitFormalChartEvSubConstantCoeffDvdStatement
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer
open TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.counit_formalChart_ev_sub_constantCoeff_dvd : ∀ (p : ℕ) (O : Type) [CommRing O] (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (n : ℕ) (F : MvPowerSeries (Fin d) O), (p : O) ∣ Coalgebra.counit (R := O) (c.ev n F) - constantCoeff F := by
  first | exact @GlobalTheory.FrNil.counit_ev_sub_constantCoeff | exact GlobalTheory.FrNil.counit_ev_sub_constantCoeff | (intros; apply GlobalTheory.FrNil.counit_ev_sub_constantCoeff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupProductGradedCommRingAxiomsHoldStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cupProduct_gradedCommRingAxioms_hold : GlobalTheory.EtC.DivisorRingCompatibility := by
  first | (exact @GlobalTheory.EtC.a6ring_holds) | (exact GlobalTheory.EtC.a6ring_holds) | (intros; apply GlobalTheory.EtC.a6ring_holds  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalPiTensorNoBlockUnipotentFixedStatement
section
open CategoryTheory Polynomial Formalism.IrreducibleCountingLemmas.TYPES Formalism.L2.DIV GlobalTheory.HcIrr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspidal_piTensor_no_blockUnipotent_fixed : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (r s : ℕ) (b : Fin r → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K)), (∀ c, IsCuspidal K (lam c)) → ∀ S : Finset (Fin r), (∃ i j, natBlocks b i = natBlocks b j ∧ i ∈ S ∧ j ∉ S) → ∀ y : PiTensorProduct ℂ (fun c => (lam c : Type)), (∀ u : blockTri (κ := K) (natBlocks b), (∀ i j, ((u : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) i j ≠ (1 : Matrix (Fin r) (Fin r) K) i j → natBlocks b i = natBlocks b j ∧ i ∈ S ∧ j ∉ S) → leviTensor b lam u y = y) → y = 0 := by
  first | exact @GlobalTheory.HcIrr.cuspidal_tensor_no_unip_fixed | exact GlobalTheory.HcIrr.cuspidal_tensor_no_unip_fixed | (intros; apply GlobalTheory.HcIrr.cuspidal_tensor_no_unip_fixed <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CutoffHoloSmoothDbarFormula
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
namespace GlobalTheory.L2Cutoff

theorem cutoff_smooth_dbar : ∀ (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M], ∀ (X : EtaleStein n M) (ψ : M → ℝ) (G : M → ℂ) (Ω : Set M) (δ b : ℝ) (θ : ℝ → ℝ), SmoothR n X.z ψ → ContDiff ℝ ∞ θ → (∀ t, b ≤ t → θ t = 0) → IsOpen Ω → (∀ e : OpenPartialHomeomorph M (V n), IsChart n X.z e → DifferentiableOn ℂ (G ∘ e.symm) (e.target ∩ e.symm ⁻¹' Ω)) → (∀ x, δ * ψ x ≤ b → x ∈ Ω) → Smooth n X.z (fun x => (θ (δ * ψ x) : ℂ) * G x) ∧ ∀ (x : M) (ξ : Fin n → ℂ), dbarDot n X.z (fun y => (θ (δ * ψ y) : ℂ) * G y) x ξ = ((deriv θ (δ * ψ x) * δ : ℝ) : ℂ) * G x * dbarDot n X.z (fun y => (ψ y : ℂ)) x ξ := by
  intro n M _ _ _ _ _ X ψ G Ω δ b θ hψ hθ hθ0 hΩ hG hsub
  have hψe : ∀ e : OpenPartialHomeomorph M (V n), IsChart n X.z e →
      ContDiffOn ℝ ∞ (fun v => ψ (e.symm v)) e.target := by
    intro e he
    have h1 := (Complex.reCLM.contDiff (n := ∞)).comp_contDiffOn (hψ e he)
    refine h1.congr fun v _ => ?_
    simp
  have hθd : ∀ t, DifferentiableAt ℝ θ t := fun t => (hθ.differentiable (by simp)) t
  have hθzero : ∀ t, b < t → θ =ᶠ[𝓝 t] fun _ => 0 := by
    intro t ht
    filter_upwards [lt_mem_nhds ht] with s hs
    exact hθ0 s hs.le
  have hloc : ∀ e : OpenPartialHomeomorph M (V n), IsChart n X.z e → ∀ v ∈ e.target,
      (e.symm v ∈ Ω → DifferentiableAt ℂ (G ∘ e.symm) v) ∧
      (e.symm v ∉ Ω → ((fun x => (θ (δ * ψ x) : ℂ) * G x) ∘ e.symm) =ᶠ[𝓝 v] fun _ => 0) := by
    intro e he v hv
    constructor
    · intro hvΩ
      exact (hG e he).differentiableAt
        ((e.isOpen_inter_preimage_symm hΩ).mem_nhds ⟨hv, hvΩ⟩)
    · intro hvΩ
      have hb : b < δ * ψ (e.symm v) := by
        by_contra h
        exact hvΩ (hsub _ (not_lt.1 h))
      have hc : ContinuousAt (fun w => δ * ψ (e.symm w)) v :=
        continuousAt_const.mul ((hψe e he).continuousOn.continuousAt (e.open_target.mem_nhds hv))
      filter_upwards [hc.eventually (lt_mem_nhds hb)] with w hw
      simp [hθ0 _ hw.le]
  refine ⟨?_, ?_⟩
  · intro e he v hv
    apply ContDiffAt.contDiffWithinAt
    by_cases hvΩ : e.symm v ∈ Ω
    · have hU := (e.isOpen_inter_preimage_symm hΩ).mem_nhds ⟨hv, hvΩ⟩
      have hGc : ContDiffAt ℝ ∞ (G ∘ e.symm) v :=
        ((contDiffOn_of_differentiableOn n _ _ (e.isOpen_inter_preimage_symm hΩ) (hG e he)).contDiffAt
          hU).restrict_scalars ℝ
      have hk : ContDiffAt ℝ ∞ (fun w => ((θ (δ * ψ (e.symm w)) : ℝ) : ℂ)) v :=
        Complex.ofRealCLM.contDiff.contDiffAt.comp v
          (hθ.contDiffAt.comp v (contDiffAt_const.mul
            ((hψe e he).contDiffAt (e.open_target.mem_nhds hv))))
      exact hk.mul hGc
    · exact contDiffAt_const.congr_of_eventuallyEq ((hloc e he v hv).2 hvΩ)
  · intro x ξ
    obtain ⟨e, he, hx⟩ := exists_chart n X.z X.isLocalHomeomorph x
    have hzx : X.z x = e x := he hx
    have hv : X.z x ∈ e.target := by rw [hzx]; exact e.map_source hx
    have hsx : e.symm (X.z x) = x := by rw [hzx]; exact e.left_inv hx
    unfold dbarDot
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [db_eq_wdb n X.z e he j _ x hx, db_eq_wdb n X.z e he j _ x hx]
    by_cases hxΩ : x ∈ Ω
    · have hGd := (hloc e he _ hv).1 (by rw [hsx]; exact hxΩ)
      have hψd : DifferentiableAt ℝ (fun w => ψ (e.symm w)) (X.z x) :=
        ((hψe e he).contDiffAt (e.open_target.mem_nhds hv)).differentiableAt (by simp)
      have hkd : DifferentiableAt ℝ (fun t => θ (δ * t)) (ψ (e.symm (X.z x))) :=
        (hθd _).comp _ ((differentiableAt_id).const_mul δ)
      have hderiv : deriv (fun t => θ (δ * t)) (ψ (e.symm (X.z x))) =
          deriv θ (δ * ψ (e.symm (X.z x))) * δ := by
        have h1 : HasDerivAt (fun t : ℝ => δ * t) δ (ψ (e.symm (X.z x))) := by
          simpa using (hasDerivAt_id (ψ (e.symm (X.z x)))).const_mul δ
        exact ((hθd _).hasDerivAt.comp _ h1).deriv
      have h1 : ((fun y => (θ (δ * ψ y) : ℂ) * G y) ∘ e.symm) =
          fun w => (((fun t => θ (δ * t)) (ψ (e.symm w)) : ℝ) : ℂ) * (G ∘ e.symm) w := rfl
      have hkd' : DifferentiableAt ℝ (fun w => (((fun t => θ (δ * t)) (ψ (e.symm w)) : ℝ) : ℂ))
          (X.z x) := differentiableAt_ofReal (DifferentiableAt.comp (f := fun w => ψ (e.symm w)) (X.z x) hkd hψd)
      rw [h1, wdb_mul hkd' (hGd.restrictScalars ℝ), wdb_of_differentiableAt hGd,
        wdb_ofReal_comp (k := fun t => θ (δ * t)) (v := fun w => ψ (e.symm w)) hkd hψd, hderiv]
      have h2 : ((fun y => (ψ y : ℂ)) ∘ e.symm) = fun w => ((ψ (e.symm w) : ℝ) : ℂ) := rfl
      rw [h2]
      simp only [Function.comp_apply, hsx]
      push_cast
      ring
    · have hb : b < δ * ψ x := by
        by_contra h
        exact hxΩ (hsub _ (not_lt.1 h))
      rw [wdb_congr ((hloc e he _ hv).2 (by rw [hsx]; exact hxΩ)),
        ((hθzero _ hb).deriv_eq)]
      simp [wdb]

end GlobalTheory.L2Cutoff
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarEnergyOnCoverBallsLtTopOfSmooth
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory

theorem n1_lt_infty_of_isSSec : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (C : Cover A) (la : La) (F0 : ι → Y → ℂ), A.IsSSec (A.kap + la) F0 → n1 C la F0 < ⊤ := by
  intro n Y _ _ _ _ _ ι La _ A C la F0 hF
  unfold n1
  rw [ENNReal.sum_lt_top]
  intro a _
  set i := C.idx a
  set T := (A.chart i).target
  have hT : IsOpen T := (A.chart i).open_target
  have hsub : closedBall (C.c a) (C.r a) ⊆ T := C.sub a
  have hF' : ContDiffOn ℝ ∞ (F0 i ∘ (A.chart i).symm) T := hF.1 i
  have hD : ContinuousOn (fun v => fderiv ℝ (F0 i ∘ (A.chart i).symm) v) T :=
    hF'.continuousOn_fderiv_of_isOpen hT (by simp)
  have hph : ContinuousOn (fun v => A.ph la i ((A.chart i).symm v)) T :=
    (A.smooth_ph la i).continuousOn
  have hcont : ContinuousOn (fun v => (∑ j, ‖wdb n j (F0 i ∘ (A.chart i).symm) v‖ ^ 2) *
      Real.exp (-A.ph la i ((A.chart i).symm v))) (closedBall (C.c a) (C.r a)) := by
    refine ContinuousOn.mono ?_ hsub
    refine ContinuousOn.mul ?_ ?_
    · refine continuousOn_finsetSum _ (fun j _ => ?_)
      refine ContinuousOn.pow (ContinuousOn.norm ?_) 2
      unfold wdb
      refine ContinuousOn.div_const (ContinuousOn.add ?_ (ContinuousOn.mul continuousOn_const ?_)) _
      · exact hD.clm_apply continuousOn_const
      · exact hD.clm_apply continuousOn_const
    · exact (hph.neg).rexp
  have hint : IntegrableOn (fun v => (∑ j, ‖wdb n j (F0 i ∘ (A.chart i).symm) v‖ ^ 2) *
      Real.exp (-A.ph la i ((A.chart i).symm v))) (closedBall (C.c a) (C.r a)) :=
    hcont.integrableOn_compact (isCompact_closedBall _ _)
  calc _ ≤ ∫⁻ v in closedBall (C.c a) (C.r a), ENNReal.ofReal
        ((∑ j, ‖wdb n j (F0 i ∘ (A.chart i).symm) v‖ ^ 2) *
          Real.exp (-A.ph la i ((A.chart i).symm v))) :=
        lintegral_mono_set ball_subset_closedBall
    _ < ⊤ := hint.lintegral_lt_top

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvdOfForallInvariantDifferentialDvdStatement
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dvd_of_forall_invariantDifferential_dvd : ∀ (p : ℕ) (O : Type) [CommRing O] (G : PDivGroup p O) (n : ℕ) (a : O) (b : G.A n), (∀ (w : G.dual.omega) (φ : CartierDual O (G.A n)), dUnit (R := O) φ = w.1 n → a ∣ φ b) → (∃ z, b = a • z) ∧ ∀ w : G.dual.omega, ∃ φ : CartierDual O (G.A n), dUnit (R := O) φ = w.1 n := by
  first | exact @GlobalTheory.PDivGroup.dvd_of_forall_omega_dvd | exact GlobalTheory.PDivGroup.dvd_of_forall_omega_dvd | (intros; apply GlobalTheory.PDivGroup.dvd_of_forall_omega_dvd <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyTwistedFilteredColimitContinuity
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

theorem GlobalTheory.EtC.pairingProperties : GlobalTheory.EtC.B1 := by
  intro q J _ _ D c hc n i
  have h := GlobalTheory.T.etaleCohomology_filteredColimit_rings_finitary (ZMod q) (tw q i) (GlobalTheory.T.tateTwist_finitary q i) J D c hc n
  exact ⟨fun x _ => h.1 x, fun j y _ hy => h.2 j y hy⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleIsFiniteOfCompEtaleSurjectiveStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_isFinite_of_comp_etale_surjective' : ∀ (X Y Z : Scheme.{0}) (h : X ⟶ Y) (f : Y ⟶ Z), Etale h → Surjective h → Etale (h ≫ f) → IsFinite (h ≫ f) → IsSeparated f → LocallyOfFiniteType f → Etale f ∧ IsFinite f := by
  first | (exact @GlobalTheory.etale_isFinite_of_comp_etale_surjective) | (exact GlobalTheory.etale_isFinite_of_comp_etale_surjective) | (intros; apply GlobalTheory.etale_isFinite_of_comp_etale_surjective <;> assumption)
end

