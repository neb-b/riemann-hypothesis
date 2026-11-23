module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0511
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0254
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0477
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0269
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0495
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0208
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0193
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0512
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0513
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0505
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MemRangeOfForallHeightEqOneOfIsReflexive
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0507
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RiemannExtensionOfLogGrowth

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftThetaMapInnerEqLambdaMulRationalVectorsStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
open Classical
open GlobalTheory.Mem.R3.HasLabelling
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftThetaMap_inner_eq_lambda_mul_rationalVectors : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → ∀ (i : Fin D.R.m) (t : T) (p : A3.fam3.base3.Ix) a b, Y.mj.eW i (D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1) (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a)))) ∈ R.Wp3 i p → ⟪D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1) (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a))), D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1) (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ b)))⟫_ℂ = ((R.lam3 i t p A3.A.v0 : ℝ) : ℂ) * ⟪D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a)), D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ b))⟫_ℂ := by
  first | exact @GlobalTheory.Mem.R3.LamMetric.inner_theta_rat_eq_lam | exact GlobalTheory.Mem.R3.LamMetric.inner_theta_rat_eq_lam | (intros; apply GlobalTheory.Mem.R3.LamMetric.inner_theta_rat_eq_lam <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftThetaMapLabelPartPreimageRationalSpanStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
open Classical
open GlobalTheory.Mem.R3.HasLabelling
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftThetaMap_labelPartPreimage_rationalSpan : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → ∀ (i : Fin D.R.m) (t : T) (p : A3.fam3.base3.Ix), ∀ x ∈ Submodule.span ℂ (Set.range fun a => D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a))), Y.mj.eW i (D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1) x) ∈ R.Wp3 i p → x ∈ Submodule.span ℂ {y | ∃ a, Y.mj.eW i (D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1) (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a)))) ∈ R.Wp3 i p ∧ D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a)) = y} := by
  first | exact @GlobalTheory.Mem.R3.PartSpan.mem_span_part | exact GlobalTheory.Mem.R3.PartSpan.mem_span_part | (intros; apply GlobalTheory.Mem.R3.PartSpan.mem_span_part <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftThetaMapOrthogonalKernelEqRationalSpanStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
open Classical
open GlobalTheory.Mem.R3.HasLabelling
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftThetaMap_orthogonalKernel_eq_rationalSpan : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → ∀ (i : Fin D.R.m) (t : T), (LinearMap.ker (D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1)))ᗮ = Submodule.span ℂ (Set.range fun a => D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a))) := by
  first | exact @GlobalTheory.Mem.KerSpan.orth_ker_thetaP | exact GlobalTheory.Mem.KerSpan.orth_ker_thetaP | (intros; apply GlobalTheory.Mem.KerSpan.orth_ker_thetaP <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftThetaMapSurjectiveOntoCuspFormsUsedTupleStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
open Classical
open GlobalTheory.Mem.R3.HasLabelling
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftThetaMap_surjective_onto_cuspForms_usedTuple : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → HostHyp D → ∀ (i : Fin D.R.m) (t : T), Used0 D (Y.tup t) → Function.Surjective (D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1)) := by
  first | exact @GlobalTheory.Mem.LiftOnto.thetaMap_surjective | exact GlobalTheory.Mem.LiftOnto.thetaMap_surjective | (intros; apply GlobalTheory.Mem.LiftOnto.thetaMap_surjective <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemRadicalOfHolomorphicRatioTendsto
section
open GlobalTheory.ShFam.BdArc Filter Topology

namespace GlobalTheory.ShFam.BdArc

theorem exists_complexPoint_of_notMem {F A : Type} [Field F] [CommRing A] [Algebra F A] [Algebra.FiniteType F A]
    (σ : F →+* ℂ) (P : Ideal A) [hP : P.IsPrime] {s : A} (hs : s ∉ P) :
    ∃ ψ : A →+* ℂ, ψ.comp (algebraMap F A) = σ ∧ (∀ x ∈ P, ψ x = 0) ∧ ψ s ≠ 0 := by
  have : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := F)
  have hj : P.jacobson = P := IsJacobsonRing.out inferInstance hP.isRadical
  rw [← hj, Ideal.jacobson, Ideal.mem_sInf] at hs
  push Not at hs
  obtain ⟨M, ⟨hle, hM⟩, hsM⟩ := hs
  let _ : Field (A ⧸ M) := Ideal.Quotient.field M
  have : Module.Finite F (A ⧸ M) := finite_of_finite_type_of_isJacobsonRing F (A ⧸ M)
  let _ : Algebra F ℂ := σ.toAlgebra
  let κ : (A ⧸ M) →ₐ[F] ℂ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine ⟨(κ.comp (Ideal.Quotient.mkₐ F M)).toRingHom, ?_, fun x hx => ?_, ?_⟩
  · ext x
    exact (κ.comp (Ideal.Quotient.mkₐ F M)).commutes x
  · show κ (Ideal.Quotient.mk M x) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.2 (hle hx), map_zero]
  · show κ (Ideal.Quotient.mk M s) ≠ 0
    rw [map_ne_zero, Ne, Ideal.Quotient.eq_zero_iff_mem]
    exact hsM

theorem dvd_or_dvd_of_height_eq_one {A : Type} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    (P : Ideal A) [P.IsPrime] (hP : P.height = 1) (a b : A) :
    (∃ s, s ∉ P ∧ a ∣ s * b) ∨ ∃ s, s ∉ P ∧ b ∣ s * a := by
  have := GlobalTheory.isDiscreteValuationRing_of_height_eq_one P hP (Localization.AtPrime P)
  have key : ∀ x y : A, algebraMap A (Localization.AtPrime P) x ∣ algebraMap A _ y → ∃ s, s ∉ P ∧ x ∣ s * y := by
    rintro x y ⟨c, hc⟩
    obtain ⟨⟨n, d⟩, hnd⟩ := IsLocalization.surj P.primeCompl c
    refine ⟨d, d.2, n, ?_⟩
    apply IsLocalization.injective (Localization.AtPrime P) P.primeCompl_le_nonZeroDivisors
    simp only at hnd
    rw [map_mul, map_mul, hc, ← hnd]
    ring
  exact (ValuationRing.dvd_total (algebraMap A (Localization.AtPrime P) a) (algebraMap A _ b)).imp (key a b) (key b a)

theorem exists_eq_mul_pow_of_tendsto_zero : ∀ (F A : Type) [Field F] [CommRing A] [IsDomain A] [Algebra F A], Algebra.Smooth F A → ∀ (σ : F →+* ℂ) (p a : A) (m : ℕ), p ≠ 0 → (∀ (ψ : ℂ → (A →+* ℂ)) (r : ℝ), IsHolPts ψ r → (∀ u ∈ Metric.ball (0 : ℂ) r, (ψ u).comp (algebraMap F A) = σ) → ψ 0 p = 0 → (∀ u ∈ Metric.ball (0 : ℂ) r, u ≠ 0 → ψ u p ≠ 0) → Tendsto (fun u => ψ u a / ψ u (p ^ m)) (𝓝[≠] 0) (𝓝 0)) → ∃ b : A, a = b * p ^ m ∧ b ∈ (Ideal.span {p}).radical := by
  intro F A _ _ _ _ hsm σ p a m hp h
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing F A
  have : IsIntegrallyClosed A := GlobalTheory.isIntegrallyClosed_of_smooth F A
  have key : ∀ (P : Ideal A) [P.IsPrime], p ∈ P → ∀ s, s ∉ P → ¬ a ∣ s * p ^ m := by
    rintro P _ hpP s hs ⟨t, ht⟩
    obtain ⟨ψ₀, hσ, hP0, hs0⟩ := exists_complexPoint_of_notMem σ P hs
    obtain ⟨ψ, r, hhol, h0, hσ', hne⟩ := _root_.GlobalTheory.HolArc.exists_holPts_ne_zero F A hsm ψ₀ p hp
    have hlim := h ψ r hhol (fun u hu => (hσ' u hu).trans hσ) (by rw [h0]; exact hP0 p hpP) hne
    have hball : Metric.ball (0 : ℂ) r ∈ 𝓝 (0 : ℂ) := Metric.ball_mem_nhds _ hhol.1
    have hc : ∀ x, Tendsto (fun u => ψ u x) (𝓝[≠] 0) (𝓝 (ψ₀ x)) := fun x => by
      rw [← h0]
      exact (((hhol.2 x).differentiableAt hball).continuousAt.tendsto).mono_left nhdsWithin_le_nhds
    have h1 := hlim.mul (hc t)
    rw [zero_mul] at h1
    have h2 : Tendsto (fun u => ψ u s) (𝓝[≠] 0) (𝓝 0) := by
      refine h1.congr' ?_
      filter_upwards [mem_nhdsWithin_of_mem_nhds hball, self_mem_nhdsWithin] with u hu hu0
      have hpu : ψ u (p ^ m) ≠ 0 := by
        rw [map_pow]
        exact pow_ne_zero _ (hne u hu hu0)
      rw [div_mul_eq_mul_div, ← map_mul, ← ht, map_mul, mul_div_cancel_right₀ _ hpu]
    exact hs0 (tendsto_nhds_unique (hc s) h2)
  obtain ⟨b, hb⟩ : p ^ m ∣ a := by
    refine GlobalTheory.dvd_of_forall_height_eq_one (pow_ne_zero m hp) fun P hP h1 hpm => ?_
    refine (dvd_or_dvd_of_height_eq_one P h1 (p ^ m) a).resolve_right ?_
    rintro ⟨s, hs, hd⟩
    exact key P (hP.mem_of_pow_mem m hpm) s hs hd
  refine ⟨b, by rw [hb, mul_comm], ?_⟩
  rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
  rintro P ⟨hle, hP⟩
  by_contra hbP
  exact key P (hle (Ideal.mem_span_singleton_self p)) b hbP ⟨1, by rw [hb]; ring⟩

end GlobalTheory.ShFam.BdArc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonodromyMatrixDotProductNonnegIntegral
section
open GlobalTheory.ShFam.Hor
open scoped Matrix

namespace GlobalTheory

theorem monodromy_dotProduct_nonneg : ∀ (n a g : ℕ) (ha : a ≤ n) (ρ₁ : ℝ) (τ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ), 0 < ρ₁ → ρ₁ ≤ 1 → (∀ i j, DifferentiableOn ℂ (fun s => τ s i j) {s | s ∈ logDom n a ∧ logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁}) → (∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁ → (τ s).IsSymm ∧ ((τ s).map Complex.im).PosDef) → (∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁ → ∀ k : Fin a, τ (s + Pi.single (Fin.castLE ha k) (2 * Real.pi * Complex.I)) = τ s + (B k).map (Int.cast : ℤ → ℂ)) → ∀ (k : Fin a) (v : Fin g → ℤ), 0 ≤ dotProduct v ((B k).mulVec v) := by
  intro n a g ha ρ₁ τ B hρ0 hρ1 hdiff hpos hmon k v
  by_cases hv : v = 0
  · subst hv; simp
  set j : Fin n := Fin.castLE ha k with hj
  have hjlt : (j : ℕ) < a := by simp [hj]
  let s₀ : Fin n → ℂ := fun i => if (i : ℕ) < a then ((Real.log (ρ₁ / 2) : ℝ) : ℂ) else 0
  let u : ℂ → Fin n → ℂ := fun t => Function.update s₀ j t
  let D := {s : Fin n → ℂ | s ∈ logDom n a ∧ logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁}
  have hlog2 : Real.log (ρ₁ / 2) < 0 := Real.log_neg (by positivity) (by linarith)
  have hlogle : Real.log ρ₁ ≤ 0 := Real.log_nonpos hρ0.le hρ1
  have hexp2 : Real.exp (Real.log (ρ₁ / 2)) = ρ₁ / 2 := Real.exp_log (by positivity)
  have hmem : ∀ t : ℂ, t.re < Real.log ρ₁ → u t ∈ D := by
    intro t ht
    refine ⟨?_, ?_⟩
    · intro i
      by_cases hi : i = j
      · subst hi
        simp only [u, Function.update_self, hjlt, if_true]
        linarith
      · simp only [u, Function.update_of_ne hi, s₀]
        split_ifs with h
        · simpa using hlog2
        · simp
    · rw [mem_ball_zero_iff, pi_norm_lt_iff hρ0]
      intro i
      by_cases hi : i = j
      · subst hi
        simp only [logExp, u, Function.update_self, hjlt, if_true, Complex.norm_exp]
        calc Real.exp t.re < Real.exp (Real.log ρ₁) := Real.exp_lt_exp.2 ht
          _ = ρ₁ := Real.exp_log hρ0
      · simp only [logExp, u, Function.update_of_ne hi, s₀]
        split_ifs with h
        · rw [Complex.norm_exp, Complex.ofReal_re, hexp2]; linarith
        · simpa using hρ0
  let v' : Fin g → ℂ := fun i => (v i : ℂ)
  let f : ℂ → ℂ := fun t => v' ⬝ᵥ (τ (u t) *ᵥ v')
  have hshift : ∀ t : ℂ, u (t + 2 * Real.pi * Complex.I) = u t + Pi.single j (2 * Real.pi * Complex.I) := by
    intro t
    ext i
    by_cases hi : i = j
    · subst hi; simp [u]
    · simp [u, hi, Function.update_of_ne hi, Pi.single_apply]
  have hcast : v' ⬝ᵥ ((B k).map (Int.cast : ℤ → ℂ) *ᵥ v') = ((v ⬝ᵥ (B k *ᵥ v) : ℤ) : ℂ) := by
    simp [v', dotProduct, Matrix.mulVec, Matrix.map_apply]
  have hper : ∀ t : ℂ, t.re < Real.log ρ₁ → f (t + 2 * Real.pi * Complex.I) = f t + ((v ⬝ᵥ (B k *ᵥ v) : ℤ) : ℂ) := by
    intro t ht
    have h1 := hmon (u t) (hmem t ht).1 (hmem t ht).2 k
    simp only [f]
    rw [hshift t, h1, Matrix.add_mulVec, dotProduct_add, hcast]
  let v'' : Fin g → ℝ := fun i => (v i : ℝ)
  have hv'' : v'' ≠ 0 := by
    intro h0
    apply hv
    funext i
    have := congrFun h0 i
    simpa [v''] using this
  have him : ∀ t : ℂ, t.re < Real.log ρ₁ → 0 < (f t).im := by
    intro t ht
    have hp := ((hpos (u t) (hmem t ht).1 (hmem t ht).2).2).dotProduct_mulVec_pos hv''
    have heq : (f t).im = star v'' ⬝ᵥ (((τ (u t)).map Complex.im) *ᵥ v'') := by
      simp [f, v', v'', dotProduct, Matrix.mulVec, Complex.im_sum, Complex.mul_im, Finset.mul_sum]
    rw [heq]; exact hp
  have hu : Differentiable ℂ u := fun t => (hasFDerivAt_update s₀ t).differentiableAt
  have hent : ∀ i l, DifferentiableOn ℂ (fun t => τ (u t) i l) {t : ℂ | t.re < Real.log ρ₁} :=
    fun i l => (hdiff i l).comp hu.differentiableOn (fun t ht => hmem t ht)
  have hdf : DifferentiableOn ℂ f {t : ℂ | t.re < Real.log ρ₁} := by
    simp only [f, dotProduct, Matrix.mulVec]
    apply DifferentiableOn.fun_sum
    intro i _
    apply DifferentiableOn.const_mul
    apply DifferentiableOn.fun_sum
    intro l _
    exact (hent i l).mul_const _
  exact_mod_cast GlobalTheory.T.periodic_left_halfPlane_shift_nonneg_of_im_pos (Real.log ρ₁) f (v ⬝ᵥ (B k *ᵥ v)) hdf hper him

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MultiplierPowerUnitConstant
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.LN GlobalTheory.TorRef GlobalTheory.IntegralCombination GlobalTheory.UU Formalism.L2.Pj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.IntFam

noncomputable section

namespace GlobalTheory.IntFam.CoordPow

theorem pow_law {X Q : Type} [AddCommGroup X] [CommGroup Q] (p : X → Q) (t : X → X → Q)
    (ht : ∀ a b, t a b = p (a + b) * (p a)⁻¹ * (p b)⁻¹) (hadd : ∀ a a' b, t (a + a') b = t a b * t a' b)
    (hev : ∀ χ, p (-χ) = p χ) (k : ℕ) (α μ : X) : p (α + k • μ) = p α * (p μ ^ k * t μ α) ^ k := by
  have hsym : ∀ a b, t a b = t b a := fun a b => by rw [ht, ht, add_comm, mul_right_comm]
  have h0 : ∀ b, t 0 b = 1 := fun b => by
    have := hadd 0 0 b
    rw [add_zero] at this
    exact left_eq_mul.1 this
  have hp0 : p 0 = 1 := by
    have := ht 0 0
    rw [h0, add_zero, mul_inv_cancel, one_mul] at this
    exact inv_eq_one.1 this.symm
  have hneg : ∀ a b, t (-a) b = (t a b)⁻¹ := fun a b => by
    have := hadd a (-a) b
    rw [add_neg_cancel, h0] at this
    exact eq_inv_of_mul_eq_one_right this.symm
  have hmm : t μ μ = p μ ^ 2 := by
    have e1 := hneg μ μ
    rw [hsym, ht, add_neg_cancel, hp0, hev, one_mul] at e1
    rw [← inv_inv (t μ μ), ← e1, ← mul_inv, inv_inv, sq]
  have hn : ∀ (n : ℕ) b, t (n • μ) b = t μ b ^ n := fun n b => by
    induction n with
    | zero => rw [zero_nsmul, pow_zero, h0]
    | succ n ih => rw [succ_nsmul, hadd, ih, pow_succ]
  have key : ∀ n : ℕ, p (α + n • μ) = p α * t μ α ^ n * p μ ^ (n * n) := fun n => by
    induction n with
    | zero => rw [zero_nsmul, add_zero, pow_zero, mul_zero, pow_zero, mul_one, mul_one]
    | succ n ih =>
      have e := ht (α + n • μ) μ
      have e2 : t (α + n • μ) μ = t μ α * (p μ ^ 2) ^ n := by
        rw [hadd, hsym α μ, hn, hmm]
      have e3 : p (α + n • μ + μ) = t (α + n • μ) μ * p (α + n • μ) * p μ := by
        rw [e]
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv]
        abel
      rw [succ_nsmul, ← add_assoc, e3, e2, ih, ← pow_mul,
        show (n + 1) * (n + 1) = n * n + 2 * n + 1 by ring]
      simp only [pow_add, pow_one]
      ac_rfl
  rw [key, mul_assoc, mul_pow, ← pow_mul, mul_comm (t μ α ^ k)]

end GlobalTheory.IntFam.CoordPow

namespace GlobalTheory.IntFam.CoordPow

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]

theorem val_unit (D : DegPre R) (ξ : Spec (CommRingCat.of (FractionRing R))) {J} (hJc : IntegralCharts D J)
    {Y : Scheme.{0}} {K : Type} [Fintype K] {φ : K → (Y ⟶ D.P.A.left)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb D.P.L φ ε)) (q : Spec (CommRingCat.of R) ⟶ Y)
    (hq : ∀ k, (q ≫ φ k) ≫ D.P.A.hom = 𝟙 _) :
    ∃ u : Rˣ, (val t (jK R ≫ q) ξ J).val = GlobalTheory.PeriodBalance.cst ξ u := by
  refine GlobalTheory.PeriodBalance.unit_gm' ξ q _ (Set.mem_iInter.2 fun k => ?_) _
  have := hJc (q ≫ φ k) (hq k)
  simp only [Category.assoc]
  exact this

end GlobalTheory.IntFam.CoordPow

namespace GlobalTheory.IntFam.CoordPow

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]

theorem pull_unit (D : DegPre R) (ξ : Spec (CommRingCat.of (FractionRing R))) {J} (hJ : Good D.P.L ξ J)
    (hJc : IntegralCharts D J) {Y : Scheme.{0}} {K : Type} [Fintype K] {φ : K → (Y ⟶ D.P.A.left)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb D.P.L φ ε)) (q : Spec (CommRingCat.of R) ⟶ Y)
    (hq : ∀ k, (q ≫ φ k) ≫ D.P.A.hom = 𝟙 _) (h : (TK R).left ⟶ Y) (hh : h = jK R ≫ q) :
    ∃ u : Rˣ, (val (LB.pullGen D.P.L φ ε t h) (𝟙 _) ξ J).val = GlobalTheory.PeriodBalance.cst ξ u := by
  rw [val_pull hJ]
  have e : 𝟙 (TK R).left ≫ h = jK R ≫ q := by rw [hh]; exact Category.id_comp _
  rw [e]
  exact val_unit D ξ hJc t q hq

theorem rig_unit (D : DegPre R) (ξ : Spec (CommRingCat.of (FractionRing R))) {J} (hJ : Good D.P.L ξ J)
    (hJc : IntegralCharts D J) : ∃ u : Rˣ, (val D.rigK (𝟙 _) ξ J).val = GlobalTheory.PeriodBalance.cst ξ u := by
  refine pull_unit D ξ hJ hJc D.rig (𝟙 _) (fun _ => ?_) _ ?_
  · rw [Category.id_comp]
    unfold eSec
    exact Over.w _
  · rw [Over.toUnit_left, Category.comp_id]; rfl

omit [IsLocalRing R] in
theorem cub_hq (D : DegPre R) (a a' b : D.X) (I : thK) :
    ((lift (D.c a) (lift (D.c a') (D.c b))).left ≫ thφ D.P.A (x3 D.P.A) I) ≫ D.P.A.hom = 𝟙 _ := by
  show ((lift (D.c a) (lift (D.c a') (D.c b))).left ≫ (psum D.P.A (x3 D.P.A) I.down).left) ≫ D.P.A.hom = _
  rw [← Over.comp_left, Over.w]; rfl

omit [IsLocalRing R] in
theorem degenerationTriplePoint_eq_lift (D : DegPre R) (a a' b : D.X) :
    D.pt3 a a' b = jK R ≫ (lift (D.c a) (lift (D.c a') (D.c b))).left := by
  simp [DegPre.pt3, ← CartesianMonoidalCategory.comp_lift]

omit [IsLocalRing R] in
open MonObj in
theorem sym_hq (D : DegPre R) (χ : D.X) (k : Fin 2) :
    ((D.c χ).left ≫ (![(ι[D.P.A]).left, 𝟙 D.P.A.left] : Fin 2 → (D.P.A.left ⟶ D.P.A.left)) k) ≫ D.P.A.hom = 𝟙 _ := by
  fin_cases k
  · show ((D.c χ).left ≫ (ι[D.P.A]).left) ≫ D.P.A.hom = _
    rw [← Over.comp_left, Over.w]; rfl
  · show ((D.c χ).left ≫ 𝟙 _) ≫ D.P.A.hom = _
    rw [Category.comp_id, Over.w]; rfl

end GlobalTheory.IntFam.CoordPow

namespace GlobalTheory.IntFam.CoordPow

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R) (D : DegData R I) (k : ℕ)
    (α mu : D.toPre.X) (r s : R), PsiCoord D.toPre α r → PsiCoord D.toPre (α + k • mu) (r * s) →
    ∀ (ξ : Spec (CommRingCat.of (FractionRing R))) (J), Good D.toPre.P.L ξ J → GlobalTheory.IntFam.IntegralCharts D.toPre J →
      ∃ u : Rˣ, (val (GlobalTheory.UU.IntGen.multK D.toPre k mu α) (𝟙 _) ξ J).val ^ k = GlobalTheory.PeriodBalance.cst ξ (u * s) := by
  intro R _ _ _ I D k α mu r s hα hαk ξ J hJ hJc
  let H : Subgroup ((Spec (CommRingCat.of (FractionRing R))).presheaf.stalk ξ)ˣ :=
    (Units.map (GlobalTheory.PeriodBalance.cst ξ).toMonoidHom).range
  have mem : ∀ {g}, (∃ u : Rˣ, g.val = GlobalTheory.PeriodBalance.cst ξ u) → g ∈ H := fun ⟨u, hu⟩ =>
    ⟨u, Units.ext (by rw [Units.coe_map, hu]; rfl)⟩
  let π := QuotientGroup.mk' H
  have π1 : ∀ {g}, (∃ u : Rˣ, g.val = GlobalTheory.PeriodBalance.cst ξ u) → π g = 1 := fun h =>
    (QuotientGroup.eq_one_iff _).2 (mem h)
  let P : D.toPre.X → ((Spec (CommRingCat.of (FractionRing R))).presheaf.stalk ξ)ˣ :=
    fun χ => val (D.toPre.psi χ) (𝟙 _) ξ J
  let T : D.toPre.X → D.toPre.X → ((Spec (CommRingCat.of (FractionRing R))).presheaf.stalk ξ)ˣ :=
    fun a b => val (D.toPre.tau a b) (𝟙 _) ξ J
  let Z : ((Spec (CommRingCat.of (FractionRing R))).presheaf.stalk ξ)ˣ := val D.toPre.rigK (𝟙 _) ξ J
  have hZ : π Z = 1 := π1 (rig_unit D.toPre ξ hJ hJc)
  have law := pow_law (fun χ => π (P χ)) (fun a b => π (T a b))
    (fun a b => by
      show π (T a b) = π (P (a + b)) * (π (P a))⁻¹ * (π (P b))⁻¹
      rw [show T a b = P (a + b) * (P a)⁻¹ * (P b)⁻¹ * Z⁻¹ from GlobalTheory.PeriodBalance.val_tau D.toPre ξ hJ a b,
        map_mul, map_mul, map_mul, map_inv, map_inv, map_inv, hZ, inv_one, mul_one])
    (fun a a' b => by
      have e := (val_mul hJ _ _ _).symm.trans ((val_corr hJ (D.tau_bimult a a' b) (𝟙 _)).trans (val_mul hJ _ _ _))
      have hc := π1 (pull_unit D.toPre ξ hJ hJc D.toPre.cub.t _ (cub_hq D.toPre a a' b) _ (degenerationTriplePoint_eq_lift D.toPre a a' b))
      have e' := congrArg π e
      rw [map_mul, map_mul] at e'
      refine (mul_one _).symm.trans (Eq.trans ?_ e')
      congr 1
      exact hc.symm)
    (fun χ => by
      have e := (val_mul hJ _ _ _).symm.trans (val_corr hJ (D.psi_even χ) (𝟙 _))
      have hc := π1 (pull_unit D.toPre ξ hJ hJc D.toPre.sym _ (sym_hq D.toPre χ) _ (DVR.QForm.ptK_eq D.toPre χ))
      have e' := congrArg π e
      rw [map_mul] at e'
      refine (mul_one _).symm.trans (Eq.trans ?_ e')
      congr 1
      exact hc.symm) k α mu
  set v : ((Spec (CommRingCat.of (FractionRing R))).presheaf.stalk ξ)ˣ :=
    val (GlobalTheory.UU.IntGen.multK D.toPre k mu α) (𝟙 _) ξ J
  have hv : v = P mu ^ k * T mu α * Z ^ k :=
    (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (map_pow _ _ _) rfl))
      (map_pow _ _ _))
  have hq : π (v ^ k * P α * (P (α + k • mu))⁻¹) = 1 := by
    simp only [map_mul, map_inv, map_pow, hv, hZ, one_pow, mul_one]
    rw [law]
    exact mul_inv_eq_one.2 (mul_comm _ _)
  obtain ⟨w, hw⟩ := (QuotientGroup.eq_one_iff _).1 hq
  obtain ⟨u₁, h₁⟩ := GlobalTheory.PeriodBalance.val_psi D.toPre ξ hJ hJc α r hα
  obtain ⟨u₂, h₂⟩ := GlobalTheory.PeriodBalance.val_psi D.toPre ξ hJ hJc (α + k • mu) (r * s) hαk
  have e : v ^ k = Units.map (GlobalTheory.PeriodBalance.cst ξ).toMonoidHom w * P (α + k • mu) * (P α)⁻¹ := by
    rw [hw]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  have hA : ((P α)⁻¹).val * (GlobalTheory.PeriodBalance.cst ξ u₁ * GlobalTheory.PeriodBalance.cst ξ r) = 1 := by
    rw [← map_mul, ← h₁]; exact Units.inv_mul _
  have hu : GlobalTheory.PeriodBalance.cst ξ (u₁⁻¹ : Rˣ) * GlobalTheory.PeriodBalance.cst ξ u₁ = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  refine ⟨w * u₂ * u₁⁻¹, ?_⟩
  rw [← Units.val_pow_eq_pow_val, e, Units.val_mul, Units.val_mul, Units.coe_map, h₂]
  simp only [Units.val_mul, map_mul]
  linear_combination (-(GlobalTheory.PeriodBalance.cst ξ w * GlobalTheory.PeriodBalance.cst ξ u₂ * GlobalTheory.PeriodBalance.cst ξ s *
    GlobalTheory.PeriodBalance.cst ξ r * ((P α)⁻¹).val)) * hu + (GlobalTheory.PeriodBalance.cst ξ w * GlobalTheory.PeriodBalance.cst ξ u₂ *
    GlobalTheory.PeriodBalance.cst ξ s * GlobalTheory.PeriodBalance.cst ξ (u₁⁻¹ : Rˣ)) * hA

end GlobalTheory.IntFam.CoordPow
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RiemannExtensionOfLogGrowthStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open scoped Matrix CategoryTheory.Obj Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.riemann_extension_of_log_growth : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (U : Set V) (φ u : V → ℂ), IsOpen U → DifferentiableOn ℂ φ U → DifferentiableOn ℂ u {b ∈ U | φ b ≠ 0} → U ⊆ closure {b ∈ U | φ b ≠ 0} → (∀ b₀ ∈ U, ∃ (C : ℝ) (k : ℕ), ∀ᶠ b in 𝓝 b₀, φ b ≠ 0 → ‖u b‖ ≤ C * (1 + |Real.log ‖φ b‖|) ^ k) → ∃ u' : V → ℂ, DifferentiableOn ℂ u' U ∧ Set.EqOn u' u {b ∈ U | φ b ≠ 0} := by
  first | exact @GlobalTheory.LogExt.riemann_extension_log | exact GlobalTheory.LogExt.riemann_extension_log | (intros; apply GlobalTheory.LogExt.riemann_extension_log <;> assumption)
end

