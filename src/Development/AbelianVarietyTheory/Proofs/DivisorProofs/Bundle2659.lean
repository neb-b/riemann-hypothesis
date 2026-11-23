module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HolomorphicMapModuliLiftsLocallyToPeriods
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2355
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicLatticeFamilyRetypePeriodType
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2628
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0822
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0069
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2080
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2052
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2619
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0170
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0559
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBoxGenOfSection
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2606
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2536
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValueAtOrigin
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0492
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SectionValueAtTorsionPointEqSumTerms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2609
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicMapLiftsLocallyToPeriodFamilies
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open Filter Topology

namespace GlobalTheory.PELU.LocLiftU

theorem comp_pow_one {X : Scheme.{0}} {G : Over X} [GrpObj G] {T U : Over X} (f : T ⟶ U) (x : U ⟶ G) {n : ℕ}
    (h : x ^ n = 1) : (f ≫ x) ^ n = 1 := by
  have : ∀ k : ℕ, (f ≫ x) ^ k = f ≫ x ^ k := fun k => by
    induction k with
    | zero => simp only [pow_zero, MonObj.comp_one]
    | succ k ih => rw [pow_succ, pow_succ, MonObj.comp_mul, ih]
  rw [this, h, MonObj.comp_one]

end GlobalTheory.PELU.LocLiftU

namespace GlobalTheory.PELU

open LocLiftU


set_option maxHeartbeats 1000000 in
theorem holomorphic_map_lifts_to_periods : ∀ (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (Λ : Type) (F : Fam ℂ O Λ g) (N : ℕ) (D' : PLat O bar) (t : Λ → D'.La) (m : ℕ) (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ F.X)) (b₀ : Fin m → ℂ) P₀ e₀, 0 < N → (∀ a, F.eta a ^ N = 1) → LocallyOfFiniteType F.s → IsOpen B → b₀ ∈ B → (∀ b ∈ B, y b ≫ F.s = spMap (RingHom.id ℂ)) → IsHolTo B y → UnifAt F (RingHom.id ℂ) ρ N D' t P₀ (y b₀) e₀ → ∃ (B' : Set (Fin m → ℂ)) (P : (Fin m → ℂ) → (D'.La →+ (Fin g → ℂ))) (e : ∀ b, (Fin g → ℂ) → (Over.mk (y b) ⟶ F.A)), IsOpen B' ∧ b₀ ∈ B' ∧ B' ⊆ B ∧ P b₀ = P₀ ∧ IsHolPeriods D' ρ B' P ∧ IsHolTo (B' ×ˢ Set.univ) (fun bz : (Fin m → ℂ) × (Fin g → ℂ) => (e bz.1 bz.2).left) ∧ ∀ b ∈ B', UnifAt F (RingHom.id ℂ) ρ N D' t (P b) (y b) (e b) := by
  intro O _ bar g ρ Λ F N D' t m B y b₀ P₀ e₀ hN heta hlft hB hb₀ hyσ hy hU
  obtain ⟨-, hper₀, hexp₀, hker₀, hact₀, hweil₀, heta₀⟩ := hU
  have hab : IsAbelianScheme F.A := F.ab
  haveI := hab.proper
  obtain ⟨B₁, e, r, hB₁, hb₁, hB₁B, rfl, hr, hol, he, hl⟩ :=
    GlobalTheory.RelExp.exists_relative_exp ℂ (RingHom.id ℂ) F.X F.s F.A g m B y b₀ e₀ hlft hab F.dim hB hb₀ hyσ hy hexp₀
  change GlobalTheory.LocLift.HasLifts B₁ y e at hl
  change ∀ b ∈ B₁, GlobalTheory.LocLift.IsExp (y b) (e b) ∧ _ at he
  have hy₁ := GlobalTheory.LocLift.isHolTo_mono hy hB₁ hB₁B
  obtain ⟨P, hP₀, hP⟩ := GlobalTheory.LocLift.exists_periods GlobalTheory.latContinuation hB₁ hb₁ hy₁ hr hol he hl P₀ hper₀.2.1
    hper₀.2.2.2.1 hker₀
  choose L hL1 hL2 using fun a : O =>
    haveI := F.hom a; GlobalTheory.LocLift.exists_hol_linear_lift hB₁ hr hol he hl (F.act a)
  have hL0 : ∀ a, L a b₀ = Matrix.toLin' (ρ a) := fun a =>
    GlobalTheory.LocLift.linear_lift_unique (he b₀ hb₁).1.1 hr (he b₀ hb₁).2 fun z => by
      rw [hL1 a b₀ hb₁, Matrix.toLin'_apply, hact₀]
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 (hP.and (hB₁.mem_nhds hb₁))
  set C := Metric.ball b₀ ε
  have hCo : IsOpen C := Metric.isOpen_ball
  have hCc : IsPreconnected C := (convex_ball b₀ ε).isPreconnected
  have hC₀ : b₀ ∈ C := Metric.mem_ball_self hε
  have hC₁ : C ⊆ B₁ := fun b hb => (hball b hb).2
  have hPd : ∀ x, DifferentiableOn ℂ (fun b => P b x) C := fun x b hb =>
    ((hball b hb).1.1 x).differentiableWithinAt
  have hmv : ∀ {M : (Fin m → ℂ) → Matrix (Fin g) (Fin g) ℂ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
      {W : Set V} {β : V → (Fin m → ℂ)} {v : V → (Fin g → ℂ)}, (∀ i j, DifferentiableOn ℂ (fun w => M (β w) i j) W) →
      DifferentiableOn ℂ v W → DifferentiableOn ℂ (fun w => (M (β w)) *ᵥ (v w)) W := fun hM hv =>
    differentiableOn_pi.2 fun i => by
      simp only [Matrix.mulVec, dotProduct]
      exact DifferentiableOn.fun_sum fun j _ => (hM i j).fun_mul (differentiableOn_pi.1 hv j)
  have hLm : ∀ a i j, DifferentiableOn ℂ (fun b => LinearMap.toMatrix' (L a b) i j) B₁ := fun a i j => by
    simp only [LinearMap.toMatrix'_apply]
    exact differentiableOn_pi.1 (hL2 a (Pi.single j 1)) i
  have hk1 : ∀ b ∈ C, ∀ x, e b (P b x) = 1 := fun b hb x => ((hball b hb).1.2.1 _).2 ⟨x, rfl⟩
  have hlin : ∀ (a : O) x, ∀ b ∈ C, P b (a • x) - L a b (P b x) = 0 := fun a x => by
    haveI := F.hom a
    have hd : ContinuousOn (fun b => P b (a • x) - L a b (P b x)) C := by
      refine ((hPd _).sub ((hmv (M := fun b => LinearMap.toMatrix' (L a b)) (β := id)
        (fun i j => (hLm a i j).mono hC₁) (hPd x)).congr fun b _ => ?_)).continuousOn
      exact (LinearMap.toMatrix'_mulVec (L a b) (P b x)).symm
    refine GlobalTheory.LocLift.eq_zero_of_small hCc hd hr (fun b hb hn => (he b (hC₁ hb)).2 _ hn ?_) hC₀ ?_
    · exact (GlobalTheory.LocLift.hom_sub_eq_one (he b (hC₁ hb)).1.1).2
        (by rw [hL1 a b (hC₁ hb), hk1 b hb, hk1 b hb, MonObj.one_comp])
    · simp only [hP₀, hL0, Matrix.toLin'_apply, hper₀.1, sub_self]
  have htor : ∀ (k : ℕ) x, IsHolTo C (fun b => (e b ((k : ℂ)⁻¹ • P b x)).left) := fun k x =>
    GlobalTheory.LocLift.isHolTo_comp (β := fun b => (b, (k : ℂ)⁻¹ • P b x)) hol hCo
      (differentiableOn_id.prodMk ((hPd x).fun_const_smul _)) fun b hb => ⟨hC₁ hb, trivial⟩
  have hpow : ∀ (k : ℕ), 0 < k → ∀ x, ∀ b ∈ C, e b ((k : ℂ)⁻¹ • P b x) ^ k = 1 := fun k hk x b hb => by
    rw [← GlobalTheory.LocLift.hom_nsmul (he b (hC₁ hb)).1.1, ← Nat.cast_smul_eq_nsmul ℂ,
      smul_inv_smul₀ (Nat.cast_ne_zero.2 hk.ne'), hk1 b hb]
  have hyC : ∀ b ∈ C, y b ≫ F.s = spMap (RingHom.id ℂ) := fun b hb => hyσ b (hB₁B (hC₁ hb))
  have hwe : ∀ b ∈ C, ∀ (k : ℕ) (a a₂ : D'.La) (c : ℂˣ), 0 < k →
      (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a a₂ : ℂ) / k) →
      Out.WeilIs F.A F.L k (e b ((k : ℂ)⁻¹ • P b a)) (e b ((k : ℂ)⁻¹ • P b a₂)) (unitOn c) :=
    fun b hb k a a₂ c hk hc => (_root_.GlobalTheory.torsion_eq_and_weilIs_of_isHolTo_anyLB F.X F.s F.A F.L hlft hab F.isLB m k C y
      (fun b => e b ((k : ℂ)⁻¹ • P b a)) (fun b => e b ((k : ℂ)⁻¹ • P b a₂)) c b₀ hk hCo hCc hC₀ hyC
      (htor k a) (htor k a₂) fun b hb => ⟨hpow k hk a b hb, hpow k hk a₂ b hb⟩).2
      (by simp only [hP₀]; exact hweil₀ k a a₂ c hk hc) b hb
  have heC : ∀ a, ∀ b ∈ C, toUnit _ ≫ F.eta a = e b ((N : ℂ)⁻¹ • P b (t a)) := fun a =>
    (_root_.GlobalTheory.torsion_eq_and_weilIs_of_isHolTo_anyLB F.X F.s F.A F.L hlft hab F.isLB m N C y (fun b => toUnit _ ≫ F.eta a)
      (fun b => e b ((N : ℂ)⁻¹ • P b (t a))) 1 b₀ hN hCo hCc hC₀ hyC
      (GlobalTheory.LocLift.isHolTo_congr (GlobalTheory.LocLift.isHolTo_comp_hom (GlobalTheory.LocLift.isHolTo_mono hy₁ hCo hC₁)
        (F.eta a).left) fun b _ => by rw [Over.comp_left, Over.toUnit_left]; rfl) (htor N (t a))
      fun b hb => ⟨comp_pow_one _ _ (heta a), hpow N hN (t a) b hb⟩).1 (by rw [hP₀]; exact heta₀ a)
  obtain ⟨B₂, h, hB₂, hb₂, hB₂C, hh₀, hhd, hh⟩ := _root_.GlobalTheory.PELU.Retype.retype O bar g ρ D' m C b₀ P hCo hC₀ hPd
    (by rw [hP₀]; exact hper₀) fun b hb => ⟨(hball b hb).1.2.2.2.1, fun a => ⟨LinearMap.toMatrix' (L a b), fun x => by
      rw [LinearMap.toMatrix'_mulVec]; exact sub_eq_zero.1 (hlin a x b hb)⟩⟩
  have hdet : ∀ b ∈ B₂, IsUnit (h b).det := fun b hb => (Matrix.isUnit_iff_isUnit_det _).1 (hh b hb).1
  obtain ⟨P', hP'⟩ := GlobalTheory.LocLift.exists_mulVec_comp h P
  have hinv : ∀ b ∈ B₂, ∀ z, (h b)⁻¹ *ᵥ (h b *ᵥ z) = z := fun b hb z => by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (hdet b hb), Matrix.one_mulVec]
  have hinv' : ∀ b ∈ B₂, ∀ z, h b *ᵥ ((h b)⁻¹ *ᵥ z) = z := fun b hb z => by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (hdet b hb), Matrix.one_mulVec]
  have key : ∀ b ∈ B₂, UnifAt F (RingHom.id ℂ) ρ N D' t (P' b) (y b) (fun z => e b ((h b)⁻¹ *ᵥ z)) := by
    intro b hb
    have hbC := hB₂C hb
    have hb1 := hC₁ hbC
    obtain ⟨j, hj⟩ := GlobalTheory.LocLift.exists_equiv_mulVec (hdet b hb)
    have hjs : ∀ z, (h b)⁻¹ *ᵥ z = j.symm z := fun z => by
      conv_lhs => rw [← j.apply_symm_apply z, ← hj]
      exact hinv b hb _
    have hPj : ∀ x, P' b x = j (P b x) := fun x => by rw [hP', hj]
    have hsm : ∀ (s : ℂ) x, (h b)⁻¹ *ᵥ (s • P' b x) = s • P b x := fun s x => by
      rw [Matrix.mulVec_smul, hP', hinv b hb]
    have hex : IsExp (y b) (fun z => e b ((h b)⁻¹ *ᵥ z)) := by
      have e1 : (fun z => e b ((h b)⁻¹ *ᵥ z)) = fun z => e b (j.symm z) := funext fun z => by rw [hjs]
      rw [e1]
      exact GlobalTheory.LocLift.IsExp.comp (he b hb1).1 j.symm
    have hPinj : Function.Injective (P' b) := fun x x' hx =>
      (hball b hbC).1.2.2.1 (j.injective (by rw [← hPj, ← hPj, hx]))
    have hker : ∀ z, e b ((h b)⁻¹ *ᵥ z) = 1 ↔ z ∈ (P' b).range := fun z => by
      rw [hjs, (hball b hbC).1.2.1]
      constructor
      · rintro ⟨x, hx⟩
        exact ⟨x, by rw [hPj, hx, j.apply_symm_apply]⟩
      · rintro ⟨x, hx⟩
        exact ⟨x, by rw [← hx, hPj, j.symm_apply_apply]⟩
    have hweil' : ∀ (k : ℕ) (a a₂ : D'.La) (c : ℂˣ), 0 < k →
        (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a a₂ : ℂ) / k) →
        Out.WeilIs F.A F.L k (e b ((h b)⁻¹ *ᵥ ((k : ℂ)⁻¹ • P' b a))) (e b ((h b)⁻¹ *ᵥ ((k : ℂ)⁻¹ • P' b a₂)))
          (unitOn c) := fun k a a₂ c hk hc => by
      rw [hsm, hsm]
      exact hwe b hbC k a a₂ c hk hc
    obtain ⟨Hm, EF', h1, h2, h3, h4⟩ :=
      _root_.GlobalTheory.exists_riemannForm_of_relAmple F.X F.A g hab F.dim F.L F.isLB F.ample (y b) _ D'.La (P' b) hex hPinj hker
    have hEF : ∀ x x', EF' x x' = D'.EF x x' := fun x x' => GlobalTheory.LocLift.int_eq_of_exp fun k hk => by
      have := congrArg Units.val (_root_.GlobalTheory.WeilComplexUnique.weilIs_unitOn_unique_complex F.X F.A g hab F.dim F.L F.isLB (y b) k _ _
        (Units.mk0 _ (Complex.exp_ne_zero _)) (Units.mk0 _ (Complex.exp_ne_zero _)) (h4 k x x' _ hk rfl)
        (hweil' k x x' _ hk rfl))
      exact this
    obtain ⟨sp, dc⟩ := GlobalTheory.LocLift.lattice_comp j.symm (P := P b) (P' := P' b)
      (fun x => by rw [hPj, j.symm_apply_apply]) (hball b hbC).1.2.2.2.1 (hball b hbC).1.2.2.2.2
    have hclaim : ∀ (a : O) w, (h b)⁻¹ *ᵥ (ρ a *ᵥ (h b *ᵥ w)) = L a b w := fun a w => by
      have hfg : ((Matrix.toLin' (h b)⁻¹ ∘ₗ Matrix.toLin' (ρ a) ∘ₗ Matrix.toLin' (h b)).restrictScalars ℝ) =
          (L a b).restrictScalars ℝ := LinearMap.ext_on (hball b hbC).1.2.2.2.1 (by
        rintro _ ⟨x, rfl⟩
        simp only [LinearMap.restrictScalars_apply, LinearMap.comp_apply, Matrix.toLin'_apply]
        rw [← (hh b hb).2 a x, hinv b hb]
        exact sub_eq_zero.1 (hlin a x b hbC))
      have := LinearMap.congr_fun hfg w
      simp only [LinearMap.restrictScalars_apply, LinearMap.comp_apply, Matrix.toLin'_apply] at this
      exact this
    refine ⟨hyσ b (hB₁B hb1), ⟨fun a x => ?_, hPinj, dc, sp, Hm, h1, h2, fun x x' => by rw [h3, hEF]⟩,
      hex, hker, fun a z => ?_, hweil', fun a => ?_⟩
    · simp only [hP']
      exact (hh b hb).2 a x
    · haveI := F.hom a
      have := hL1 a b hb1 ((h b)⁻¹ *ᵥ z)
      rw [← hclaim, hinv' b hb] at this
      exact this
    · beta_reduce
      rw [hsm]
      exact heC a b hbC
  refine ⟨B₂, P', fun b z => e b ((h b)⁻¹ *ᵥ z), hB₂, hb₂, hB₂C.trans (hC₁.trans hB₁B), ?_,
    ⟨fun b hb => (key b hb).2.1, fun x => ?_⟩, ?_, key⟩
  · ext1 x
    rw [hP', hh₀, Matrix.one_mulVec, hP₀]
  · exact (hmv (M := h) (β := id) hhd ((hPd x).mono hB₂C)).congr fun b _ => hP' b x
  · have hid : ∀ i j, DifferentiableOn ℂ (fun b => (h b)⁻¹ i j) B₂ :=
      GlobalTheory.RiemannRel.differentiableOn_left_inverse h (fun b => (h b)⁻¹) hhd fun b hb =>
        Matrix.nonsing_inv_mul _ (hdet b hb)
    exact GlobalTheory.LocLift.isHolTo_comp (β := fun bz : (Fin m → ℂ) × (Fin g → ℂ) => (bz.1, (h bz.1)⁻¹ *ᵥ bz.2)) hol
      (hB₂.prod isOpen_univ) (differentiableOn_fst.prodMk (hmv (M := fun b => (h b)⁻¹) (β := Prod.fst)
        (fun i j => (hid i j).comp differentiableOn_fst fun _ hw => hw.1) differentiableOn_snd))
      fun _ hw => ⟨hC₁ (hB₂C hw.1), trivial⟩

end GlobalTheory.PELU
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomogeneousFormCombinationEqZeroIndependent
section
open Filter Topology MvPolynomial GlobalTheory.HSAmp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSAmp.HomInj

theorem aeval_mul_hom {σ R A : Type} [CommRing R] [CommRing A] [Algebra R A] {P : MvPolynomial σ R} {q : ℕ} (hP : P.IsHomogeneous q)
    (c : A) (z : σ → A) : aeval (fun i => c * z i) P = c ^ q * aeval z P := by
  conv_lhs => rw [P.as_sum]
  conv_rhs => rw [P.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hd := hP (mem_support_iff.mp hm)
  simp only [aeval_monomial, mul_pow]
  rw [Finsupp.prod_mul, ← hd]
  have : (m.prod fun _ k => c ^ k) = c ^ (Finsupp.weight 1 m) := by
    simp [Finsupp.prod, Finset.prod_pow_eq_pow_sum, Finsupp.weight_apply, Finsupp.sum]
  rw [this]; ring

def dehom (D : ℕ) : MvPolynomial (Fin (D + 1)) ℤ →ₐ[ℤ] MvPolynomial (Fin D) ℤ :=
  aeval (Fin.cons 1 X)

theorem aeval_dehom {A : Type} [CommRing A] [Algebra ℤ A] {D : ℕ} (w : Fin D → A) (P : MvPolynomial (Fin (D + 1)) ℤ) :
    aeval w (dehom D P) = aeval (Fin.cons 1 w : Fin (D + 1) → A) P := by
  rw [dehom, ← AlgHom.comp_apply, comp_aeval]
  congr 2
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp

theorem dehom_eq_zero {D q : ℕ} {P : MvPolynomial (Fin (D + 1)) ℤ} (hP : P.IsHomogeneous q)
    (h : dehom D P = 0) : P = 0 := by
  let R := MvPolynomial (Fin (D + 1)) ℤ
  let F := FractionRing R
  have hinj : Function.Injective (algebraMap R F) := IsFractionRing.injective R F
  set c : F := algebraMap R F (X 0) with hc
  have hc0 : c ≠ 0 := by
    rw [hc, Ne, ← map_zero (algebraMap R F)]
    exact fun e => X_ne_zero (R := ℤ) (0 : Fin (D + 1)) (hinj e)
  let z : Fin (D + 1) → F := fun i => algebraMap R F (X i) / c
  have hz : (fun i => algebraMap R F (X i)) = fun i => c * z i := by
    funext i; exact (mul_div_cancel₀ _ hc0).symm
  have hz0 : z = Fin.cons 1 (fun j => z j.succ) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · show algebraMap R F (X 0) / c = 1
      exact div_self hc0
    · simp
  have key : algebraMap R F P = c ^ q * aeval z P := by
    have e1 : algebraMap R F P = aeval (fun i => algebraMap R F (X i)) P := by
      rw [← Function.comp_def (algebraMap R F) X, aeval_algebraMap_apply, aeval_X_left_apply]
    rw [e1, hz]
    exact aeval_mul_hom hP c z
  have hzP : aeval z P = 0 := by
    have e2 := aeval_dehom (fun j => z j.succ) P
    rw [h, map_zero] at e2
    rw [hz0]; exact e2.symm
  apply hinj
  rw [key, hzP, mul_zero, map_zero]

end GlobalTheory.HSAmp.HomInj

namespace GlobalTheory.HSAmp


open GlobalTheory.HSAmp.HomInj in
theorem homogComb_eq_zero : ∀ (K : Type) [Field K] [CharZero K] (D : ℕ) (x : Fin (D + 1) → K), (∀ j, x j ≠ 0) →
    AlgebraicIndependent ℤ (fun j : Fin D => x j.succ / x 0) → FiniteDimensional (ratF x) K →
    ∀ (ι : Type) [Fintype ι] (g : ι → K), LinearIndependent (ratF x) g → ∀ (q : ℕ)
    (T : ι → MvPolynomial (Fin (D + 1)) ℤ), (∀ i, (T i).IsHomogeneous q) → ∑ i, aeval x (T i) * g i = 0 → T = 0 := by
  intro K _ _ D x hx hind _ ι _ g hg q T hT hsum
  let y : Fin (D + 1) → K := fun j => x j / x 0
  have hy : ∀ j, y j ∈ ratF x := by
    intro j
    refine Fin.cases ?_ (fun j => ?_) j
    · simp only [y, div_self (hx 0)]; exact (ratF x).one_mem
    · exact Subfield.subset_closure ⟨j, rfl⟩
  let y' : Fin (D + 1) → ratF x := fun j => ⟨y j, hy j⟩
  have hxy : x = fun j => x 0 * y j := by
    funext j; exact (mul_div_cancel₀ _ (hx 0)).symm
  have hval : ∀ i, aeval y (T i) = ((aeval y' (T i) : ratF x) : K) := by
    intro i
    show _ = algebraMap (ratF x) K _
    rw [← aeval_algebraMap_apply]
    rfl
  have h1 : ∀ i, aeval x (T i) = x 0 ^ q * aeval y (T i) := by
    intro i
    rw [← aeval_mul_hom (hT i) (x 0) y]
    exact congrArg (fun v => aeval v (T i)) hxy
  have hsum' : ∑ i, aeval y' (T i) • g i = 0 := by
    have hq : x 0 ^ q ≠ 0 := pow_ne_zero _ (hx 0)
    have : x 0 ^ q * ∑ i, aeval y' (T i) • g i = 0 := by
      rw [Finset.mul_sum, ← hsum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [h1, hval, Subfield.smul_def, smul_eq_mul]; ring
    exact (mul_eq_zero.mp this).resolve_left hq
  have h0 : ∀ i, aeval y (T i) = 0 := by
    intro i
    rw [hval, Fintype.linearIndependent_iff.1 hg _ hsum' i]; rfl
  have hy0 : y = Fin.cons 1 (fun j : Fin D => x j.succ / x 0) := by
    funext j
    refine Fin.cases ?_ (fun j => ?_) j
    · simp [y, div_self (hx 0)]
    · simp [y]
  funext i
  apply dehom_eq_zero (hT i)
  apply (algebraicIndependent_iff_injective_aeval.1 hind)
  rw [aeval_dehom, ← hy0, h0, map_zero]

end GlobalTheory.HSAmp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealSheafAlongLocalSpecNormalisedBlowupPrincipa
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.NormBlPrincipal

theorem idlAlong_comap_principal : ∀ {S Z : Scheme.{0}} (π : S ⟶ Z) (J : Z.IdealSheafData), IsNormBl π J →
    ∀ (R : Type) [CommRing R] [IsLocalRing R]
    (ξ : Sp R ⟶ S), ∃ g₀ : R, idlAlong (J.comap π) ξ = Ideal.span {g₀} := by
  intro S Z π J h R _ _ ξ
  obtain ⟨-, S₀, π₀, ν, -, hbl, hc, -⟩ := h
  obtain ⟨U, f, hx, -, hU⟩ := hbl.1 ((ξ ≫ ν) (closedPoint R))
  have hle : ⊤ ≤ (ξ ≫ ν) ⁻¹ᵁ U.1 := (Scheme.preimage_eq_top_of_closedPoint_mem (ξ ≫ ν) hx).ge
  refine ⟨((ξ ≫ ν).appLE U.1 ⊤ hle ≫ (Scheme.ΓSpecIso (.of R)).hom).hom f, ?_⟩
  have e : idlAlong (J.comap π) ξ = idlAlong (J.comap π₀) (ξ ≫ ν) := by
    rw [GlobalTheory.PullAlong.idlAlong_comap_eq, GlobalTheory.PullAlong.idlAlong_comap_eq, ← hc, Category.assoc]
  have hmap : idlAlong (J.comap π₀) (ξ ≫ ν) =
      ((J.comap π₀).ideal U).map
        ((ξ ≫ ν).appLE U.1 ⊤ hle ≫ (Scheme.ΓSpecIso (.of R)).hom).hom := by
    unfold idlAlong
    rw [ds_stalkId_eq_map (J.comap π₀) U _ hx, Ideal.map_map,
      ← CommRingCat.hom_comp, Scheme.germ_stalkClosedPointTo]
    congr 2
  rw [e, hmap, hU, Ideal.map_span, Set.image_singleton]

end GlobalTheory.NormBlPrincipal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsLastLast
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd GlobalTheory.ProdUnif

namespace GlobalTheory.ProdUnif

theorem even_box₂ : ∀ {B B₁ B₂ G G₁ G₂ T T₁ T₂ : Scheme.{0}} {M : LB B} {M₁ : LB B₁} {M₂ : LB B₂} {L : LB G} {L₁ : LB G₁} {L₂ : LB G₂} {b₁ : B ⟶ B₁} {b₂ : B ⟶ B₂} {g₁ : G ⟶ G₁} {g₂ : G ⟶ G₂} {p : T ⟶ B} {f : T ⟶ G} {p₁ : T₁ ⟶ B₁} {f₁ : T₁ ⟶ G₁} {p₂ : T₂ ⟶ B₂} {f₂ : T₂ ⟶ G₂} {h₁ : T ⟶ T₁} {h₂ : T ⟶ T₂} (wM : LB.Iso M (extLB M₁ M₂ b₁ b₂)) (wL : LB.Iso L (extLB L₁ L₂ g₁ g₂)) (we₁ : LB.Iso (L₁.pull f₁) (M₁.pull p₁)) (we₂ : LB.Iso (L₂.pull f₂) (M₂.pull p₂)), M.IsLB → M₁.IsLB → M₂.IsLB → L.IsLB → L₁.IsLB → L₂.IsLB → p ≫ b₁ = h₁ ≫ p₁ → p ≫ b₂ = h₂ ≫ p₂ → f ≫ g₁ = h₁ ≫ f₁ → f ≫ g₂ = h₂ ≫ f₂ → ∀ (we : LB.Iso (L.pull f) (M.pull p)), BoxSq wM wL we we₁ we₂ h₁ h₂ → ∀ (iT : T ⟶ T) (iT₁ : T₁ ⟶ T₁) (iT₂ : T₂ ⟶ T₂) {iG : G ⟶ G} {iG₁ : G₁ ⟶ G₁} {iG₂ : G₂ ⟶ G₂} {iB : B ⟶ B} {iB₁ : B₁ ⟶ B₁} {iB₂ : B₂ ⟶ B₂} (s : LB.Gen (LB.LinComb L (K := Fin 2) ![iG, 𝟙 G] ![1, -1])) (s₁ : LB.Gen (LB.LinComb L₁ (K := Fin 2) ![iG₁, 𝟙 G₁] ![1, -1])) (s₂ : LB.Gen (LB.LinComb L₂ (K := Fin 2) ![iG₂, 𝟙 G₂] ![1, -1])) (σ : LB.Gen (LB.LinComb M (K := Fin 2) ![iB, 𝟙 B] ![1, -1])) (σ₁ : LB.Gen (LB.LinComb M₁ (K := Fin 2) ![iB₁, 𝟙 B₁] ![1, -1])) (σ₂ : LB.Gen (LB.LinComb M₂ (K := Fin 2) ![iB₂, 𝟙 B₂] ![1, -1])), iT ≫ h₁ = h₁ ≫ iT₁ → iT ≫ h₂ = h₂ ≫ iT₂ → iT ≫ f = f ≫ iG → iT ≫ p = p ≫ iB → iT₁ ≫ f₁ = f₁ ≫ iG₁ → iT₁ ≫ p₁ = p₁ ≫ iB₁ → iT₂ ≫ f₂ = f₂ ≫ iG₂ → iT₂ ≫ p₂ = p₂ ≫ iB₂ → IsBoxGen wL g₁ g₂ s s₁ s₂ → IsBoxGen wM b₁ b₂ σ σ₁ σ₂ → GlobalTheory.PowUnif.EvenAlong we₁ iT₁ s₁ σ₁ → GlobalTheory.PowUnif.EvenAlong we₂ iT₂ s₂ σ₂ → GlobalTheory.PowUnif.EvenAlong we iT s σ := by
  intro B B₁ B₂ G G₁ G₂ T T₁ T₂ M M₁ M₂ L L₁ L₂ b₁ b₂ g₁ g₂ p f p₁ f₁ p₂ f₂ h₁ h₂ wM wL we₁ we₂
    hM hM₁ hM₂ hL hL₁ hL₂ e₁ e₂ e₃ e₄ we Q iT iT₁ iT₂ iG iG₁ iG₂ iB iB₁ iB₂ s s₁ s₂ σ σ₁ σ₂
    ih₁ ih₂ iF iP iF₁ iP₁ iF₂ iP₂ Hs Hσ ev₁ ev₂
  intro jS jT cS cT V k₁ k₂ k₃ k₄
  refine unit_ext fun z hz => ?_
  obtain ⟨n₁, n₂⟩ := GlobalTheory.EvenPull.even_stalk we s σ jS jT V k₁ k₂ k₃ k₄ (𝟙 T) z hz
  refine n₁.trans (Eq.trans ?_ n₂.symm)
  clear n₁ n₂
  obtain ⟨J, hJ, hJj⟩ := exists_good M hM z (fun k => p ≫ (![iB, 𝟙 B] : Fin 2 → _) k) jT cT
    (fun k => Set.mem_iInter.1 (k₁ hz) k)
  obtain ⟨N, hN, hNj⟩ := exists_good L hL z (fun k => f ≫ (![iG, 𝟙 G] : Fin 2 → _) k) jS cS
    (fun k => Set.mem_iInter.1 (k₄ hz) k)
  obtain ⟨J₁, hJ₁⟩ := GlobalTheory.BoxFamily.exists_good_at hM₁ z
  obtain ⟨J₂, hJ₂⟩ := GlobalTheory.BoxFamily.exists_good_at hM₂ z
  obtain ⟨N₁, hN₁⟩ := GlobalTheory.BoxFamily.exists_good_at hL₁ z
  obtain ⟨N₂, hN₂⟩ := GlobalTheory.BoxFamily.exists_good_at hL₂ z

  have hb₁ : (p ≫ iB) ≫ b₁ = (h₁ ≫ p₁) ≫ iB₁ := by
    rw [← iP, Category.assoc, e₁, ← Category.assoc, ih₁, Category.assoc, iP₁, Category.assoc]
  have hb₂ : (p ≫ iB) ≫ b₂ = (h₂ ≫ p₂) ≫ iB₂ := by
    rw [← iP, Category.assoc, e₂, ← Category.assoc, ih₂, Category.assoc, iP₂, Category.assoc]
  have hg₁ : (f ≫ iG) ≫ g₁ = (h₁ ≫ f₁) ≫ iG₁ := by
    rw [← iF, Category.assoc, e₃, ← Category.assoc, ih₁, Category.assoc, iF₁, Category.assoc]
  have hg₂ : (f ≫ iG) ≫ g₂ = (h₂ ≫ f₂) ≫ iG₂ := by
    rw [← iF, Category.assoc, e₄, ← Category.assoc, ih₂, Category.assoc, iF₂, Category.assoc]
  have QQ : ∀ k, om wM z J₁ J₂ J (p ≫ (![iB, 𝟙 B] : Fin 2 → _) k) *
        gw we ((![iT, 𝟙 T] : Fin 2 → _) k) z (J (p ≫ (![iB, 𝟙 B] : Fin 2 → _) k))
          (fun _ => N (f ≫ (![iG, 𝟙 G] : Fin 2 → _) k)) =
      gw we₁ ((![h₁ ≫ iT₁, h₁] : Fin 2 → _) k) z (J₁ ((h₁ ≫ p₁) ≫ (![iB₁, 𝟙 B₁] : Fin 2 → _) k))
          (fun _ => N₁ ((h₁ ≫ f₁) ≫ (![iG₁, 𝟙 G₁] : Fin 2 → _) k)) *
        gw we₂ ((![h₂ ≫ iT₂, h₂] : Fin 2 → _) k) z (J₂ ((h₂ ≫ p₂) ≫ (![iB₂, 𝟙 B₂] : Fin 2 → _) k))
          (fun _ => N₂ ((h₂ ≫ f₂) ≫ (![iG₂, 𝟙 G₂] : Fin 2 → _) k)) *
        om wL z N₁ N₂ N (f ≫ (![iG, 𝟙 G] : Fin 2 → _) k) := by
    refine Fin.forall_fin_two.2 ⟨?_, ?_⟩
    · have q := Q T iT z J₁ J₂ J N₁ N₂ N hJ₁ hJ₂ hJ hN₁ hN₂ hN
      rw [iP, iF, ih₁, ih₂, hb₁, hb₂, hg₁, hg₂] at q
      simpa only [Matrix.cons_val_zero] using q
    · have q := Q T (𝟙 T) z J₁ J₂ J N₁ N₂ N hJ₁ hJ₂ hJ hN₁ hN₂ hN
      simp only [Category.id_comp] at q
      rw [e₁, e₂, e₃, e₄] at q
      simpa only [Matrix.cons_val_one, Matrix.cons_val_zero, Category.comp_id] using q
  have HM := Hσ T p z J₁ J₂ J hJ₁ hJ₂ hJ
  rw [e₁, e₂] at HM
  have HL := Hs T f z N₁ N₂ N hN₁ hN₂ hN
  rw [e₃, e₄] at HL
  have H₁ : val σ₁ (h₁ ≫ p₁) z J₁ = (∏ k, gw we₁ ((![h₁ ≫ iT₁, h₁] : Fin 2 → _) k) z
      (J₁ ((h₁ ≫ p₁) ≫ (![iB₁, 𝟙 B₁] : Fin 2 → _) k))
      (fun _ => N₁ ((h₁ ≫ f₁) ≫ (![iG₁, 𝟙 G₁] : Fin 2 → _) k)) ^ (![1, -1] : Fin 2 → ℤ) k) *
      val s₁ (h₁ ≫ f₁) z N₁ :=
    ev₁.stalk iF₁ iP₁ h₁ z _ _
      (fun a b e => congrArg N₁ ((Category.assoc _ _ _).trans ((congrArg (h₁ ≫ ·) e).trans
        (Category.assoc _ _ _).symm)))
      (fun a b e => congrArg J₁ ((Category.assoc _ _ _).trans ((congrArg (h₁ ≫ ·) e).trans
        (Category.assoc _ _ _).symm)))
      (fun k => hN₁ ((h₁ ≫ f₁) ≫ (![iG₁, 𝟙 G₁] : Fin 2 → _) k))
      (fun k => hJ₁ ((h₁ ≫ p₁) ≫ (![iB₁, 𝟙 B₁] : Fin 2 → _) k))
  have H₂ : val σ₂ (h₂ ≫ p₂) z J₂ = (∏ k, gw we₂ ((![h₂ ≫ iT₂, h₂] : Fin 2 → _) k) z
      (J₂ ((h₂ ≫ p₂) ≫ (![iB₂, 𝟙 B₂] : Fin 2 → _) k))
      (fun _ => N₂ ((h₂ ≫ f₂) ≫ (![iG₂, 𝟙 G₂] : Fin 2 → _) k)) ^ (![1, -1] : Fin 2 → ℤ) k) *
      val s₂ (h₂ ≫ f₂) z N₂ :=
    ev₂.stalk iF₂ iP₂ h₂ z _ _
      (fun a b e => congrArg N₂ ((Category.assoc _ _ _).trans ((congrArg (h₂ ≫ ·) e).trans
        (Category.assoc _ _ _).symm)))
      (fun a b e => congrArg J₂ ((Category.assoc _ _ _).trans ((congrArg (h₂ ≫ ·) e).trans
        (Category.assoc _ _ _).symm)))
      (fun k => hN₂ ((h₂ ≫ f₂) ≫ (![iG₂, 𝟙 G₂] : Fin 2 → _) k))
      (fun k => hJ₂ ((h₂ ≫ p₂) ≫ (![iB₂, 𝟙 B₂] : Fin 2 → _) k))
  have R := rel_alg (![1, -1] : Fin 2 → ℤ) _ _ _ _ _ QQ HM HL H₁ H₂
  rw [val_of σ p z J jT hJj, val_of s f z N jS hNj, Fin.prod_univ_two] at R
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, zpow_one, zpow_neg] at R
  have a₀ : J (p ≫ iB) = jT 0 := hJj 0
  have a₁ : J (p ≫ 𝟙 B) = jT 1 := hJj 1
  have c₀ : N (f ≫ iG) = jS 0 := hNj 0
  have c₁ : N (f ≫ 𝟙 G) = jS 1 := hNj 1
  rw [a₀, a₁, c₀, c₁] at R
  simp only [Category.id_comp]
  rw [R, mul_right_comm, inv_mul_cancel_right]

end GlobalTheory.ProdUnif
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralCombinationTermsRationalPointFrameStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_combination_terms_rational_point_frame : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (g : GtPt D (𝟙_ (Over (Sp R)))) (g' : GtPtF D (FractionRing R)), GtPt.IsPullF (FractionRing R) (toUnit (TF (R := R) (FractionRing R))).left g g' → ∀ (t : LB.Gen (LB.LinComb D.P.L ![(η[D.P.A]).left, g.b.left] (DegPre.lineε 1))) (l : FractionRing R), l ≠ 0 → ∀ (k : ℕ) (wk : Frm D (FractionRing R) k g'.b), wk.IsGen → (∀ (z : (TF (R := R) (FractionRing R)).left) (J : ((TF (R := R) (FractionRing R)).left ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J → GlobalTheory.UT.cst (FractionRing R) z (l ^ k) * (val wk (𝟙 _) z J).val = (val t (toUnit (TF (R := R) (FractionRing R))).left z J ^ k).val) → ∀ (s : Fam D (FractionRing R) k) (n : ℕ) (c : Fin n → FractionRing R) (fs : Fin n → ∀ α : D.X, D.SecB k α), (∀ α : D.X, GeneratorPullback.SecLin D.P.L (DegPre.famφ D (FractionRing R) α) (DegPre.famε k) (s.s α) (D.famφB α) (DegPre.famε k) (fun i => fs i α) (DegPre.prB D (FractionRing R)).left (fun i => scal (fst (TF (R := R) (FractionRing R)) D.P.A).left (c i))) → ∀ a : Fin n → D.X → R, (∀ (i : Fin n) (α : D.X) (Z : Scheme.{0}) (r : Z ⟶ Sp R) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J → sval (fs i α) (r ≫ g.b.left) z J * (val (g.s α) r z J).val * (val t r z J ^ k).val = Geo.Tor.cst r z (a i α) * (val (L := D.P.L) D.rig r z J ^ k).val) → ∀ α : D.X, l ^ k * coef s g' wk α = ∑ i, c i * algebraMap R (FractionRing R) (a i α) := by
  first | exact @GlobalTheory.Poinc.IntEval.coef_comb_pull | exact GlobalTheory.Poinc.IntEval.coef_comb_pull | (intros; apply GlobalTheory.Poinc.IntEval.coef_comb_pull <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftBaseChangePadicIntInjectiveSaturatedOfModLStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftBaseChange_padicInt_injective_saturated_of_modL : ∀ (l : ℕ) [Fact l.Prime] (H T : Type) [AddCommGroup H] [Module.Finite ℤ H] [Module.Free ℤ H] [AddCommGroup T] [Module ℤ_[l] T], (∀ t : T, (l : ℤ_[l]) • t = 0 → t = 0) → ∀ φ : H →+ T, (∀ (h : H) (t : T), φ h = (l : ℤ_[l]) • t → ∃ h' : H, h = l • h') → Function.Injective (φ.toIntLinearMap.liftBaseChange ℤ_[l]) ∧ ∀ t : T, (l : ℤ_[l]) • t ∈ LinearMap.range (φ.toIntLinearMap.liftBaseChange ℤ_[l]) → t ∈ LinearMap.range (φ.toIntLinearMap.liftBaseChange ℤ_[l]) := by
  first | (exact @GlobalTheory.latticeMap_liftBaseChange_injective_saturated) | (exact GlobalTheory.latticeMap_liftBaseChange_injective_saturated) | (intros; apply GlobalTheory.latticeMap_liftBaseChange_injective_saturated  <;> assumption)
end

