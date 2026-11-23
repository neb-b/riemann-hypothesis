module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0643
public import ReciprocityTheory.L2DbarEstimates.Imports
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.MemAnalyticAtZeroOfEventuallyDifferentiableAt
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioCover
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0018
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0618
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0631
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FinrankOfIsStandardSmoothOfRelativeDimension
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0638
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0016

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEtaleCoordinatesSectionQuotientsStatement
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isEtaleCoordinates_section_quotients : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (B : La) (t0 : ι → Y → ℂ) (t : Fin n → ι → Y → ℂ) (U : Set Y), A.IsSec B t0 → (∀ j, A.IsSec B (t j)) → IsOpen U → (∀ y ∈ U, t0 (A.pick y) y ≠ 0 ∧ A.IsCoordAt t0 t y) → Etale A U (A.zmap t0 t) := by
  first | exact @GlobalTheory.OTY.etale_zmap_main | exact GlobalTheory.OTY.etale_zmap_main | (intros; apply GlobalTheory.OTY.etale_zmap_main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNilpotentOfComap
section
open Filter Topology

namespace GlobalTheory
namespace SquareZeroSum

open TrivSqZeroExt

theorem isNilpotent_comap {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (I : Ideal B)
    (hI : IsNilpotent I) (hf : ∀ x y, f x = 0 → f y = 0 → x * y = 0) :
    IsNilpotent (I.comap f) := by
  obtain ⟨m, hm⟩ := hI
  have h1 : (I.comap f) ^ m ≤ RingHom.ker f := by
    have := Ideal.le_comap_pow f (K := I) m
    rw [hm] at this
    exact this
  refine ⟨m + m, ?_⟩
  rw [pow_add, Ideal.zero_eq_bot, eq_bot_iff, Ideal.mul_le]
  intro r hr s hs
  exact (Submodule.mem_bot _).2 (hf r s (h1 hr) (h1 hs))

theorem isNilpotent_of_comap {A B : Type} [CommRing A] [CommRing B] (f : A →+* B)
    (hf : Function.Surjective f) (I : Ideal B) (hI : IsNilpotent (I.comap f)) :
    IsNilpotent I := by
  obtain ⟨m, hm⟩ := hI
  refine ⟨m, ?_⟩
  rw [← Ideal.map_comap_of_surjective f hf I, ← Ideal.map_pow, hm]
  simp

section
variable {K : Type} [Fintype K] [DecidableEq K] {D : Type} [CommRing D] (δ : K → D)

theorem prod_fst_snd {ι : Type} [DecidableEq ι] (s : ι → K) (t : Finset ι) :
    (∏ a ∈ t, ((inl (δ (s a)) : TrivSqZeroExt D (K → D)) - inr (Pi.single (s a) 1))).fst
        = ∏ a ∈ t, δ (s a) ∧
      ∑ k, (∏ a ∈ t, ((inl (δ (s a)) : TrivSqZeroExt D (K → D))
          - inr (Pi.single (s a) 1))).snd k * δ k = -(t.card : D) * ∏ a ∈ t, δ (s a) := by
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
    obtain ⟨h1, h2⟩ := ih
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.card_insert_of_notMem ha]
    generalize (∏ a ∈ t, ((inl (δ (s a)) : TrivSqZeroExt D (K → D))
      - inr (Pi.single (s a) 1))) = P at h1 h2 ⊢
    refine ⟨by simp [h1], ?_⟩
    have h3 : ∀ k, ((((inl (δ (s a)) : TrivSqZeroExt D (K → D))
        - inr (Pi.single (s a) 1))) * P).snd k * δ k
        = δ (s a) * (P.snd k * δ k) - P.fst * ((Pi.single (s a) 1 : K → D) k * δ k) := by
      intro k
      simp [snd_mul]
      ring
    simp only [h3, Finset.sum_sub_distrib, ← Finset.mul_sum, h2, h1]
    simp [Pi.single_apply]
    ring

end

theorem step (N : ℕ) {K : Type} [Fintype K] (D : Type) [CommRing D] [Algebra ℂ D]
    (π : D →ₐ[ℂ] ℂ) (δ : K → D) (hπ : IsNilpotent (RingHom.ker π)) (hδ : ∀ a, π (δ a) = 0)
    (hs : ∀ s : Fin (N + 1 + 1) → K, ∏ a, δ (s a) = 0) :
    ∃ (D' : Type) (_ : CommRing D') (_ : Algebra ℂ D') (ι : D →ₐ[ℂ] D') (π' : D' →ₐ[ℂ] ℂ)
      (ν : K → D'), Function.Injective ι ∧ (∀ d, π' (ι d) = π d) ∧
      IsNilpotent (RingHom.ker π') ∧ (∀ a, π' (ν a) = 0) ∧ (∀ a b, ν a * ν b = 0) ∧
      ∀ s : Fin (N + 1) → K, ∏ a, (ι (δ (s a)) - ν (s a)) = 0 := by
  classical
  let g : (Fin (N + 1) → K) → TrivSqZeroExt D (K → D) := fun s =>
    ∏ a, ((inl (δ (s a)) : TrivSqZeroExt D (K → D)) - inr (Pi.single (s a) 1))
  let Q : Ideal (TrivSqZeroExt D (K → D)) := Ideal.span (Set.range g)
  let E : TrivSqZeroExt D (K → D) → D := fun x => ((N + 1 : ℕ) : D) * x.fst + ∑ k, x.snd k * δ k
  have hEadd : ∀ x y, E (x + y) = E x + E y := by
    intro x y
    simp only [E, fst_add, snd_add, Pi.add_apply, add_mul, Finset.sum_add_distrib]
    ring
  have hg : ∀ s c, E (c * g s) = 0 := by
    intro s c
    obtain ⟨h1, h2⟩ := prod_fst_snd δ s Finset.univ
    change (g s).fst = _ at h1
    change ∑ k, (g s).snd k * δ k = _ at h2
    have h3 : ∀ k, (c * g s).snd k * δ k
        = c.fst * ((g s).snd k * δ k) + c.snd k * (δ k * ∏ a, δ (s a)) := by
      intro k
      simp [snd_mul, h1]
      ring
    have h4 : ∀ k, δ k * ∏ a, δ (s a) = 0 := by
      intro k
      have := hs (Fin.cons k s)
      rw [Fin.prod_univ_succ] at this
      simpa using this
    simp only [E, h3, h4, mul_zero, add_zero, ← Finset.mul_sum, h2, fst_mul, h1,
      Finset.card_univ, Fintype.card_fin]
    ring
  have hQ : ∀ x ∈ Q, ∀ c, E (c * x) = 0 := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => obtain ⟨s, rfl⟩ := hx; exact hg s
    | zero => intro c; simp [E]
    | add x y _ _ hx hy => intro c; rw [mul_add, hEadd, hx, hy, add_zero]
    | smul a x _ hx => intro c; rw [smul_eq_mul, ← mul_assoc]; exact hx _
  let p : TrivSqZeroExt D (K → D) →ₐ[ℂ] ℂ := π.comp (fstHom ℂ D (K → D))
  have hp : ∀ x ∈ Q, p x = 0 := by
    have : Q ≤ RingHom.ker p := by
      rw [Ideal.span_le]
      rintro _ ⟨s, rfl⟩
      have h1 : (g s).fst = _ := (prod_fst_snd δ s Finset.univ).1
      simp [p, h1, hδ, map_prod]
    exact this
  refine ⟨TrivSqZeroExt D (K → D) ⧸ Q, inferInstance, inferInstance,
    (Ideal.Quotient.mkₐ ℂ Q).comp (inlAlgHom ℂ D (K → D)), Ideal.Quotient.liftₐ Q p hp,
    fun a => Ideal.Quotient.mk Q (inr (Pi.single a 1)), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro d hd
    have hd' : (inl d : TrivSqZeroExt D (K → D)) ∈ Q := Ideal.Quotient.eq_zero_iff_mem.1 hd
    have h := hQ _ hd' 1
    simp only [E, one_mul, fst_inl, snd_inl, Pi.zero_apply, zero_mul, Finset.sum_const_zero,
      add_zero] at h
    have hu : IsUnit ((N + 1 : ℕ) : D) := by
      rw [← map_natCast (algebraMap ℂ D)]
      exact (IsUnit.mk0 _ (Nat.cast_ne_zero.2 (Nat.succ_ne_zero N))).map _
    exact hu.mul_right_eq_zero.1 h
  · intro d
    rfl
  · refine isNilpotent_of_comap (Ideal.Quotient.mk Q) Ideal.Quotient.mk_surjective _ ?_
    have := isNilpotent_comap (fstHom ℂ D (K → D)).toRingHom _ hπ (by
      intro x y hx hy
      have hx' : x.fst = 0 := hx
      have hy' : y.fst = 0 := hy
      ext1 <;> simp [snd_mul, hx', hy'])
    exact this
  · intro a
    change p (inr _) = 0
    simp [p]
  · intro a b
    rw [← map_mul, inr_mul_inr, map_zero]
  · intro s
    have : Ideal.Quotient.mk Q (g s) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨s, rfl⟩)
    rw [← this]
    simp only [g, map_prod, map_sub]
    rfl

theorem exists_sum_sq_zero : ∀ (N : ℕ) {K : Type} [Fintype K] (D : Type) [CommRing D] [Algebra ℂ D] (π : D →ₐ[ℂ] ℂ) (δ : K → D), IsNilpotent (RingHom.ker π) → (∀ a, π (δ a) = 0) → (∀ s : Fin (N + 1) → K, ∏ a, δ (s a) = 0) → ∃ (D' : Type) (_ : CommRing D') (_ : Algebra ℂ D') (ι : D →ₐ[ℂ] D') (π' : D' →ₐ[ℂ] ℂ) (n : Fin N → K → D'), Function.Injective ι ∧ (∀ d, π' (ι d) = π d) ∧ IsNilpotent (RingHom.ker π') ∧ (∀ j a, π' (n j a) = 0) ∧ (∀ j a b, n j a * n j b = 0) ∧ ∀ a, ι (δ a) = ∑ j, n j a := by
  intro N
  induction N with
  | zero =>
    intro K _ D _ _ π δ hπ hδ hs
    refine ⟨D, inferInstance, inferInstance, AlgHom.id ℂ D, π, fun j => j.elim0,
      Function.injective_id, fun _ => rfl, hπ, fun j => j.elim0, fun j => j.elim0, ?_⟩
    intro a
    simpa using hs (fun _ => a)
  | succ N ih =>
    intro K _ D _ _ π δ hπ hδ hs
    obtain ⟨D₁, _, _, ι₁, π₁, ν, hi₁, hc₁, hn₁, hν, hνν, hs₁⟩ := step N D π δ hπ hδ hs
    obtain ⟨D₂, _, _, ι₂, π₂, n, hi₂, hc₂, hn₂, hn, hnn, hsum⟩ :=
      ih D₁ π₁ (fun a => ι₁ (δ a) - ν a) hn₁ (fun a => by simp [hc₁, hδ, hν]) hs₁
    refine ⟨D₂, inferInstance, inferInstance, ι₂.comp ι₁, π₂,
      Fin.cons (fun a => ι₂ (ν a)) n, hi₂.comp hi₁, fun d => by simp [hc₂, hc₁], hn₂, ?_, ?_, ?_⟩
    · intro j
      refine Fin.cases (fun a => ?_) (fun j a => ?_) j
      · simp [hc₂, hν]
      · simp [hn]
    · intro j
      refine Fin.cases (fun a b => ?_) (fun j a b => ?_) j
      · simp [← map_mul, hνν]
      · simp [hnn]
    · intro a
      rw [Fin.sum_univ_succ]
      simp [← hsum]

end SquareZeroSum
end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegularOnOpenUniformisedSubalgebraRestrict
section
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RegAlg

theorem main : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), ∀ U : A.left.Opens, (∀ a : ℂ, IsReg u.ex U fun _ => a) ∧ (∀ k k', IsReg u.ex U k → IsReg u.ex U k' → IsReg u.ex U (k + k') ∧ IsReg u.ex U (k - k') ∧ IsReg u.ex U (k * k')) ∧ (∀ k k', IsReg u.ex U k → (∀ z ∈ pre u.ex U, k' z = k z) → IsReg u.ex U k') ∧ (∀ V, V ≤ U → ∀ k, IsReg u.ex U k → IsReg u.ex V k) ∧ (∀ k, IsReg u.ex U k → DifferentiableOn ℂ k (pre u.ex U)) ∧ ∀ (n : ℕ) (k : Fin n → (Fin g → ℂ) → ℂ), (∀ i, IsReg u.ex U (k i)) → IsReg u.ex U (fun z => ∑ i, k i z) := by
  intro A _ g L u U
  refine ⟨fun a => ?_, fun k k' hk hk' => ?_, fun k k' hk he => ?_, fun V hV k hk => ?_, fun k hk => ?_, fun n k hk => ?_⟩
  · refine ⟨constFn A.hom U a, fun z hz => ?_⟩
    have hp : (u.ex z).left ≫ A.hom = 𝟙 _ := by
      simpa using Over.w (u.ex z)
    exact (GlobalTheory.valAt'_constFn (u.ex z).left A.hom hp U a hz).symm
  · obtain ⟨b, hb⟩ := hk
    obtain ⟨b', hb'⟩ := hk'
    refine ⟨⟨b + b', fun z hz => ?_⟩, ⟨b - b', fun z hz => ?_⟩, ⟨b * b', fun z hz => ?_⟩⟩
    · simp only [Pi.add_apply, GlobalTheory.CechPer.val, GlobalTheory.valAt'_add, hb z hz, hb' z hz]
    · simp only [Pi.sub_apply, GlobalTheory.CechPer.val, GlobalTheory.valAt'_sub, hb z hz, hb' z hz]
    · simp only [Pi.mul_apply, GlobalTheory.CechPer.val, GlobalTheory.valAt'_mul, hb z hz, hb' z hz]
  · obtain ⟨b, hb⟩ := hk
    exact ⟨b, fun z hz => (he z hz).trans (hb z hz)⟩
  · obtain ⟨b, hb⟩ := hk
    refine ⟨resG A.left hV b, fun z hz => ?_⟩
    have hzU : z ∈ pre u.ex U := GlobalTheory.top_le_preimage_mono _ hV hz
    rw [hb z hzU]
    exact (GlobalTheory.valAt'_res (u.ex z).left hV b hz).symm
  · obtain ⟨b, hb⟩ := hk
    exact (u.hol U b).2.congr fun z hz => hb z hz
  · choose b hb using hk
    refine ⟨∑ i, b i, fun z hz => ?_⟩
    simp only [GlobalTheory.CechPer.val, GlobalTheory.valAt'_sum]
    exact Finset.sum_congr rfl fun i _ => hb i z hz

end GlobalTheory.RegAlg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IterateLinearPart
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries

namespace GlobalTheory.LinearPartIteration

variable {R : Type} [CommRing R] {d : ℕ}

def part (F : MvPowerSeries (Fin d) R) (j : Fin d) : MvPowerSeries (Fin d) R :=
  fun α => if ∀ k < j, α k = 0 then coeff (α + Finsupp.single j 1) F else 0

theorem coeff_part (F : MvPowerSeries (Fin d) R) (j : Fin d) (α : Fin d →₀ ℕ) :
    coeff α (part F j) = if ∀ k < j, α k = 0 then coeff (α + Finsupp.single j 1) F else 0 := rfl

theorem constantCoeff_part (F : MvPowerSeries (Fin d) R) (j : Fin d) :
    constantCoeff (part F j) = coeff (Finsupp.single j 1) F := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_part]
  simp

theorem coeff_X_mul_part (F : MvPowerSeries (Fin d) R) (j : Fin d) (β : Fin d →₀ ℕ) :
    coeff β (X j * part F j) = if β j ≠ 0 ∧ ∀ k < j, β k = 0 then coeff β F else 0 := by
  classical
  rw [X_def, coeff_monomial_mul, one_mul, coeff_part]
  by_cases h : β j = 0
  · rw [if_neg, if_neg]
    · simp [h]
    · rw [Finsupp.single_le_iff]; omega
  · have hle : Finsupp.single j 1 ≤ β := by rw [Finsupp.single_le_iff]; omega
    rw [if_pos hle, tsub_add_cancel_of_le hle]
    have : (∀ k < j, (β - Finsupp.single j 1 : Fin d →₀ ℕ) k = 0) ↔ (β j ≠ 0 ∧ ∀ k < j, β k = 0) := by
      constructor
      · intro H
        refine ⟨h, fun k hk => ?_⟩
        have := H k hk
        rwa [Finsupp.tsub_apply, Finsupp.single_eq_of_ne hk.ne, Nat.sub_zero] at this
      · intro H k hk
        rw [Finsupp.tsub_apply, H.2 k hk, Nat.zero_sub]
    simp only [this]

theorem eq_const_add_sum (F : MvPowerSeries (Fin d) R) :
    F = C (constantCoeff F) + ∑ j, X j * part F j := by
  classical
  ext β
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_add (f := _), map_sum, coeff_C]
  simp only [coeff_X_mul_part]
  by_cases hβ : β = 0
  · subst hβ
    simp
  · rw [if_neg hβ, zero_add]
    have hne : β.support.Nonempty := Finsupp.support_nonempty_iff.2 hβ
    have h0 : β (β.support.min' hne) ≠ 0 := Finsupp.mem_support_iff.1 (β.support.min'_mem hne)
    have h1 : ∀ k < β.support.min' hne, β k = 0 := fun k hk => by
      by_contra hk0
      exact absurd (β.support.min'_le k (Finsupp.mem_support_iff.2 hk0)) (not_le.2 hk)
    rw [Finset.sum_eq_single (β.support.min' hne), if_pos ⟨h0, h1⟩]
    · intro j _ hj
      rw [if_neg]
      rintro ⟨h2, h3⟩
      rcases lt_or_gt_of_ne hj with h | h
      · exact h2 (h1 j h)
      · exact h0 (h3 _ h)
    · simp

theorem iterate_linear_part : ∀ (p : ℕ) [Fact (Nat.Prime p)] (R : Type) [inst : CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R), (∀ (i : Fin d), (MvPowerSeries.constantCoeff : MvPowerSeries (Fin d ⊕ Fin d) R → R) (μ i) = (0 : R)) → ((GlobalTheory.Katz.op μ (fun (i : Fin d) ↦ MvPowerSeries.X i) fun (x : Fin d) ↦ (0 : MvPowerSeries (Fin d) R)) = fun (i : Fin d) ↦ MvPowerSeries.X i) → (∀ (i : Fin d), GlobalTheory.Katz.swap (μ i) = μ i) → ∀ (u : Fin d → R) (F : MvPowerSeries (Fin d) R), ∃ (r : R), (MvPowerSeries.constantCoeff : MvPowerSeries (Fin d) R → R) ((GlobalTheory.LawDer.invDer μ u)^[p] F) - ∑ j : Fin d, (MvPowerSeries.constantCoeff : MvPowerSeries (Fin d) R → R) ((GlobalTheory.LawDer.invDer μ u)^[p] (MvPowerSeries.X j)) * (MvPowerSeries.coeff fun₀ | j => (1 : ℕ) : MvPowerSeries (Fin d) R → R) F = (↑p : R) * r := by
  intro p hp R _ d μ h0 h1 _ u F
  obtain ⟨hadd, hsmul, hC⟩ := GlobalTheory.T.invariantDerivationFormalGroupLaw_isLinear R d μ h0 u
  let D : MvPowerSeries (Fin d) R →ₗ[R] MvPowerSeries (Fin d) R :=
    { toFun := GlobalTheory.LawDer.invDer μ u, map_add' := hadd, map_smul' := hsmul }
  have hD : ∀ G, (GlobalTheory.LawDer.invDer μ u)^[p] G = (D ^ p) G := fun G => by
    rw [Module.End.pow_apply]; rfl
  have hDC : ∀ a : R, (D ^ p) (C a) = 0 := fun a => by
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hp.out.ne_zero
    rw [hn, pow_succ, Module.End.mul_apply, show D (C a) = 0 from hC a, map_zero]
  have key : ∀ j : Fin d, ∃ r : R, constantCoeff ((D ^ p)
      (X j * (part F j - C (coeff (Finsupp.single j 1) F)))) = p * r := fun j => by
    rw [← hD]
    exact _root_.GlobalTheory.LawDer.constantCoeff_iterate_invDer_mul p R d μ h0 h1 u _ _ (by simp) (by simp [constantCoeff_part])
  choose r hr using key
  refine ⟨∑ j, r j, ?_⟩
  have hF : constantCoeff ((D ^ p) F) = ∑ j, constantCoeff ((D ^ p) (X j * part F j)) := by
    conv_lhs => rw [eq_const_add_sum F]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_add (f := _), hDC, zero_add, map_sum, map_sum]
  simp only [hD]
  rw [hF, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← hr j, mul_sub, map_sub, map_sub, mul_comm (X j) (C _), ← smul_eq_C_mul, map_smul,
    ← coeff_zero_eq_constantCoeff_apply ((_ : R) • _), map_smul, coeff_zero_eq_constantCoeff_apply,
    smul_eq_mul, mul_comm (constantCoeff _)]

end GlobalTheory.LinearPartIteration
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IteratedFDerivWordEqCoeff
section
open Filter Topology

namespace GlobalTheory.PeriodFamily

theorem sum_words_eq_sum_multinomial {I : Type} [Fintype I] [DecidableEq I] {D : Type}
    [AddCommGroup D] [Module ℂ D] (k : ℕ) (G : (I →₀ ℕ) → D) :
    ∑ s : Fin k → I, G (∑ a, Finsupp.single (s a) 1) =
      ∑ m ∈ Finset.finsuppAntidiag (Finset.univ : Finset I) k,
        (Nat.multinomial Finset.univ m : ℂ) • G m := by
  let ℓ : MvPolynomial I ℂ →ₗ[ℂ] D := (MvPolynomial.basisMonomials I ℂ).constr ℂ G
  have hℓ : ∀ m, ℓ (MvPolynomial.monomial m 1) = G m := fun m => by
    have := (MvPolynomial.basisMonomials I ℂ).constr_basis ℂ G m
    rwa [MvPolynomial.coe_basisMonomials] at this
  have h1 : (∑ i, (MvPolynomial.X i : MvPolynomial I ℂ)) ^ k =
      ∑ s : Fin k → I, MvPolynomial.monomial (∑ a, Finsupp.single (s a) 1) 1 := by
    rw [Fintype.sum_pow]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [MvPolynomial.monomial_sum_one]
    rfl
  have h2 : (∑ i, (MvPolynomial.X i : MvPolynomial I ℂ)) ^ k =
      ∑ m ∈ Finset.finsuppAntidiag (Finset.univ : Finset I) k,
        (Nat.multinomial Finset.univ m : ℂ) • MvPolynomial.monomial m 1 := by
    rw [Finset.sum_pow_eq_sum_piAntidiag]
    symm
    refine Finset.sum_nbij' (fun m => (m : I → ℕ)) (fun m => Finsupp.equivFunOnFinite.symm m)
      ?_ ?_ ?_ ?_ ?_
    · intro m hm
      simpa using hm
    · intro m hm
      simpa using hm
    · intro m _
      simp
    · intro m _
      simp
    · intro m _
      rw [MvPolynomial.monomial_eq, Finsupp.prod_fintype _ _ (by simp), Nat.cast_smul_eq_nsmul,
        nsmul_eq_mul]
      simp
  have h := congrArg ℓ (h1.symm.trans h2)
  set_option synthInstance.maxHeartbeats 100000 in
    simpa only [map_sum, map_smul, hℓ] using h

theorem iteratedFDeriv_word_eq_coeff {I : Type} [Fintype I] [DecidableEq I] {k : ℕ}
    {f : (I → ℂ) → ℂ} (hf : AnalyticAt ℂ f 0) (s : Fin k → I) :
    iteratedFDeriv ℂ k f 0 (fun a => Pi.single (s a) 1) =
      ((∏ i, ((∑ a, Finsupp.single (s a) 1 : I →₀ ℕ) i).factorial : ℕ) : ℂ) *
        MvPowerSeries.coeff (∑ a, Finsupp.single (s a) 1) (GlobalTheory.taylor f) := by
  have hl : ((List.ofFn s : List I) : Multiset I) =
      Finsupp.toMultiset (∑ a, Finsupp.single (s a) 1 : I →₀ ℕ) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [Finsupp.toMultiset_single, one_smul]
    rw [← Fin.univ_val_map, Finset.sum_eq_multiset_sum, ← Multiset.sum_map_singleton (Multiset.map s _),
      Multiset.map_map]
    rfl
  rw [GlobalTheory.taylor_eq_taylorDir, GlobalTheory.coeff_taylorDir_eq_lineDerivList _ hf hl, List.map_ofFn,
    GlobalTheory.lineDerivList_ofFn hf, mul_inv_cancel_left₀ (GlobalTheory.cast_prod_factorial_ne_zero _)]
  rfl

theorem taylor_eq_sum_coeff_taylor : ∀ {I : Type} [Fintype I] [DecidableEq I] {D : Type}
    [CommRing D] [Algebra ℂ D] (N : ℕ) (t : I → D) (f : (I → ℂ) → ℂ), AnalyticAt ℂ f 0 →
    GlobalTheory.PeriodFamily.taylor N t f = ∑ k ∈ Finset.range (N + 1),
      ∑ m ∈ Finset.finsuppAntidiag (Finset.univ : Finset I) k,
        MvPowerSeries.coeff m (GlobalTheory.taylor f) • ∏ i, t i ^ m i := by
  intro I _ _ D _ _ N t f hf
  unfold GlobalTheory.PeriodFamily.taylor
  refine Finset.sum_congr rfl fun k _ => ?_
  have hp : ∀ s : Fin k → I, ∏ a, t (s a) =
      ∏ i, t i ^ (∑ a, Finsupp.single (s a) 1 : I →₀ ℕ) i := fun s => by
    simp only [Finsupp.finsetSum_apply, ← Finset.prod_pow_eq_pow_sum]
    rw [Finset.prod_comm]
    refine Finset.prod_congr rfl fun a _ => ?_
    simp [Finsupp.single_apply]
  simp only [iteratedFDeriv_word_eq_coeff hf, hp]
  rw [sum_words_eq_sum_multinomial k fun m : I →₀ ℕ =>
    ((k.factorial : ℂ)⁻¹ * (((∏ i, (m i).factorial : ℕ) : ℂ) *
      MvPowerSeries.coeff m (GlobalTheory.taylor f))) • ∏ i, t i ^ m i]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hk : ∑ i, m i = k := (Finset.mem_finsuppAntidiag.1 hm).1
  have hs : ((∏ i, (m i).factorial : ℕ) : ℂ) * (Nat.multinomial Finset.univ m : ℂ) =
      (k.factorial : ℂ) := by
    rw [← Nat.cast_mul, Nat.multinomial_spec, hk]
  have h0 : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.2 k.factorial_ne_zero
  rw [smul_smul]
  congr 1
  rw [← mul_assoc, ← mul_assoc, mul_right_comm _ _ ((∏ i, (m i).factorial : ℕ) : ℂ),
    mul_comm (Nat.multinomial _ _ : ℂ), hs, mul_inv_cancel₀ h0, one_mul]

end GlobalTheory.PeriodFamily
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KaehlerAffineOpenFiniteProjectiveRank
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechPer

theorem locally_standardSmooth_sec (A : Over (Sp ℂ)) (g : ℕ) (h : SmoothOfRelativeDimension g A.hom) (U : A.left.affineOpens) :
    RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension g) (algebraMap ℂ (Sec (str A) U.1)) := by
  have h' : SmoothOfRelativeDimension g (str A) := by
    simpa [str] using h
  have h1 := HasRingHomProperty.appLE (@SmoothOfRelativeDimension g) (str A) h' ⟨⊤, isAffineOpen_top _⟩ U le_top
  have hr := RingHom.locally_respectsIso (RingHom.isStandardSmoothOfRelativeDimension_respectsIso (n := g))
  exact hr.2 _ (Scheme.ΓSpecIso (CommRingCat.of ℂ)).symm.commRingCatIsoToRingEquiv h1

theorem kaehler_sec_finite_projective_rank : ∀ (A : Over (Sp ℂ)) (g : ℕ), SmoothOfRelativeDimension g A.hom → ∀ U : A.left.affineOpens, Module.Finite (Sec (str A) U.1) Ω[Sec (str A) U.1⁄ℂ] ∧ Module.Projective (Sec (str A) U.1) Ω[Sec (str A) U.1⁄ℂ] ∧ ∀ p : PrimeSpectrum (Sec (str A) U.1), Module.rankAtStalk Ω[Sec (str A) U.1⁄ℂ] p = g := by
  intro A g h U
  have hl := locally_standardSmooth_sec A g h U
  haveI := GlobalTheory.AugCot.smooth_of_locally hl
  exact ⟨inferInstance, inferInstance, GlobalTheory.AugCot.rankAtStalk_kaehler_of_locally hl⟩

end GlobalTheory.CechPer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelQuotientModuleSurjection
section
open NumberField GlobalTheory.UPel.HT GlobalTheory.UPel.HT.EtLev
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_quotient_module_surjection : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (w0 : Ideal (𝓞 D.F)) (r : ℕ), w0.IsMaximal →
    ∃ g : D.La →+ (Fin (D.m * D.n) → 𝓞 D.F ⧸ w0 ^ r), Function.Surjective g ∧
      (∀ (c : 𝓞 D.F) (x : D.La), g (algebraMap (𝓞 D.F) D.O c • x) = Ideal.Quotient.mk (w0 ^ r) c • g x) ∧
      ∀ x, g x = 0 ↔ x ∈ GlobalTheory.UPel.HT.EtLev.wSub D w0 r := by
  first | (exact @GlobalTheory.UPel.HT.EtLev.latQuot_free) | (exact GlobalTheory.UPel.HT.EtLev.latQuot_free) | (intros; apply GlobalTheory.UPel.HT.EtLev.latQuot_free <;> assumption)
end

