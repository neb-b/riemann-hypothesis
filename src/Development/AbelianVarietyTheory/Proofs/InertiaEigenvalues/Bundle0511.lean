module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0497
public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0493
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0477
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0315
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0379
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowEqOfRoot
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalLetter
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AutCongrContinuousCycInertia
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0455
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0190
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0464
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0433
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0443
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0453
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0461
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0471
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0452
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0463
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0186
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0245
public import GroundTheory.LocalFields.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPolynomialApproxDividedTwoVariableSet
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism GlobalTheory.CrysEval
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.CrysEval

theorem coeff_coeff_natCast_mul {K : Type} [CommRing K] (m : ℕ) (q : K⟦X⟧⟦X⟧) (i n : ℕ) :
    coeff n (coeff i ((m : K⟦X⟧⟦X⟧) * q)) = (m : K) * coeff n (coeff i q) := by
  rw [← map_natCast (C : K⟦X⟧ →+* K⟦X⟧⟦X⟧), coeff_C_mul, ← map_natCast (C : K →+* K⟦X⟧), coeff_C_mul]

theorem exists_poly_approx_PPSet : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), ∀ F ∈ PPSet t K e, ∀ r : ℕ, ∃ (n : ℕ) (b : Bp l a) (p h : ZMod a → K⟦X⟧⟦X⟧), n ≠ 0 ∧ p ∈ PPSet t K e ∧ h ∈ PPSet t K e ∧ (n : ZMod a → K⟦X⟧⟦X⟧) * p = iotaP K t b ∧ F = p + (l : ZMod a → K⟦X⟧⟦X⟧) ^ r * h := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ t F hF r
  classical
  have hK0 := charZero_K (l := l) (K := K)
  obtain ⟨w, hw, hFw⟩ := hF
  let N : ℕ × ℕ → ℕ := fun x => x.1.factorial * (x.2 / e).factorial
  have hNpos : ∀ x, N x ≠ 0 := fun x => Nat.mul_ne_zero (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _)
  have hN0 : ∀ x, (N x : K) ≠ 0 := fun x => Nat.cast_ne_zero.2 (hNpos x)
  let ser : (ℕ × ℕ → Wq l a) → ZMod a → K⟦X⟧⟦X⟧ := fun v τ =>
    PowerSeries.mk fun i => PowerSeries.mk fun n => embK K t τ (v (i, n)) / (N (i, n) : K)
  have coeff_ser : ∀ v τ i n, coeff n (coeff i (ser v τ)) = embK K t τ (v (i, n)) / (N (i, n) : K) := by
    intro v τ i n; simp [ser]
  have ser_mem : ∀ v, LTo0 l v → ser v ∈ PPSet t K e := by
    intro v hv
    refine ⟨v, hv, fun τ i n => ?_⟩
    rw [coeff_ser, mul_div_cancel₀ _ (hN0 (i, n))]
    rfl
  have coeff_F : ∀ τ i n, coeff n (coeff i (F τ)) = embK K t τ (w (i, n)) / (N (i, n) : K) := by
    intro τ i n
    rw [eq_div_iff (hN0 _), mul_comm]
    exact hFw τ i n
  have hfin : {x | ¬ (l : Wq l a) ^ r ∣ w x}.Finite := Filter.eventually_cofinite.1 (hw r)
  let s := hfin.toFinset
  have mem_s : ∀ x, x ∈ s ↔ ¬ (l : Wq l a) ^ r ∣ w x := fun x => by simp [s]
  let c : ℕ × ℕ → Wq l a := fun x => if h : (l : Wq l a) ^ r ∣ w x then h.choose else 0
  let w₁ : ℕ × ℕ → Wq l a := fun x => if x ∈ s then w x else 0
  have hsplit : ∀ x, w x = w₁ x + (l : Wq l a) ^ r * c x := by
    intro x
    by_cases h : (l : Wq l a) ^ r ∣ w x
    · have hx : x ∉ s := fun hx => (mem_s x).1 hx h
      simp only [w₁, c, hx, if_false, dif_pos h, zero_add]
      exact h.choose_spec
    · have hx : x ∈ s := (mem_s x).2 h
      simp [w₁, c, hx, h]
  have hw₁ : LTo0 l w₁ := by
    intro m
    refine Filter.eventually_cofinite.2 (hfin.subset fun x hx => ?_)
    simp only [Set.mem_setOf_eq] at hx ⊢
    intro hd
    apply hx
    have : x ∉ s := fun hx' => (mem_s x).1 hx' hd
    simp [w₁, this]
  have hc : LTo0 l c := by
    intro m
    filter_upwards [hw (m + r)] with x hx
    have h : (l : Wq l a) ^ r ∣ w x := dvd_trans (pow_dvd_pow _ (Nat.le_add_left r m)) hx
    obtain ⟨d, hd⟩ := hx
    have hcx : c x = h.choose := dif_pos h
    have hspec := h.choose_spec
    refine ⟨d, ?_⟩
    rw [hcx]
    have hl0 : l ^ r ≠ 0 := pow_ne_zero _ (Fact.out : l.Prime).ne_zero
    have := wq_nat_cancel (K := K) t hl0 (x := h.choose - (l : Wq l a) ^ m * d) (by
      push_cast
      linear_combination hd - hspec)
    exact sub_eq_zero.1 this
  let nn : ℕ := ∏ x ∈ s, N x
  let b : Bp l a := ∑ x ∈ s, Polynomial.monomial x.1 (Polynomial.monomial x.2 ((nn / N x) • w x))
  have coeff_b : ∀ i n, (b.coeff i).coeff n = if (i, n) ∈ s then (nn / N (i, n)) • w (i, n) else 0 := by
    intro i n
    simp only [b, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
    rw [Finset.sum_congr rfl (g := fun x => if x = (i, n) then (nn / N x) • w x else 0)]
    · exact Finset.sum_ite_eq' _ _ _
    · intro x _
      obtain ⟨x1, x2⟩ := x
      by_cases h1 : x1 = i <;> by_cases h2 : x2 = n <;> simp [h1, h2, Polynomial.coeff_monomial, Prod.ext_iff] <;> first | done | (subst h1; simp_all) | (split_ifs <;> simp_all)
  refine ⟨nn, b, ser w₁, ser c, Finset.prod_ne_zero_iff.2 fun x _ => hNpos x, ser_mem _ hw₁, ser_mem _ hc, ?_, ?_⟩
  · funext τ
    refine PowerSeries.ext fun i => PowerSeries.ext fun n => ?_
    rw [Pi.mul_apply, Pi.natCast_apply, coeff_coeff_natCast_mul, coeff_ser, coeff_iotaP, coeff_b]
    split_ifs with hx
    · have hdvd : N (i, n) ∣ nn := Finset.dvd_prod_of_mem N hx
      simp only [w₁, hx, if_true]
      rw [map_nsmul, nsmul_eq_mul, Nat.cast_div hdvd (hN0 _)]
      field_simp
    · simp [w₁, hx]
  · funext τ
    refine PowerSeries.ext fun i => PowerSeries.ext fun n => ?_
    rw [← Nat.cast_pow, Pi.add_apply, Pi.mul_apply, Pi.natCast_apply, map_add (f := _), map_add (f := _), coeff_coeff_natCast_mul,
      coeff_F, coeff_ser, coeff_ser, hsplit (i, n), map_add, map_mul, map_pow, map_natCast]
    push_cast
    ring

end GlobalTheory.CrysEval
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsXPowSmulMemWachModuleOfFrobenius
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices
set_option maxHeartbeats 1000000

namespace GlobalTheory.NL.DenomStep

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA]
    [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}
    {W : LocWach PD LL O v n}

theorem mem_N_of_jD (E : EtTie W RA RW inclR φR gR πA) (T : LocLat G Qp LL O)
    (hT : IsCrys PD T.ρ) (h1 : p1et W E T)
    (h6 : ∀ x : W.EE, (∃ y, inclR y = E.ioE x) → ∃ a : LetA O n, algebraMap _ W.EE a = x)
    (x : W.DD T) (hx : E.jD T x ∈ NAinf W E T) : x ∈ W.N T := by
  obtain ⟨⟨r, b, hbN, hbA, hbW⟩, -⟩ := h1

  have hNA : ∀ z ∈ NAinf W E T, ∃ β : Fin r → RA, z = ∑ j, inclR (β j) • E.jD T (b j) := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨a, x, hxN, rfl⟩ := hz
      obtain ⟨α, hα, -⟩ := hbA x hxN
      refine ⟨fun j => a * E.io (α j), ?_⟩
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hα, map_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [GlobalTheory.NL.FrobDenom.jD_smulA, smul_smul, map_mul]
    | zero => exact ⟨0, by simp⟩
    | add z w _ _ hz hw =>
      obtain ⟨β, rfl⟩ := hz
      obtain ⟨γ, rfl⟩ := hw
      refine ⟨β + γ, ?_⟩
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Pi.add_apply, map_add (f := _), add_smul]
    | smul c z _ hz =>
      obtain ⟨β, rfl⟩ := hz
      refine ⟨c • β, ?_⟩
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Pi.smul_apply, map_smul, smul_assoc]

  have hDE : ∀ y : W.DD T, ∃ μ : Fin r → W.EE, y = ∑ j, μ j • b j := by
    intro y
    refine (W.N_base T hT).inductionOn y ?_ ?_ ?_
    · intro z
      obtain ⟨α, hα, -⟩ := hbA z z.2
      refine ⟨fun j => algebraMap _ W.EE (α j), ?_⟩
      simp only [Submodule.subtype_apply, algebraMap_smul]
      exact hα
    · rintro e y ⟨μ, rfl⟩
      exact ⟨e • μ, by simp [Finset.smul_sum, smul_smul]⟩
    · rintro y y' ⟨μ, rfl⟩ ⟨μ', rfl⟩
      exact ⟨μ + μ', by simp [add_smul, Finset.sum_add_distrib]⟩
  obtain ⟨β, hβ⟩ := hNA _ hx
  obtain ⟨μ, rfl⟩ := hDE x
  have hj : E.jD T (∑ j, μ j • b j) = ∑ j, E.ioE (μ j) • E.jD T (b j) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_congr rfl fun j _ => E.jD_smul T _ _
  obtain ⟨c, -, hc⟩ := hbW (E.jD T (∑ j, μ j • b j))
  have e1 := hc (fun j => E.ioE (μ j)) hj
  have e2 := hc (fun j => inclR (β j)) hβ
  have hμ : ∀ j, ∃ a : LetA O n, algebraMap _ W.EE a = μ j := fun j =>
    h6 (μ j) ⟨β j, (congrFun e2 j).trans (congrFun e1 j).symm⟩
  choose a ha using hμ
  have : ∑ j, μ j • b j = ∑ j, a j • b j := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← ha j, algebraMap_smul]
  rw [this]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hbN j)

end Generic

end GlobalTheory.NL.DenomStep

namespace GlobalTheory.NL.DenomStep

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA]
    [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}
    {W : LocWach PD LL O v n}

theorem of_tie (E : EtTie W RA RW inclR φR gR πA) (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ)
    (hF : ∀ (J : Multiset ℕ) (y : W.DD T), (J.map fun j => (W.φA ^ j) W.Q).prod • y ∈ W.N T →
      ∀ b : TW RW T, TWmap φR T b - b = E.jD T y → ∀ m : ℕ, (∀ j ∈ J, j ≤ m) → ∃ a : ℕ,
        TensorProduct.map (LinearMap.mulLeft O
          (inclR (E.io (∏ j ∈ Finset.range (m + 1), (W.φA ^ j) W.X)) ^ a)) LinearMap.id b ∈
          TAinf inclR T)
    (hP1 : p1et W E T ∧ wachInfiniteLevel W E T)
    (h6 : ∀ x : W.EE, (∃ y, inclR y = E.ioE x) → ∃ a : LetA O n, algebraMap _ W.EE a = x)
    (M : ℕ) (m : W.DD T) (hm : W.φD T m - m ∈ invN W T (W.Q ^ M)) :
    ∃ a : ℕ, W.X ^ a • m ∈ W.N T := by
  have hy : ((Multiset.replicate M 0).map fun j => (W.φA ^ j) W.Q).prod • (W.φD T m - m) ∈
      W.N T := by
    rw [Multiset.map_replicate, Multiset.prod_replicate, pow_zero]
    exact hm
  have hb : TWmap φR T (E.jD T m) - E.jD T m = E.jD T (W.φD T m - m) := by
    rw [map_sub, E.jD_φ]
  obtain ⟨a, ha⟩ := hF _ _ hy _ hb 0 (fun j hj => (Multiset.eq_of_mem_replicate hj).le)
  rw [Finset.prod_range_one, pow_zero, GlobalTheory.NL.SandArb.map_mulLeft] at ha
  obtain ⟨h1, k, hk, -⟩ := hP1
  have hz := hk _ ha
  refine ⟨k + a, mem_N_of_jD E T hT h1 h6 _ ?_⟩
  rw [GlobalTheory.NL.FrobDenom.jD_smulA, map_pow, map_pow, pow_add, mul_smul]
  exact hz

end Generic


set_option synthInstance.maxHeartbeats 200000 in
theorem main : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ (M : ℕ) (m : W.DD T), W.φD T m - m ∈ invN W T (W.Q ^ M) → ∃ a : ℕ, W.X ^ a • m ∈ W.N T := by
  intro D HW F l _ K s LL h W T hT M m hm
  exact of_tie ((F l).E K s LL h).tie T hT (GlobalTheory.NL.FrobDenom.main D HW F l K s LL h T hT)
    (GlobalTheory.NL.NygaardExtension.main D HW F l K s LL h T hT) (GlobalTheory.NL.IoXQ.main D HW F l K s LL h).2.2.2.2.2.1 M m hm

end GlobalTheory.NL.DenomStep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FKEqResDeg
section
noncomputable section

open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain GlobalTheory.WeilDeligne GlobalTheory.Pst
open GlobalTheory.BKReal IsLocalRing Formalism.BasicNotions.Examples₂.LB

namespace GlobalTheory.AinfK

theorem fK_eq_resDeg {l : ℕ} [hl : Fact l.Prime] {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {O : Type} [CommRing O]
    [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (h : IsPlaceOver A w)
    (hj : Induces Bw) : fK Bw.Kw = resDeg l w := by
  have hN := normV_eq_pow (hj.mem_placesOver h)
  refine Nat.pow_right_injective hl.out.two_le (le_antisymm ?_ ?_)
  · obtain ⟨-, ω, hω, -⟩ := exists_gen l (fK Bw.Kw)
    have h1 := one_lt_pow_l l (fK Bw.Kw)
    have hm : ω ∈ K0 Bw.Kw := Kunr_fK Bw.Kw ▸ IntermediateField.subset_adjoin _ _ (show ω ^ l ^ fK Bw.Kw = ω by
      rw [← Nat.sub_add_cancel h1.le, pow_succ, hω.pow_eq_one, one_mul])
    have h2 := weilToGK_frobUr hj (frob h) (a := 1) (b := 0) (actsAs_of_deg (by simp)) ⟨ω, hm.2⟩
    rw [mul_one, mul_zero, pow_zero, frobUr_pow_root _ _ (l ^ fK Bw.Kw - 1) (by omega)
      (fun hd => hl.out.not_dvd_one ((Nat.dvd_sub_iff_right h1.le (dvd_pow_self l (NeZero.ne _))).1 hd))
      (Subtype.ext hω.pow_eq_one)] at h2
    have h3 : ω = ω ^ l ^ resDeg l w :=
      ((IntermediateField.mem_fixingSubgroup_iff _ _).1 (weilToGK Bw h (frob h)).2 _ hm.1).symm.trans h2
    have h4 := one_lt_normV w
    rw [hN] at h4
    have h5 : ω ^ (l ^ resDeg l w - 1) = 1 := mul_right_cancel₀ (hω.ne_zero (by omega)) (by
      rw [← pow_succ, Nat.sub_add_cancel h4.le, one_mul, ← h3])
    have := Nat.le_of_dvd (by omega) (hω.dvd_of_pow_eq_one _ h5)
    change l ^ _ ≤ l ^ _
    omega
  · change l ^ _ ≤ l ^ _
    rw [← hN, ← card_res]
    let u : 𝓞 E →+* ↥Bw.Kw.1 :=
      (Bw.j.comp ((algebraMap E Ω).comp (algebraMap (𝓞 E) E))).codRestrict Bw.Kw.1 fun x => Bw.j_E _
    let v : 𝓞 E →+* ↥(OL Bw.Kw) := u.codRestrict (OL Bw.Kw) fun x =>
      (map_isIntegral_int u (RingOfIntegers.isIntegral x)).tower_top
    have hk : ∀ x, ((residue _).comp v) x = 0 ↔ x ∈ w.asIdeal := fun x => by
      rw [RingHom.comp_apply, residue_eq_zero_iff, mem_max, ← h x, hj.valuation_lt_one_iff]
      rfl
    have := OL_resFinite Bw.Kw
    exact Nat.card_le_card_of_injective (Ideal.Quotient.lift w.asIdeal _ fun x hx => (hk x).2 hx)
      (RingHom.lift_injective_of_ker_le_ideal _ _ fun x hx => (hk x).1 hx)

end GlobalTheory.AinfK
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteLengthOfFiniteDimensional
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Polynomial

noncomputable section
namespace GlobalTheory.ConsCompare

section Factors
open GlobalTheory.AdmLoc
variable {k A : Type} [Field k] [Ring A] [Algebra k A]

theorem finiteLength_of_finiteDimensional (k : Type) [Field k] [Algebra k A] (M : Type) [AddCommGroup M]
    [Module k M] [Module A M] [IsScalarTower k A M] [FiniteDimensional k M] : IsFiniteLength A M := by
  rw [isFiniteLength_iff_isNoetherian_isArtinian]
  exact ⟨isNoetherian_of_tower k inferInstance, isArtinian_of_tower k inferInstance⟩

theorem exists_semisimple_sameFactors : ∀ (d : ℕ) (M : Type) [AddCommGroup M] [Module k M] [Module A M]
    [IsScalarTower k A M] [FiniteDimensional k M], Module.finrank k M = d →
    ∃ (S : Type) (_ : AddCommGroup S) (_ : Module k S) (_ : Module A S) (_ : IsScalarTower k A S)
      (_ : FiniteDimensional k S), IsSemisimpleModule A S ∧ SameFactors A M S := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro M _ _ _ _ _ hd
  have hfl := finiteLength_of_finiteDimensional (A := A) k M
  rcases subsingleton_or_nontrivial M with h0 | h0
  · exact ⟨M, _, _, _, inferInstance, inferInstance, (isSemisimpleModule_iff A M).2
      (have := (Submodule.subsingleton_iff A).2 h0; Subsingleton.instComplementedLattice),
      SameFactors.refl hfl⟩
  · haveI : IsNoetherian A M := isNoetherian_of_tower k inferInstance
    obtain ⟨N, hN, -⟩ := (eq_top_or_exists_le_coatom (⊥ : Submodule A M)).resolve_left bot_ne_top
    have hlt : Module.finrank k N < d := by
      rw [← hd]
      exact Submodule.finrank_lt (s := N.restrictScalars k) fun h => hN.1 (by simpa using h)
    obtain ⟨S, _, _, _, _, _, hS, hf⟩ := ih _ hlt N rfl
    haveI : IsSimpleModule A (M ⧸ N) := isSimpleModule_iff_isCoatom.2 hN
    exact ⟨S × (M ⧸ N), _, _, _, inferInstance, inferInstance,
      isSemisimpleModule_of_isSemisimpleModule_submodule' (p := fun b : Bool =>
        cond b (LinearMap.range (LinearMap.inl A S (M ⧸ N))) (LinearMap.range (LinearMap.inr A S (M ⧸ N))))
        (by rintro (_ | _) <;> exact IsSemisimpleModule.range _)
        (by rw [iSup_bool_eq]; exact LinearMap.sup_range_inl_inr),
      (SameFactors.sub_prod_quot hfl N).trans
        (hf.prod (SameFactors.refl (finiteLength_of_finiteDimensional k _)))⟩

theorem cpOn_eq_of_sameFactors (a : A) {M M' : Type} [AddCommGroup M] [Module k M] [Module A M]
    [IsScalarTower k A M] [FiniteDimensional k M] [AddCommGroup M'] [Module k M'] [Module A M']
    [IsScalarTower k A M'] [FiniteDimensional k M'] (h : SameFactors A M M') : cpOn k a M = cpOn k a M' := by
  obtain ⟨s, t, h1, h2, h3, h4, f, hf⟩ := h
  rw [cpOn_series _ s h1 h2, cpOn_series _ t h3 h4]
  exact Fintype.prod_equiv f _ _ fun j => cpOn_congr _ (hf j).some

variable {Γ : Type} [Group Γ]

def repOf (k Γ S : Type) [Field k] [Group Γ] [AddCommGroup S] [Module k S] [Module (MonoidAlgebra k Γ) S]
    [IsScalarTower k (MonoidAlgebra k Γ) S] : Representation k Γ S :=
  (Algebra.lsmul k k S : MonoidAlgebra k Γ →ₐ[k] Module.End k S).toMonoidHom.comp (MonoidAlgebra.of k Γ)

theorem isSS_repOf {S : Type} [AddCommGroup S] [Module k S] [Module (MonoidAlgebra k Γ) S]
    [IsScalarTower k (MonoidAlgebra k Γ) S] [IsSemisimpleModule (MonoidAlgebra k Γ) S] :
    IsSS (repOf k Γ S) := fun W hW => by
  let W₁ : Submodule (MonoidAlgebra k Γ) S :=
    { W.toAddSubmonoid with
      smul_mem' := fun a v hv => by
        induction a using MonoidAlgebra.induction_on with
        | of g => exact hW g v hv
        | add a b ha hb => rw [add_smul]; exact W.add_mem ha hb
        | smul c a ha => rw [smul_assoc]; exact W.smul_mem c ha }
  obtain ⟨W₂, h⟩ := exists_isCompl W₁
  refine ⟨W₂.restrictScalars k, fun g v hv => W₂.smul_mem (MonoidAlgebra.of k Γ g) hv, ?_⟩
  exact (Submodule.isCompl_restrictScalars_iff k (s := W₁)).2 h

theorem sameSS_of_charpoly_eq (hBN : GlobalTheory.ConstituentsCompare.BrauerNesbitt) {V W : Type} [AddCommGroup V]
    [Module k V] [FiniteDimensional k V] [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (ρ : Representation k Γ V) (σ : Representation k Γ W)
    (h : ∀ g, LinearMap.charpoly (ρ g) = LinearMap.charpoly (σ g)) : GlobalTheory.IndefiniteRowSideFullHecke.CharPolyRootsConstruction.SameSS ρ σ := by
  have : FiniteDimensional k ρ.asModule := inferInstanceAs (FiniteDimensional k V)
  have : FiniteDimensional k σ.asModule := inferInstanceAs (FiniteDimensional k W)
  have e1 : ∀ g, LinearMap.charpoly (ρ g) = cpOn k (MonoidAlgebra.of k Γ g) ρ.asModule := fun g => by
    unfold cpOn
    rw [← LinearEquiv.charpoly_conj ρ.asModuleEquiv]
    congr 1
    ext v
    simp [LinearEquiv.conj_apply]
    rfl
  have e2 : ∀ g, LinearMap.charpoly (σ g) = cpOn k (MonoidAlgebra.of k Γ g) σ.asModule := fun g => by
    unfold cpOn
    rw [← LinearEquiv.charpoly_conj σ.asModuleEquiv]
    congr 1
    ext v
    simp [LinearEquiv.conj_apply]
    rfl
  obtain ⟨S, _, _, _, _, _, hS, hf⟩ :=
    exists_semisimple_sameFactors (k := k) (A := MonoidAlgebra k Γ) _ ρ.asModule rfl
  obtain ⟨S', _, _, _, _, _, hS', hf'⟩ :=
    exists_semisimple_sameFactors (k := k) (A := MonoidAlgebra k Γ) _ σ.asModule rfl
  obtain ⟨e, he⟩ := GlobalTheory.brauerNesbitt_abstract_of_matrix hBN (repOf k Γ S) (repOf k Γ S') isSS_repOf isSS_repOf
    fun g => ((cpOn_eq_of_sameFactors _ hf).symm.trans ((e1 g).symm.trans ((h g).trans (e2 g)))).trans
      (cpOn_eq_of_sameFactors _ hf')
  let e' : S ≃ₗ[MonoidAlgebra k Γ] S' :=
    { e.toAddEquiv with
      map_smul' := fun a v => by
        show e (a • v) = a • e v
        induction a using MonoidAlgebra.induction_on with
        | of g => exact he g v
        | add a b ha hb => rw [add_smul, add_smul, map_add (f := _), ha, hb]
        | smul c a ha => rw [smul_assoc, smul_assoc, map_smul, ha] }
  exact (hf.trans (SameFactors.of_equiv hf.finiteLength_right e')).trans hf'.symm

end Factors

section Distinct
open Matrix

end Distinct

section BaseChange
open GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing

variable {Γ X A B : Type} [Group Γ] [CommRing A] [CommRing B] {n r t : ℕ}

variable [Algebra A B]

variable [IsDomain A] [IsDomain B]

variable [IsLocalRing A] [IsLocalRing B]

end BaseChange

end GlobalTheory.ConsCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteUnitsModSquaresOfUnramifiedQuadratic
section
open GlobalTheory.UnitLemma

namespace GlobalTheory.UnitLemma

theorem UQ.finite_units_mod_sq : ∀ (K : UQ) (L : Type) [Field L] [Algebra K.E L] [FiniteDimensional K.E L],
    Finite (Lˣ ⧸ (powMonoidHom 2 : Lˣ →* Lˣ).range) := by
  intro K L _ _ _
  letI := GlobalTheory.LocFieldOfDVR.valued K.O K.E
  letI : ValuativeRel K.E := .ofValuation (GlobalTheory.LocFieldOfDVR.val K.O K.E)
  haveI : (GlobalTheory.LocFieldOfDVR.val K.O K.E).Compatible := .ofValuation _
  haveI : IsNonarchimedeanLocalField K.E := by
    have : IsValuativeTopology K.E :=
      IsValuativeTopology.of_mem_nhds_iff_vle (GlobalTheory.LocFieldOfDVR.val K.O K.E)
        (fun {s x} => Valued.mem_nhds)
    have : ValuativeRel.IsNontrivial K.E :=
      (ValuativeRel.isNontrivial_iff_isNontrivial (GlobalTheory.LocFieldOfDVR.val K.O K.E)).mpr inferInstance
    have : LocallyCompactSpace K.E := GlobalTheory.LocFieldOfDVR.locallyCompactSpace
    exact {}
  obtain ⟨vrL, topL, hlocL, -⟩ := GroundTheory.LocalField.exists_isNonarchimedeanLocalField_valuativeExtension K.E L
  haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap K.E L).injective
  exact GroundTheory.LocalField.finite_quotient_range_pow_of_charZero (K := L) two_ne_zero

end GlobalTheory.UnitLemma
end

