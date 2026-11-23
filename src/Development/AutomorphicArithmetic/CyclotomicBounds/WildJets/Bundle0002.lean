module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ExistsSmallSpherical
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0329
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HighestWeightBelow
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1615
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0484
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0471
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0431
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0442
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1641

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.AttExp
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.Chain.StepVac in
private theorem mu_exp' {D : D7} {T : Type} {L : LevCh D T} {μ₀ : T} (hL : L.Is μ₀) (t : T) (j : ℕ) (hj : j < D.R.m)
    (τ : D.what₂.Tau) : HasInfExp D (L.mu t (j + 1)) τ (-(D.hc τ).e ⟨j, hj⟩) := by
  obtain ⟨n, hn, ho⟩ := hL.xi_fin t
  have h0 := GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ _ (hL.mu0 ⟨j, hj⟩) (hasInfQ_tau (L.C.isMu0 ⟨j, hj⟩).inf) τ
  obtain ⟨θ, hθ⟩ : ∃ θ, IsInfFam (D := D) θ := by
    obtain ⟨_, _, hθ, _⟩ := h0
    exact hθ
  have := hasInfExp_mul h0 (hasInfExp_of_order hθ (hL.xi t) hn ho τ)
  rw [add_zero, Formalism.L2.Host.eExp, Equiv.symm_apply_apply] at this
  exact this

private theorem att_exp' {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) {μ0 : T} (hL : L.Is μ0)
    {i : ℕ} (hi : i < D.R.m) (n : ℕ) (τ : D.what₂.Tau) :
    HasInfExp D (Formalism.IndefR.Lift.attChr (G.ch.chi (D.R.m - i)) L.eta n) τ
      ((cen D sc.cGap τ (D.R.m - i) : ℚ) - if Odd n then 1 / 2 else 0) := by
  have hm1 : 1 ≤ D.R.m - i := by omega
  have hm2 : D.R.m - i ≤ D.R.m := by omega
  have h0 : HasInfExp D (G.ch.chi (D.R.m - i)) τ (cen D sc.cGap τ (D.R.m - i) : ℚ) :=
    GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ (fun τ => (cen D sc.cGap τ (D.R.m - i) : ℚ)) (G.ch.chi_eq _ hm1 hm2)
      ⟨fun τ => 2 * cen D sc.cGap τ (D.R.m - i), fun τ => by push_cast; ring, G.ch.inf _ hm1 hm2⟩ τ
  unfold Formalism.IndefR.Lift.attChr
  split_ifs
  · rw [sub_eq_add_neg]
    exact GlobalTheory.Chain.StepVac.hasInfExp_mul h0 (GlobalTheory.Chain.StepVac.hasInfExp_inv (GlobalTheory.SquareExps.eta_exp hL τ))
  · simpa using h0

theorem UpperTheory.WildA.expEx :
    ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GlobalTheory.ChiGrid.GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ p : GlobalTheory.ChiGrid.Pair T, DefPair D.R.m p → ∃ (a b : D.what₂.Tau → ℚ) (e₁ e₂ : D.what₂.Tau → ℤ),
      (∀ τ, HasInfExp D (G.chrS p) τ (a τ)) ∧ (∀ τ, HasInfExp D (G.chrT p) τ (b τ)) ∧
      (∀ τ, (e₁ τ : ℚ) = a τ + GlobalTheory.FockReal.sgnP p * (G.pS p).rank / 2) ∧ ∀ τ, (e₂ τ : ℚ) = -(b τ + GlobalTheory.FockReal.sgnP p * (G.pT p).rank / 2) := by
  intro D T L sc G μ₀ hL p hp
  have half : ∀ (c : ℤ) (n : ℕ), ∃ e : ℤ, (e : ℚ) = ((c : ℚ) - if Odd n then 1 / 2 else 0) + (-1) * (n : ℚ) / 2 := by
    intro c n
    rcases Nat.even_or_odd n with h | h
    · obtain ⟨k, hk⟩ := id h
      refine ⟨c - k, ?_⟩
      simp only [Nat.not_odd_iff_even.2 h, ite_false]; rw [hk]; push_cast; ring
    · obtain ⟨k, hk⟩ := id h
      refine ⟨c - k - 1, ?_⟩
      simp only [h, ite_true]; rw [hk]; push_cast; ring
  cases p with
  | mu t i j => exact hp.elim
  | core i => exact hp.elim
  | top t j =>
    have hj : j < D.R.m := hp
    have hr0 : Even (G.V (.top j)).rank := by rw [GlobalTheory.FunObj.rank_top G (j := j) (by omega)]; exact even_rankX D j
    have hr1 : Even (G.V (.top (j + 1))).rank := by
      rw [GlobalTheory.FunObj.rank_top G (j := j + 1) (by omega)]; exact even_rankX D (j + 1)
    have hS : G.chrS (.top t j) = L.mu t (j + 1) := by
      simp only [GridData.chrS, Formalism.IndefR.Lift.attChr, GridData.chr, GridData.pS, Nat.not_odd_iff_even.2 hr0, ite_false]
    have hT : G.chrT (.top t j) = L.mu t (j + 1) := by
      simp only [GridData.chrT, Formalism.IndefR.Lift.attChr, GridData.chr, GridData.pT, Nat.not_odd_iff_even.2 hr1, ite_false]
    have hce : ∀ τ, (((num D sc.cGap τ).e (j + 1) : ℤ) : ℚ) = (D.hc τ).e ⟨j, hj⟩ := fun τ =>
      GlobalTheory.SignedHC.GridData.extend_cast 1 (D.hc τ).e_int ⟨j, hj⟩
    obtain ⟨k0, hk0⟩ := hr0
    obtain ⟨k1, hk1⟩ := hr1
    refine ⟨fun τ => -((D.hc τ).e ⟨j, hj⟩ : ℚ), fun τ => -((D.hc τ).e ⟨j, hj⟩ : ℚ),
      fun τ => -(num D sc.cGap τ).e (j + 1) + k0, fun τ => (num D sc.cGap τ).e (j + 1) - k1,
      fun τ => ?_, fun τ => ?_, fun τ => ?_, fun τ => ?_⟩
    · rw [hS]; exact mu_exp' hL t j hj τ
    · rw [hT]; exact mu_exp' hL t j hj τ
    · simp only [GlobalTheory.FockReal.sgnP, one_mul, hk0, ← hce]; push_cast; ring
    · simp only [GlobalTheory.FockReal.sgnP, one_mul, hk1, ← hce]; push_cast; ring
  | chi i j =>
    have hi : i < D.R.m := hp.1
    choose e he using half
    refine ⟨_, _, fun τ => e (cen D sc.cGap τ (D.R.m - i)) (G.pS (.chi i j : Pair T)).rank,
      fun τ => -e (cen D sc.cGap τ (D.R.m - i)) (G.pT (.chi i j : Pair T)).rank,
      fun τ => att_exp' G hL hi _ τ, fun τ => att_exp' G hL hi _ τ, fun τ => ?_, fun τ => ?_⟩
    · exact he _ _
    · rw [Int.cast_neg, he]; rfl
end

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.BdLoss
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem UpperTheory.WildA.bdLoss :
    ∀ (D : D7) (w : PlL D) (l : ℕ) [Fact l.Prime], (l : 𝓞 D.what₂.LL) ∈ w.asIdeal → ∀ (z : ℂ) (B : ℝ), z ∈ Set.range D.what₂.embLL →
      (∀ lam : Formalism.MainNotions.TaylorLogMetric.Qbar →+* ℂ_[l], GlobalTheory.NormSum.Term.Bd lam ((l : ℝ) ^ B) z) → LossLe w z ((vw w ((l : ℕ) : D.what₂.LL) : ℝ) * B) := by
  intro D w l _ hl z B hz hB
  obtain ⟨y, rfl⟩ := hz
  refine ⟨y, rfl, ?_⟩
  by_cases hy : y = 0
  · exact Or.inl hy
  · right
    have key := GlobalTheory.PadicPlaceBound.neg_mul_vw_le_vw D.what₂.LL D.what₂.embLL y l w B hy hl
      (fun lam => (hB lam).2)
    rw [mul_comm] at key
    exact key
end

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.BvvInt
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

private theorem sum_map_apply {ι σ : Type} [Fintype ι] (m : ι → σ →₀ ℕ) (i : ι) (x : σ) :
    (∑ j, Finsupp.mapDomain (fun v : σ => (j, v)) (m j)) (i, x) = m i x := by
  classical
  rw [Finsupp.finsetSum_apply, Finset.sum_eq_single i]
  · exact Finsupp.mapDomain_apply_of_injective (fun a b h => (Prod.mk.inj h).2) _ _
  · intro j _ hj
    apply Finsupp.mapDomain_notin_range
    rintro ⟨y, hy⟩
    exact hj (Prod.mk.inj hy).1
  · intro h
    exact absurd (Finset.mem_univ i) h

private theorem coeff_prod' {ι σ C : Type} [DecidableEq ι] [DecidableEq σ] [CommRing C] (f : ι → MvPolynomial σ C)
    (d : σ →₀ ℕ) (s : Finset ι) :
    AddMonoidAlgebra.coeff (∏ j ∈ s, f j) d = ∑ l ∈ Finset.finsuppAntidiag s d, ∏ j ∈ s, AddMonoidAlgebra.coeff (f j) (l j) := by
  have h := MvPowerSeries.coeff_prod (fun j => (f j : MvPowerSeries σ C)) d s
  have hp : ((∏ j ∈ s, f j : MvPolynomial σ C) : MvPowerSeries σ C) = ∏ j ∈ s, (f j : MvPowerSeries σ C) :=
    map_prod (MvPolynomial.coeToMvPowerSeries.ringHom (σ := σ) (R := C)) f s
  rw [← hp] at h
  simpa only [MvPolynomial.coeff_coe] using h

private theorem coeff_prod_ren {ι σ C : Type} [Fintype ι] [CommRing C] (m : ι → σ →₀ ℕ)
    (G : ι → MvPolynomial σ C) :
    AddMonoidAlgebra.coeff (∏ j, MvPolynomial.rename (fun v : σ => (j, v)) (G j))
        (∑ j, Finsupp.mapDomain (fun v : σ => (j, v)) (m j)) =
      ∏ j, AddMonoidAlgebra.coeff (G j) (m j) := by
  classical
  set D := ∑ j, Finsupp.mapDomain (fun v : σ => (j, v)) (m j) with hD
  have inj : ∀ j : ι, Function.Injective (fun v : σ => (j, v)) := fun j a b h => (Prod.mk.inj h).2
  rw [coeff_prod', Finset.sum_eq_single
    (Finsupp.equivFunOnFinite.symm fun j => Finsupp.mapDomain (fun v : σ => (j, v)) (m j))]
  · refine Finset.prod_congr rfl fun j _ => ?_
    exact MvPolynomial.coeff_rename_mapDomain _ (inj j) _ _
  · intro l hl hne
    by_contra hprod
    apply hne
    have hu : ∀ k, ∃ u : σ →₀ ℕ, Finsupp.mapDomain (fun v : σ => (k, v)) u = l k := by
      intro k
      by_contra hk
      push_neg at hk
      apply hprod
      apply Finset.prod_eq_zero (Finset.mem_univ k)
      apply MvPolynomial.coeff_rename_eq_zero
      intro u hu'
      exact absurd hu' (hk u)
    choose u hu using hu
    have hsum : ∑ k, Finsupp.mapDomain (fun v : σ => (k, v)) (u k) = D := by
      rw [Finset.mem_finsuppAntidiag] at hl
      simp only [hu]
      exact hl.1
    have hum : u = m := by
      funext k
      ext x
      have hx := congrArg (fun F => F (k, x)) hsum
      simp only [hD, sum_map_apply] at hx
      exact hx
    ext1 k
    show l k = Finsupp.mapDomain (fun v : σ => (k, v)) (m k)
    rw [← hu k, hum]
  · intro h
    exfalso
    apply h
    rw [Finset.mem_finsuppAntidiag]
    refine ⟨?_, Finset.subset_univ _⟩
    show ∑ k ∈ Finset.univ, Finsupp.mapDomain (fun v : σ => (k, v)) (m k) = D
    rw [hD]

private theorem unitri {I P C : Type} [Fintype I] [PartialOrder P] [CommRing C] (S : Subring C) (e : I → P)
    (he : Function.Injective e) (A : I → I → C) (c : I → C) (hA : ∀ i j, A i j ∈ S) (h1 : ∀ i, A i i = 1)
    (hle : ∀ i j, A i j ≠ 0 → e j ≤ e i) (hc : ∀ j, ∑ i, c i * A i j ∈ S) (j : I) : c j ∈ S := by
  classical
  suffices key : ∀ n, ∀ j, (Finset.univ.filter fun i => e j < e i).card = n → c j ∈ S from key _ j rfl
  intro n
  refine Nat.strong_induction_on n fun n ih => ?_
  intro j hj
  have hrest : ∀ i ∈ Finset.univ.erase j, c i * A i j ∈ S := by
    intro i hi
    by_cases h0 : A i j = 0
    · rw [h0, mul_zero]
      exact S.zero_mem
    · have hlt : e j < e i :=
        lt_of_le_of_ne (hle i j h0) (fun h => (Finset.ne_of_mem_erase hi) (he h).symm)
      refine S.mul_mem ?_ (hA i j)
      refine ih _ ?_ i rfl
      rw [← hj]
      apply Finset.card_lt_card
      refine (Finset.ssubset_iff_of_subset ?_).mpr ⟨i, ?_, ?_⟩
      · intro k hk
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
        exact lt_trans hlt hk
      · simp [hlt]
      · simp
  have hsum := hc j
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j), h1, mul_one] at hsum
  have hfin := S.sub_mem hsum (sum_mem hrest)
  simpa using hfin

theorem UpperTheory.WildA.bvvInt :
    ∀ {ι : Type} [Fintype ι] {b : ℕ} (lam : ι → DomWeight b) (v : VV ℂ lam),
      (∀ m, ∃ z : ℤ, AddMonoidAlgebra.coeff (v : Pol ℂ ι b) m = (z : ℂ)) → ∀ i, ∃ z : ℤ, (bVV ℂ lam).repr v i = (z : ℂ) := by
  intro ι _ b lam v hv i
  classical
  let L : VVIdx lam → (ι × Fin b × Fin b →₀ ℕ) := fun j =>
    ∑ τ, Finsupp.mapDomain (fun x : Fin b × Fin b => (τ, x)) ((j τ : Fin b × Fin b →₀ ℕ))
  let A : VVIdx lam → VVIdx lam → ℂ := fun i j => AddMonoidAlgebra.coeff (bVVfun ℂ lam i) (L j)
  let e : VVIdx lam → (ι → (Formalism.GradedWeylDivisibility.colLex b b).syn) := fun i τ =>
    (Formalism.GradedWeylDivisibility.colLex b b).toSyn ((i τ : Fin b × Fin b →₀ ℕ))
  have hspec : ∀ {n : ℕ} (ν : Fin n → ℕ) (m : Formalism.GradedWeylDivisibility.ssIdx n n ν),
      (Formalism.GradedWeylDivisibility.colLex n n).degree (ssB ℂ ν m) = m ∧ (Formalism.GradedWeylDivisibility.colLex n n).leadingCoeff (ssB ℂ ν m) = 1 := by
    intro n ν m
    have h := (Formalism.L2.DIV.ssB._proof_1 ℂ ν).choose_spec.2 m
    exact ⟨h.1, h.2.1⟩
  have hAprod : ∀ i j, A i j =
      ∏ τ, AddMonoidAlgebra.coeff (ssB ℂ (lam τ).natW (i τ)) (j τ : Fin b × Fin b →₀ ℕ) := by
    intro i j
    exact coeff_prod_ren (fun τ => (j τ : Fin b × Fin b →₀ ℕ)) (fun τ => ssB ℂ (lam τ).natW (i τ))
  have hdiag : ∀ i, A i i = 1 := by
    intro i
    rw [hAprod]
    apply Finset.prod_eq_one
    intro τ _
    have h := hspec (lam τ).natW (i τ)
    simpa [MonomialOrder.leadingCoeff, h.1] using h.2
  have hexp : (v : Pol ℂ ι b) = ∑ k ∈ ((bVV ℂ lam).repr v).support,
      ((bVV ℂ lam).repr v k) • bVVfun ℂ lam k := by
    have h0 := (bVV ℂ lam).linearCombination_repr v
    rw [Finsupp.linearCombination_apply, Finsupp.sum] at h0
    conv_lhs => rw [← h0]
    rw [Submodule.coe_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Submodule.coe_smul, bVV_coe]
  by_cases hi : i ∈ ((bVV ℂ lam).repr v).support
  swap
  · simp only [Finsupp.mem_support_iff, not_not] at hi
    exact ⟨0, by simp [hi]⟩
  have key : (bVV ℂ lam).repr v i ∈ (Int.castRingHom ℂ).range := by
    refine unitri (I := {x // x ∈ ((bVV ℂ lam).repr v).support}) (Int.castRingHom ℂ).range
      (fun x => e x.1) ?_ (fun x y => A x.1 y.1) (fun x => (bVV ℂ lam).repr v x.1) ?_ ?_ ?_ ?_ ⟨i, hi⟩
    · intro x y hxy
      apply Subtype.ext
      funext τ
      apply Subtype.ext
      exact (Formalism.GradedWeylDivisibility.colLex b b).toSyn.injective (congrFun hxy τ)
    · intro x y
      obtain ⟨P, hP⟩ := bVVfun_int ℂ lam x.1
      refine RingHom.mem_range.mpr ⟨AddMonoidAlgebra.coeff P (L y.1), ?_⟩
      show _ = AddMonoidAlgebra.coeff (bVVfun ℂ lam x.1) (L y.1)
      rw [hP, MvPolynomial.coeff_map]
    · intro x
      exact hdiag x.1
    · intro x y hxy τ
      have hne : ∀ τ ∈ Finset.univ,
          AddMonoidAlgebra.coeff (ssB ℂ (lam τ).natW (x.1 τ)) (y.1 τ : Fin b × Fin b →₀ ℕ) ≠ 0 := by
        rw [← Finset.prod_ne_zero_iff, ← hAprod]
        exact hxy
      have hd := (Formalism.GradedWeylDivisibility.colLex b b).le_degree
        (MvPolynomial.mem_support_iff.mpr (hne τ (Finset.mem_univ τ)))
      rw [(hspec (lam τ).natW (x.1 τ)).1] at hd
      exact hd
    · intro j
      have hcoef : AddMonoidAlgebra.coeff (v : Pol ℂ ι b) (L j.1) =
          ∑ x : {x // x ∈ ((bVV ℂ lam).repr v).support}, (bVV ℂ lam).repr v x.1 * A x.1 j.1 := by
        rw [hexp, MvPolynomial.coeff_sum, ← Finset.sum_coe_sort]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [MvPolynomial.coeff_smul, smul_eq_mul] <;> rfl
      show ∑ x : {x // x ∈ ((bVV ℂ lam).repr v).support}, (bVV ℂ lam).repr v x.1 * A x.1 j.1 ∈ _
      rw [← hcoef]
      obtain ⟨z, hz⟩ := hv (L j.1)
      exact RingHom.mem_range.mpr ⟨z, by simp [hz]⟩
  obtain ⟨z, hz⟩ := RingHom.mem_range.mp key
  exact ⟨z, by simpa using hz.symm⟩
end

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.DepSum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

private theorem false_of_coprime_natCast_mem_heightOne {R : Type*} [CommRing R] [IsDomain R] (v : HeightOneSpectrum R)
    (a b : ℕ) (hab : Nat.Coprime a b) (ha : (a : R) ∈ v.asIdeal) (hb : (b : R) ∈ v.asIdeal) : False := by
  obtain ⟨x, y, hxy⟩ := Nat.isCoprime_iff_coprime.2 hab
  have h1 : (x : R) * a + (y : R) * b = 1 := by
    have := congrArg (Int.cast : ℤ → R) hxy
    push_cast at this
    exact this
  apply v.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← h1]
  exact add_mem (Ideal.mul_mem_left _ _ ha) (Ideal.mul_mem_left _ _ hb)

private theorem prime_le_absNorm_of_mem_heightOne (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (l : ℕ)
    (hl : l.Prime) (h : (l : 𝓞 K) ∈ v.asIdeal) : l ≤ Ideal.absNorm v.asIdeal := by
  have hN : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact v.ne_bot
  apply Nat.le_of_dvd (Nat.pos_of_ne_zero hN)
  by_contra hd
  exact false_of_coprime_natCast_mem_heightOne v l _ ((Nat.Prime.coprime_iff_not_dvd hl).2 hd) h (Ideal.absNorm_mem _)

private theorem prime_eq_of_natCast_mem_heightOne {R : Type*} [CommRing R] [IsDomain R] (v : HeightOneSpectrum R)
    (l m : ℕ) (hl : l.Prime) (hm : m.Prime) (h1 : (l : R) ∈ v.asIdeal) (h2 : (m : R) ∈ v.asIdeal) : l = m := by
  by_contra hne
  exact false_of_coprime_natCast_mem_heightOne v l m ((Nat.coprime_primes hl hm).2 hne) h1 h2

theorem UpperTheory.WildA.depSum :
    ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GlobalTheory.ChiGrid.GridData L sc}, ∃ S : Finset ℕ, GlobalTheory.NormSum.Exponents S (fun l => if l.Prime then (depL G l : ℝ) else 0) (sig G) := by
  classical
  intro D T L sc G
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ v ∈ G.pl.S0, Ideal.absNorm v.asIdeal ≤ N := by
    refine ⟨∑ v ∈ G.pl.S0, Ideal.absNorm v.asIdeal, fun v hv => ?_⟩
    exact Finset.single_le_sum (f := fun v : Pl ↥D.host.F => Ideal.absNorm v.asIdeal)
      (fun _ _ => Nat.zero_le _) hv
  obtain ⟨S, hS⟩ : ∃ S : Finset ℕ, ∀ l, l ∈ S ↔ l.Prime ∧ l ≤ N :=
    ⟨(Finset.range (N + 1)).filter Nat.Prime, fun l => by
      rw [Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff, and_comm]⟩
  have key : ∀ v ∈ G.pl.S0, ∀ l : ℕ, l.Prime → ((l : ℕ) : 𝓞 D.host.E) ∈ (G.pl.w v).asIdeal →
      l ≤ Ideal.absNorm v.asIdeal := by
    intro v hv l hl h
    apply prime_le_absNorm_of_mem_heightOne _ v l hl
    have := G.pl.w_over v hv
    rw [← this]
    simpa [IsDedekindDomain.HeightOneSpectrum.under] using h
  have hdep : ∀ l : ℕ, depL G l ≤
      ∑ v ∈ G.pl.S0.filter (fun v => ((l : ℕ) : 𝓞 D.host.E) ∈ (G.pl.w v).asIdeal), G.pl.depth sc v := by
    intro l
    unfold GlobalTheory.SumSize.depL
    apply Finset.sup_le
    intro PP hPP
    obtain ⟨hPP1, hmem⟩ := Finset.mem_filter.1 hPP
    unfold GlobalTheory.ChiGrid.Places.W0 at hPP1
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hPP1
    rw [(GlobalTheory.FunObj.depthAt_w G hv).2]
    exact Finset.single_le_sum (f := fun v => G.pl.depth sc v) (fun _ _ => Nat.zero_le _)
      (Finset.mem_filter.2 ⟨hv, hmem⟩)
  have hinner : ∀ v ∈ G.pl.S0,
      ∑ l ∈ S.filter (fun l : ℕ => ((l : ℕ) : 𝓞 D.host.E) ∈ (G.pl.w v).asIdeal), Real.log (l : ℝ) ≤
        Real.log (Ideal.absNorm v.asIdeal : ℝ) := by
    intro v hv
    rcases (S.filter (fun l : ℕ => ((l : ℕ) : 𝓞 D.host.E) ∈ (G.pl.w v).asIdeal)).eq_empty_or_nonempty
      with he | ⟨l0, hl0⟩
    · rw [he, Finset.sum_empty]
      exact Real.log_natCast_nonneg _
    · obtain ⟨hl0S, hl0P⟩ := Finset.mem_filter.1 hl0
      have hp0 : l0.Prime := ((hS l0).1 hl0S).1
      have hsub : S.filter (fun l : ℕ => ((l : ℕ) : 𝓞 D.host.E) ∈ (G.pl.w v).asIdeal) ⊆ {l0} := by
        intro m hm
        rw [Finset.mem_singleton]
        obtain ⟨hmS, hmP⟩ := Finset.mem_filter.1 hm
        exact prime_eq_of_natCast_mem_heightOne _ m l0 ((hS m).1 hmS).1 hp0 hmP hl0P
      calc _ ≤ ∑ l ∈ ({l0} : Finset ℕ), Real.log (l : ℝ) :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => Real.log_natCast_nonneg i)
        _ = Real.log (l0 : ℝ) := Finset.sum_singleton _ _
        _ ≤ _ := by
          apply Real.log_le_log (by exact_mod_cast hp0.pos)
          exact_mod_cast key v hv l0 hp0 hl0P
  refine ⟨S, ?_⟩
  unfold GlobalTheory.NormSum.Exponents
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro l hl
    exact ((hS l).1 hl).1
  · intro l
    dsimp only
    split_ifs <;> positivity
  · intro l hl
    dsimp only
    split_ifs with hp
    · have h0 : depL G l = 0 := by
        apply Nat.eq_zero_of_le_zero
        refine (hdep l).trans (le_of_eq (Finset.sum_eq_zero ?_))
        intro v hv'
        obtain ⟨hv, hmem⟩ := Finset.mem_filter.1 hv'
        exact absurd ((hS l).2 ⟨hp, (key v hv l hp hmem).trans (hN v hv)⟩) hl
      rw [h0, Nat.cast_zero]
    · rfl
  · dsimp only
    calc ∑ l ∈ S, (if l.Prime then (depL G l : ℝ) else 0) * Real.log (l : ℝ)
        ≤ ∑ l ∈ S, ∑ v ∈ G.pl.S0, (if ((l : ℕ) : 𝓞 D.host.E) ∈ (G.pl.w v).asIdeal then
            (G.pl.depth sc v : ℝ) * Real.log (l : ℝ) else 0) := by
          apply Finset.sum_le_sum
          intro l hl
          have hp : l.Prime := ((hS l).1 hl).1
          rw [if_pos hp, ← Finset.sum_filter, ← Finset.sum_mul]
          apply mul_le_mul_of_nonneg_right _ (Real.log_natCast_nonneg l)
          exact_mod_cast hdep l
      _ = ∑ v ∈ G.pl.S0, (G.pl.depth sc v : ℝ) *
            ∑ l ∈ S.filter (fun l : ℕ => ((l : ℕ) : 𝓞 D.host.E) ∈ (G.pl.w v).asIdeal), Real.log (l : ℝ) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun v _ => ?_)
          rw [Finset.mul_sum, Finset.sum_filter]
      _ ≤ ∑ v ∈ G.pl.S0, (G.pl.depth sc v : ℝ) * Real.log (Ideal.absNorm v.asIdeal : ℝ) := by
          apply Finset.sum_le_sum
          intro v hv
          exact mul_le_mul_of_nonneg_left (hinner v hv) (by positivity)
      _ = sig G := by
          unfold GlobalTheory.SumSize.sig
          rfl
end

