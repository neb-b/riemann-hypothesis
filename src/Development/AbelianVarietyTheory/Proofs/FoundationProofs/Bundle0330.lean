module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryRationalConjIntersectionCardDvdInvariant
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DefiniteThetaPairTermsNormsIndependentRepresenta
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DerivationDenominatorsAndHostFieldSizes
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0329
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0039
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0009

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DefiniteThetaPairNormPadicValuationBound
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.NormVal

def Bd (p : ℕ) [Fact p.Prime] (r : ℝ) (x : ℂ) : Prop :=
  x ∈ Qbar ∧ ∀ lam : Qbar →+* ℂ_[p], ‖lamC lam x‖ ≤ r

variable {p : ℕ} [Fact p.Prime]

lemma lamC_of_mem (lam : Qbar →+* ℂ_[p]) {x : ℂ} (h : x ∈ Qbar) : lamC lam x = lam ⟨x, h⟩ := by
  unfold lamC
  rw [dite_eq_left h]

lemma Bd.zero {r : ℝ} (hr : 0 ≤ r) : Bd p r 0 := by
  refine ⟨zero_mem _, fun lam => ?_⟩
  rw [lamC_of_mem lam (zero_mem _)]
  have : (⟨0, zero_mem _⟩ : Qbar) = 0 := rfl
  rw [this, map_zero, norm_zero]
  exact hr

lemma Bd.add {r : ℝ} {x y : ℂ} (hx : Bd p r x) (hy : Bd p r y) : Bd p r (x + y) := by
  refine ⟨add_mem hx.1 hy.1, fun lam => ?_⟩
  have h1 := hx.2 lam
  have h2 := hy.2 lam
  rw [lamC_of_mem lam hx.1] at h1
  rw [lamC_of_mem lam hy.1] at h2
  rw [lamC_of_mem lam (add_mem hx.1 hy.1)]
  have : (⟨x + y, add_mem hx.1 hy.1⟩ : Qbar) = ⟨x, hx.1⟩ + ⟨y, hy.1⟩ := rfl
  rw [this, map_add (f := _)]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 h2)

lemma Bd.mul {r s : ℝ} {x y : ℂ} (hx : Bd p r x) (hy : Bd p s y) : Bd p (r * s) (x * y) := by
  refine ⟨mul_mem hx.1 hy.1, fun lam => ?_⟩
  have h1 := hx.2 lam
  have h2 := hy.2 lam
  rw [lamC_of_mem lam hx.1] at h1
  rw [lamC_of_mem lam hy.1] at h2
  rw [lamC_of_mem lam (mul_mem hx.1 hy.1)]
  have : (⟨x * y, mul_mem hx.1 hy.1⟩ : Qbar) = ⟨x, hx.1⟩ * ⟨y, hy.1⟩ := rfl
  rw [this, map_mul, norm_mul]
  exact mul_le_mul h1 h2 (norm_nonneg _) ((norm_nonneg _).trans h1)

lemma Bd.mono {r s : ℝ} {x : ℂ} (hx : Bd p r x) (h : r ≤ s) : Bd p s x :=
  ⟨hx.1, fun lam => (hx.2 lam).trans h⟩

lemma conj_mem {x : ℂ} (hx : x ∈ Qbar) : (starRingEnd ℂ) x ∈ Qbar := by
  rw [mem_algebraicClosure_iff] at hx ⊢
  exact hx.algHom ((starRingEnd ℂ).toRatAlgHom)

noncomputable def conjQ : Qbar →+* Qbar :=
  ((starRingEnd ℂ).comp (algebraMap Qbar ℂ)).codRestrict Qbar (fun x => conj_mem x.2)

lemma Bd.conj {r : ℝ} {x : ℂ} (hx : Bd p r x) : Bd p r ((starRingEnd ℂ) x) := by
  refine ⟨conj_mem hx.1, fun lam => ?_⟩
  have h1 := hx.2 (lam.comp conjQ)
  rw [lamC_of_mem _ hx.1] at h1
  rw [lamC_of_mem lam (conj_mem hx.1)]
  exact h1

lemma Bd.inv_nat {n M : ℕ} (hM : M ≠ 0) (h : n ∣ M) :
    Bd p ((p : ℝ) ^ (padicValNat p M : ℝ)) ((n : ℂ)⁻¹) := by
  have hn : n ≠ 0 := fun h0 => hM (by simpa [h0] using h)
  have hm : (n : ℂ)⁻¹ ∈ Qbar := inv_mem (natCast_mem _ n)
  refine ⟨hm, fun lam => ?_⟩
  rw [lamC_of_mem lam hm]
  have : (⟨(n : ℂ)⁻¹, hm⟩ : Qbar) = (n : Qbar)⁻¹ := by
    apply Subtype.ext
    simp
  rw [this, map_inv₀, map_natCast, norm_inv]
  have h2 : ‖(n : ℂ_[p])‖ = ‖(n : ℚ_[p])‖ := by
    rw [← map_natCast (algebraMap ℚ_[p] ℂ_[p]) n, norm_algebraMap']
  have hn' : (n : ℚ_[p]) ≠ 0 := by exact_mod_cast hn
  rw [h2, Padic.norm_eq_zpow_neg_valuation hn', Padic.valuation_natCast, zpow_neg, inv_inv,
    zpow_natCast, Real.rpow_natCast]
  have hp : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_le
  apply pow_le_pow_right₀ hp
  rw [← (by simpa only [_root_.Nat.padicValNat_def] using @_root_.multiplicity_dvd_iff_le : ∀ {p : _root_.Nat} [hp : _root_.Fact (_root_.Nat.Prime p)] {a n : _root_.Nat} (ha : a ≠ 0), p ^ n ∣ a ↔ n ≤ _root_.padicValNat p a) hM]
  simpa only [_root_.Nat.padicValNat_def] using
    (_root_.Dvd.intro_left _ (_root_.Nat.divMaxPow_mul_pow_padicValNat p n)).trans h

lemma order_dvd {f r N : ℕ} (h : r ≤ 2 * N) :
    8 ^ (2 * f * r) * (2 * (2 * f * r)).factorial ∣ 8 ^ (4 * f * N) * (8 * f * N).factorial := by
  have h1 : f * r ≤ f * (2 * N) := Nat.mul_le_mul_left _ h
  apply mul_dvd_mul
  · apply pow_dvd_pow
    nlinarith
  · apply Nat.factorial_dvd_factorial
    nlinarith

theorem norm_mem_and_le : ∀ (D : D7), Inp D → ∀ (S : Finset ℕ) (dl : ℕ → ℝ), Letters D S dl → ∀ (δ t0 : ℂ) (Q : ℕ), Crv D ⊤ δ → GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D ⊤ δ) t0 → GoodLevel D Q → ∀ (P : Pair D ⊤ δ t0 Q) (N : ℕ) (B : ℝ), P.Small N B → ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), ((P.norm : ℝ) : ℂ) ∈ Qbar ∧ ‖lamC lam ((P.norm : ℝ) : ℂ)‖ ≤ (p : ℝ) ^ (3 * ((padicValNat p (8 ^ (4 * fF D * N) * (8 * fF D * N).factorial) : ℝ) + 4 * fF D * N * B * (dl p + (if p = D.host.d then 1 / 4 else 0) + (padicValNat p Q : ℝ)) + 4 * (N : ℝ) ^ 2 * (padicValNat p Q : ℝ))) := by
  intro D hI S dl hL δ t0 Q hC hT hQ P N B hS p _ lam
  set M : ℕ := 8 ^ (4 * fF D * N) * (8 * fF D * N).factorial with hMdef
  have hM : M ≠ 0 := by positivity
  set c : ℝ := dl p + (if p = D.host.d then 1 / 4 else 0) + (padicValNat p Q : ℝ) with hc
  set v : ℝ := (padicValNat p M : ℝ) with hv
  set w : ℝ := (padicValNat p Q : ℝ) with hw
  have hw0 : 0 ≤ w := Nat.cast_nonneg _
  have hv0 : 0 ≤ v := Nat.cast_nonneg _
  have hc0 : 0 ≤ c := by
    have := hL.2.1 p
    have h2 : (0 : ℝ) ≤ (if p = D.host.d then 1 / 4 else 0) := by split_ifs <;> norm_num
    rw [hc]
    linarith
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_le
  have hp0 : (0 : ℝ) < p := by linarith
  set e : ℝ := ((P.a * ∑ τ, P.n τ : ℕ) : ℝ) * c + ((P.a * P.d : ℕ) : ℝ) * w with he
  have he0 : 0 ≤ e := by positivity
  have ha : P.a ≤ 2 * N := P.a_le.trans hS.1
  have heE : e ≤ 4 * fF D * N * B * c + 4 * (N : ℝ) ^ 2 * w := by
    have hcard := (_root_.GlobalTheory.NormSum.letters_and_sizes D hI.g1).2.2.2.2.1
    have h1 : ((∑ τ, P.n τ : ℕ) : ℝ) ≤ fF D * (2 * B) := by
      rw [Nat.cast_sum, ← hcard]
      have := Finset.sum_le_card_nsmul Finset.univ (fun τ => (P.n τ : ℝ)) (2 * B)
        (fun τ _ => hS.2 τ)
      simpa using this
    have haR : (P.a : ℝ) ≤ 2 * N := by exact_mod_cast ha
    have hdR : (P.d : ℝ) ≤ 2 * N := by exact_mod_cast hS.1
    have h2 : ((P.a * ∑ τ, P.n τ : ℕ) : ℝ) ≤ 4 * fF D * N * B := by
      rw [Nat.cast_mul]
      calc (P.a : ℝ) * ((∑ τ, P.n τ : ℕ) : ℝ) ≤ (2 * N) * (fF D * (2 * B)) :=
            mul_le_mul haR h1 (Nat.cast_nonneg _) (by positivity)
        _ = _ := by ring
    have h3 : ((P.a * P.d : ℕ) : ℝ) ≤ 4 * (N : ℝ) ^ 2 := by
      rw [Nat.cast_mul]
      calc (P.a : ℝ) * (P.d : ℝ) ≤ (2 * N) * (2 * N) :=
            mul_le_mul haR hdR (Nat.cast_nonneg _) (by positivity)
        _ = _ := by ring
    exact add_le_add (mul_le_mul_of_nonneg_right h2 hc0) (mul_le_mul_of_nonneg_right h3 hw0)
  obtain ⟨hterm, hsq, -⟩ := _root_.GlobalTheory.NormSum.RepInv.rep_indep D hI ⊤ δ t0 Q hC hT P hQ.1
  have hgam : ∀ (r : ℕ), r ≤ 2 * N → ∀ (J : Subgroup (GA D r)), J ≤ intG D r → ∀ g,
      Bd p ((p : ℝ) ^ v) ((gam D J g : ℂ)⁻¹) := fun r hr J hJ g =>
    Bd.inv_nat hM ((_root_.GlobalTheory.StabOrder.gam_ne_zero_dvd_invariant D r J hJ g).2.1.trans (order_dvd hr))
  have hcoord : ∀ (h k' : GA D P.d), k' ∈ intG D P.d →
      TrivAt D p ((h * k' : GA D P.d) : GL (Fin P.d) (AE D)) → ∀ T,
      Bd p ((p : ℝ) ^ v * (p : ℝ) ^ e) (P.coord h T) := by
    intro h k' hk' htr T
    unfold Pair.coord
    refine finsum_induction (Bd p ((p : ℝ) ^ v * (p : ℝ) ^ e)) (Bd.zero (by positivity))
      (fun x y => Bd.add) (fun x => ?_)
    refine Bd.mul (hgam _ ha _ le_rfl _) ?_
    obtain ⟨γ, k, γ', h1, h2, h3⟩ := hI.rep P.a p Fact.out x.out
    rw [← hterm γ (Subgroup.subset_closure ⟨γ', h1⟩) k (Subgroup.subset_closure h2)]
    exact ⟨(_root_.GlobalTheory.NormSum.Term.term_bound D hI S dl hL δ t0 Q hC hT hQ P p lam _ h k' hk' h3 htr T).1,
      fun lam' => (_root_.GlobalTheory.NormSum.Term.term_bound D hI S dl hL δ t0 Q hC hT hQ P p lam' _ h k' hk' h3 htr T).2⟩
  have hsqb : ∀ h : GA D P.d,
      Bd p (((p : ℝ) ^ v * (p : ℝ) ^ e) * ((p : ℝ) ^ v * (p : ℝ) ^ e)) ((P.sq h : ℝ) : ℂ) := by
    intro h
    obtain ⟨γ, k, γ', h1, h2, h3⟩ := hI.rep P.d p Fact.out h
    rw [← hsq γ (Subgroup.subset_closure ⟨γ', h1⟩) 1 (one_mem _) h, mul_one]
    unfold Pair.sq
    rw [Complex.ofReal_sum]
    refine Finset.sum_induction _ _ (fun x y => Bd.add) (Bd.zero (by positivity)) (fun T _ => ?_)
    have hb := hcoord (γ * h) k (Subgroup.subset_closure h2) h3 T
    rw [Complex.ofReal_pow, ← Complex.mul_conj']
    exact hb.mul hb.conj
  have hfin : Bd p ((p : ℝ) ^ v * (((p : ℝ) ^ v * (p : ℝ) ^ e) * ((p : ℝ) ^ v * (p : ℝ) ^ e)))
      ((P.norm : ℝ) : ℂ) := by
    unfold Pair.norm
    refine finsum_induction (fun x : ℝ => Bd p ((p : ℝ) ^ v * (((p : ℝ) ^ v * (p : ℝ) ^ e) *
      ((p : ℝ) ^ v * (p : ℝ) ^ e))) (x : ℂ)) ?_ (fun x y hx hy => ?_) (fun x => ?_)
    · rw [Complex.ofReal_zero]
      exact Bd.zero (by positivity)
    · rw [Complex.ofReal_add]
      exact hx.add hy
    · rw [Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_natCast]
      exact (hgam _ hS.1 _ P.J_le _).mul (hsqb _)
  refine ⟨hfin.1, (hfin.2 lam).trans ?_⟩
  rw [← Real.rpow_add hp0, ← Real.rpow_add hp0, ← Real.rpow_add hp0]
  apply Real.rpow_le_rpow_of_exponent_le hp1
  linarith

end GlobalTheory.NormVal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdemAtEqOneIff
section
noncomputable section

namespace GlobalTheory.FlatLine.Definite

open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.Frames

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem exists_bc {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T)
    (y : FrPt Xo c S) : ∃ z, FrMap φ y z :=
  GlobalTheory.Frames.FramedBaseChange.exists_frMap GlobalTheory.abelianSchemeLaws_all.1.secBaseChange E H Dw l Xo c S T φ y

theorem frMap_of_comp {R S T : Type} [CommRing R] [Algebra c.F R] [CommRing S] [Algebra c.F S] [CommRing T]
    [Algebra c.F T] {φ : R →ₐ[c.F] S} {ψ : S →ₐ[c.F] T} {χ : R →ₐ[c.F] T} (h : ψ.comp φ = χ) {y : FrPt Xo c R}
    {z : FrPt Xo c S} {w : FrPt Xo c T} (hz : FrMap φ y z) (hw : FrMap χ y w) : FrMap ψ z w := by
  obtain ⟨w', hw'⟩ := exists_bc ψ z
  rwa [(frMap_unique_refl_iff E H Dw l Xo c R T χ y).1 w w' hw (h ▸ ReciprocityTheory.ChartRestriction.G.PullbackSections.frMap_trans _ _ hz hw')]

abbrev idemAt (Z : Comp Xo c) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) : S :=
  CompSplitPfB.cspB_idem _ (CompSplitPfB.cspB_isClopen (CompSplitPfD.cspD_comp_disj Xo c) Z) y.x y.x_over

theorem idemAt_eq_one_iff (Z : Comp Xo c) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) :
    idemAt Z y = 1 ↔ LiesOn Z y := by
  refine ⟨fun h q => (CompSplitPfB.cspB_idem_spec _
    (CompSplitPfB.cspB_isClopen (CompSplitPfD.cspD_comp_disj Xo c) Z) y.x y.x_over q).1 ?_, fun h => ?_⟩
  · show idemAt Z y ∉ _
    rw [h]
    exact (Ideal.ne_top_iff_one _).1 q.isPrime.ne_top
  · refine CompSplitPfB.cspB_idem_eq_of (CompSplitPfB.cspB_idem_idem _ _ _ _) IsIdempotentElem.one fun q => ?_
    rw [CompSplitPfB.cspB_idem_spec]
    exact iff_of_true (h q) ((Ideal.ne_top_iff_one _).1 q.isPrime.ne_top)

def IsCoef (Z : Comp Xo c) (y₀ : FrPt Xo c c.F) (τ : E →+* ℂ) {S : Type} [CommRing S] [Algebra c.F S]
    (y : FrPt Xo c S) (s : S) : Prop :=
  idemAt Z y * s = s ∧ ∀ (T : Type) [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T) (w z : FrPt Xo c T)
    (g : (∀ ρ : E →+* ℂ, Matrix (Fin (Dw.mult ρ)) (Fin (Dw.mult ρ)) T)) (a : T),
    FrMap φ y w → FrMap (Algebra.ofId c.F T) y₀ z → FrChg g a w z → φ s = (g τ).det

theorem eq_of_mk_eq {S : Type} [CommRing S] {e s t : S} (he : IsIdempotentElem e) (hs : e * s = s) (ht : e * t = t)
    (h : Ideal.Quotient.mk (Ideal.span {1 - e}) s = Ideal.Quotient.mk (Ideal.span {1 - e}) t) : s = t := by
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq.1 h)
  have := he.eq
  linear_combination ht - hs - e * hb - b * this

theorem exists_isCoef {Z : Comp Xo c} {y₀ : FrPt Xo c c.F} (h₀ : LiesOn Z y₀)
    (hy₀ : ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S), LiesOn Z y →
      y.x = spMap (algebraMap c.F S) ≫ y₀.x) (τ : E →+* ℂ) {S : Type} [CommRing S] [Algebra c.F S]
    (y : FrPt Xo c S) : ∃ s s' : S, IsCoef Z y₀ τ y s ∧ (∀ t, IsCoef Z y₀ τ y t → t = s) ∧
      idemAt Z y * s' = s' ∧ s * s' = idemAt Z y := by
  have he : IsIdempotentElem (idemAt Z y) := CompSplitPfB.cspB_idem_idem _ _ _ _
  let π := Ideal.Quotient.mkₐ c.F (Ideal.span {1 - idemAt Z y})
  have hπ : π (idemAt Z y) = 1 := by
    rw [← map_one π]
    exact (Ideal.Quotient.eq.2 (Ideal.mem_span_singleton_self _)).symm
  obtain ⟨w, hw⟩ := exists_bc π y
  obtain ⟨z, hz⟩ := exists_bc (Algebra.ofId c.F (S ⧸ Ideal.span {1 - idemAt Z y})) y₀
  have hwZ : LiesOn Z w := (idemAt_eq_one_iff Z w).1
    ((CompSplitPfB.cspB_idem_map _ _ π y.x_over w.x_over hw.1).symm.trans hπ)
  obtain ⟨g, a, hg, hc⟩ := (frChg_exists_unique E H Dw l Xo c _ w z).1 (hz.1.trans (hy₀ _ w hwZ).symm)
  obtain ⟨d', hd'⟩ := (hg τ).exists_right_inv
  obtain ⟨s, hs⟩ := Ideal.Quotient.mkₐ_surjective c.F _ (g τ).det
  obtain ⟨s', hs'⟩ := Ideal.Quotient.mkₐ_surjective c.F _ d'
  have k : ∀ t, idemAt Z y * (idemAt Z y * t) = idemAt Z y * t := fun t => by rw [← mul_assoc, he.eq]
  have hs₁ : π (idemAt Z y * s) = (g τ).det := by rw [map_mul, hπ, one_mul]; exact hs
  have hs₂ : π (idemAt Z y * s') = d' := by rw [map_mul, hπ, one_mul]; exact hs'
  refine ⟨idemAt Z y * s, idemAt Z y * s', ⟨k s, fun T _ _ φ w' z' g' a' hw' hz' hc' => ?_⟩,
    fun t ht => eq_of_mk_eq he ht.1 (k s) ((ht.2 _ π w z g a hw hz hc).trans hs₁.symm), k s',
    eq_of_mk_eq he (by rw [← mul_assoc, k]) he.eq ?_⟩
  · have h1 : φ (idemAt Z y) = 1 := (CompSplitPfB.cspB_idem_map _ _ φ y.x_over w'.x_over hw'.1).trans
      ((CompSplitPfB.cspB_idem_congr _ _ z'.x_over w'.x_over hc'.1.symm).trans
        ((idemAt_eq_one_iff Z z').2 (liesOn_frMap hz' h₀)))
    let ψ := Ideal.Quotient.liftₐ (Ideal.span {1 - idemAt Z y}) φ fun b hb => by
      obtain ⟨b', rfl⟩ := Ideal.mem_span_singleton'.1 hb
      rw [map_mul, map_sub, h1, map_one, sub_self, mul_zero]
    have hψ : ψ.comp π = φ := Ideal.Quotient.liftₐ_comp _ _ _
    have c₁ := (ChgBC.frChg_baseChange E H Dw l Xo c _ T ψ w z w' z' g a hc (frMap_of_comp hψ hw hw')).1
      (frMap_of_comp (Subsingleton.elim _ _) hz hz')
    rw [((frChg_exists_unique E H Dw l Xo c T w' z').2 _ _ _ _ hc' c₁).1, ← hψ, AlgHom.comp_apply, hs₁]
    exact ψ.toRingHom.map_det (g τ)
  · show π _ = π _
    rw [map_mul, hs₁, hs₂, hd', hπ]

theorem prod_exOf_flatWt (hq : Dw.q = 0) (τ : Psi H) {G : Type} [CommGroup G] (t : Ix Dw → G) :
    ∏ i, t i ^ exOf Dw (flatWt Dw τ) 0 i = (∏ i, t (some ⟨τ.1, i⟩))⁻¹ := by
  have h : ∀ (ρ : E →+* ℂ) (i : Fin (Dw.mult ρ)),
      exOf Dw (flatWt Dw τ) 0 (some ⟨ρ, i⟩) = open Classical in if ρ = τ.1 then -1 else 0 := fun ρ i => by
    have hi := i.2
    have hρ : ρ (H.rt : E) = H.rt0 := by
      by_contra hn
      simp [Datum.mult, hn, hq] at hi
    refine (wtOf_big (flatWt Dw τ) 0 ⟨ρ, hρ⟩ i (by simpa [Datum.mult, hρ] using hi)).trans ?_
    simp only [flatWt, parWt, sub_zero]
    by_cases h1 : ρ = τ.1
    · rw [if_pos h1, if_pos (Subtype.ext h1)]
    · rw [if_neg h1, if_neg fun h2 => h1 (congrArg Subtype.val h2)]
  have h0 : exOf Dw (flatWt Dw τ) 0 none = 0 := rfl
  rw [Fintype.prod_option, h0, zpow_zero, one_mul, Fintype.prod_sigma, Finset.prod_eq_single τ.1
    (fun ρ _ hρ => by simp [h, hρ]) (by simp)]
  simp [h]

theorem inv_mem_secZ_on {Z : Comp Xo c} {e : Ix Dw → ℤ} {f f' : Rul Xo c} (hf : f ∈ secZ Xo c e)
    (h1 : idem Z * f' = f') (h2 : f * f' = idem Z) : f' ∈ secZ Xo c (-e) := by
  have k1 : ∀ p y, idem Z p y * f' p y = f' p y := fun p y => congrFun (congrFun h1 p) y
  have k2 : ∀ p y, f p y * f' p y = idem Z p y := fun p y => congrFun (congrFun h2 p) y
  have hi := idem_mem_secZ Z
  refine ⟨fun p q φ y z h => ?_, fun p t y y' h => ?_⟩
  · have a1 := congrArg φ (k1 p y)
    have a2 := congrArg φ (k2 p y)
    rw [map_mul, ← hi.1 p q φ y z h] at a1
    rw [map_mul, ← hi.1 p q φ y z h, ← hf.1 p q φ y z h] at a2
    linear_combination a1 - k1 q z - f' q z * a2 + φ (f' p y) * k2 q z
  · have a1 := k2 p y'
    have a0 : idem Z p y' = idem Z p y := by simpa using hi.2 p t y y' h
    have a4 := k1 p y'
    rw [hf.2 p t y y' h, a0] at a1
    rw [a0] at a4
    have a3 : ((∏ i, t i ^ (-e) i : (p.R)ˣ) : p.R) * ((∏ i, t i ^ e i : (p.R)ˣ) : p.R) = 1 := by
      rw [← Units.val_mul, ← Finset.prod_mul_distrib]; simp
    generalize ((∏ i, t i ^ (-e) i : (p.R)ˣ) : p.R) = A at *
    generalize ((∏ i, t i ^ e i : (p.R)ˣ) : p.R) = B at *
    linear_combination A * f' p y * a1 - a4 - f' p y' * k2 p y + A * k1 p y - f p y * f' p y * f' p y' * a3

theorem exists_flatRule : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), Dw.q = 0 → ∀ (Z : Comp Xo c) (τ : Psi H) (y₀ : FrPt Xo c c.F), LiesOn Z y₀ → (∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S), LiesOn Z y → y.x = spMap (algebraMap c.F S) ≫ y₀.x) → ∃ f f' : Rul Xo c, f ∈ secZ Xo c (exOf Dw (flatWt Dw τ) 0) ∧ f' ∈ secZ Xo c (-exOf Dw (flatWt Dw τ) 0) ∧ idem Z * f = f ∧ idem Z * f' = f' ∧ f * f' = idem Z ∧ ∀ (S : Type) [CommRing S] [Algebra c.F S] (y z : FrPt Xo c S) (g : (∀ ρ : E →+* ℂ, Matrix (Fin (Dw.mult ρ)) (Fin (Dw.mult ρ)) S)) (a : S), Tested y → FrMap (Algebra.ofId c.F S) y₀ z → FrChg g a y z → evR Xo c f y = (g τ.1).det := by
  intro E _ _ _ H Dw l Xo c hq Z τ y₀ h₀ hy₀
  choose f f' hf hu h1 h2 using fun (p : TRing c.F) (y : FrPt Xo c p.R) => exists_isCoef h₀ hy₀ τ.1 y
  have i1 : idem Z * f' = f' := funext fun p => funext fun y => h1 p y
  have i2 : (f : Rul Xo c) * f' = idem Z := funext fun p => funext fun y => h2 p y
  have hm : f ∈ secZ Xo c (exOf Dw (flatWt Dw τ) 0) := by
    refine ⟨fun p q φ y z h => (hu q z _ ⟨?_, fun T _ _ ψ w z' g a hw hz hc => ?_⟩).symm,
      fun p t y y' h => (hu p y' _ ⟨?_, fun T _ _ ψ w' z' g a hw hz hc => ?_⟩).symm⟩
    · rw [idemAt, ← CompSplitPfB.cspB_idem_map _ _ φ y.x_over z.x_over h.1, ← map_mul]
      exact congrArg φ (hf p y).1
    · exact (hf p y).2 T (ψ.comp φ) w z' g a (ReciprocityTheory.ChartRestriction.G.PullbackSections.frMap_trans _ _ h hw) hz hc
    · rw [mul_left_comm, idemAt, CompSplitPfB.cspB_idem_congr _ _ y.x_over y'.x_over h.1]
      exact congrArg _ (hf p y).1
    · obtain ⟨k, k0, k1, hk⟩ := ((frBor_calculus E H Dw l Xo c _ y y' y').1 t).1 h
      obtain ⟨w, hw₀⟩ := exists_bc ψ y
      have c₁ := (ChgBC.frChg_baseChange E H Dw l Xo c _ T ψ y y' w w' k _ hk hw₀).1 hw
      have c₂ := (frChg_refl_and_comp E H Dw l Xo c T w w' z').2 _ _ _ _ c₁ hc
      have hd : (k τ.1).det = ((∏ i, t (some ⟨τ.1, i⟩) : (p.R)ˣ) : p.R) := by
        rw [Matrix.det_of_isLowerTriangular _ (fun i j hij => k0 τ.1 i j hij), Units.coe_prod]
        exact Finset.prod_congr rfl fun i _ => k1 τ.1 i
      have hd' : ((k τ.1).map ψ).det = ψ (k τ.1).det := (ψ.toRingHom.map_det (k τ.1)).symm
      rw [map_mul, (hf p y).2 T ψ w z' _ _ hw₀ hz c₂, Matrix.det_mul, hd', hd, prod_exOf_flatWt hq, mul_left_comm,
        ← map_mul, Units.inv_mul, map_one, mul_one]
  refine ⟨f, f', hm, inv_mem_secZ_on hm i1 i2, funext fun p => funext fun y => (hf p y).1, i1, i2,
    fun S _ _ y z g a ht hz hc => ?_⟩
  unfold evR evalAt
  rw [dite_eq_left ht]
  exact (hf _ _).2 S _ y z g a ht.choose_spec.choose_spec.choose_spec hz hc

end GlobalTheory.FlatLine.Definite
end
end

