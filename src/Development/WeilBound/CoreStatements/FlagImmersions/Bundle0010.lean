module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0011
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Bundle0007
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Bundle0005
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0015
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0002
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE
public import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle0001
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.Bundle0001

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.FlagImmersions.EqOfSpecializesGenPt
section
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace RootFieldNumerics

section General

variable {X : Scheme.{0}} {Ω Ω' : Type} [Field Ω] [Field Ω']

theorem spMap_genMap (ξ : Spec (CommRingCat.of Ω) ⟶ X) (p : Cpt ξ) :
    Spec.map (CommRingCat.ofHom (genMap ξ p)) ≫ X.fromSpecStalk p.1 = ξ := by
  have h1 := Spec.map_comp (X.presheaf.stalkSpecializes p.2) (Scheme.stalkClosedPointTo ξ)
  have h2 := Scheme.SpecMap_stalkSpecializes_fromSpecStalk (X := X) p.2
  exact (congrArg (· ≫ X.fromSpecStalk p.1) h1).trans <| (Category.assoc _ _ _).trans <|
    (congrArg (Spec.map (Scheme.stalkClosedPointTo ξ) ≫ ·) h2).trans
      (Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ)

theorem eq_of_specializes_genPt {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    (hb : Function.Bijective (Scheme.stalkClosedPointTo ξ).hom) (x' : X) (h : x' ⤳ genPt ξ) : x' = genPt ξ := by
  have hF : IsField (X.presheaf.stalk (genPt ξ)) :=
    (RingEquiv.ofBijective _ hb).toMulEquiv.isField (Field.toIsField Ω)
  have h1 : x' ∈ Set.range (X.fromSpecStalk (genPt ξ)) := by
    rw [Scheme.range_fromSpecStalk]; exact h
  have h2 : genPt ξ ∈ Set.range (X.fromSpecStalk (genPt ξ)) := by
    rw [Scheme.range_fromSpecStalk]; exact specializes_rfl
  obtain ⟨u, hu⟩ := h1
  obtain ⟨v, hv⟩ := h2
  let _ := hF.toField
  have huv : u = v := Subsingleton.elim (α := PrimeSpectrum (X.presheaf.stalk (genPt ξ))) u v
  rw [← hu, huv, hv]

theorem exists_factor {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    (hb : Function.Bijective (Scheme.stalkClosedPointTo ξ).hom) (ξ' : Spec (CommRingCat.of Ω') ⟶ X)
    (h : genPt ξ' ⤳ genPt ξ) : ∃ φ : Ω →+* Ω', ξ' = spMap φ ≫ ξ := by
  let e := RingEquiv.ofBijective _ hb
  refine ⟨(genMap ξ' ⟨genPt ξ, h⟩).comp e.symm.toRingHom, ?_⟩
  have h1 : Scheme.stalkClosedPointTo ξ ≫
      CommRingCat.ofHom ((genMap ξ' ⟨genPt ξ, h⟩).comp e.symm.toRingHom) =
      CommRingCat.ofHom (genMap ξ' ⟨genPt ξ, h⟩) := by
    ext a
    exact congrArg (genMap ξ' ⟨genPt ξ, h⟩) (e.symm_apply_apply a)
  have h2 := spMap_genMap ξ' ⟨genPt ξ, h⟩
  have h3 := Spec.map_comp (Scheme.stalkClosedPointTo ξ)
    (CommRingCat.ofHom ((genMap ξ' ⟨genPt ξ, h⟩).comp e.symm.toRingHom))
  refine h2.symm.trans ?_
  refine (congrArg (fun u => Spec.map u ≫ X.fromSpecStalk (genPt ξ)) h1.symm).trans ?_
  refine (congrArg (· ≫ X.fromSpecStalk (genPt ξ)) h3).trans <| (Category.assoc _ _ _).trans ?_
  exact congrArg (spMap ((genMap ξ' ⟨genPt ξ, h⟩).comp e.symm.toRingHom) ≫ ·)
    (Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ)

end General

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

theorem splitComps_of_origin {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)}
    {T : Top.RootTower (CMType H) (D.p + D.q)} (o : TowerOrigin Y T) : SplitComps Y := by
  intro Ω _ ξ cst hξ hs a ha
  have : NumberField c.F := { to_charZero := inferInstance, to_finiteDimensional := c.fin }
  obtain ⟨b, hb⟩ := o.comp_onto (genPt ξ) (eq_of_specializes_genPt hξ.bij)
  obtain ⟨φ, hφ⟩ := exists_factor hξ.bij (o.Fx b).ξf (hb ▸ specializes_rfl)
  let r := o.Or 0 b
  have h1 : spMap (r.𝔐.cst.comp (algebraMap (𝓞 c.F) c.F)) =
      spMap ((r.g.comp (φ.comp cst)).comp (algebraMap (𝓞 c.F) c.F)) := by
    rw [← r.𝔐.cst_over, ← Category.assoc, r.g_over, hφ, Category.assoc, Category.assoc, hs,
      ← Spec.map_comp, ← Spec.map_comp]
    rfl
  have h2 : r.𝔐.cst.comp (algebraMap (𝓞 c.F) c.F) =
      (r.g.comp (φ.comp cst)).comp (algebraMap (𝓞 c.F) c.F) :=
    congrArg CommRingCat.Hom.hom (Spec.map_injective h1)
  have h3 : r.𝔐.cst = r.g.comp (φ.comp cst) :=
    IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 c.F)) h2
  obtain ⟨x, hx⟩ := r.g_const (φ a) (ha.algHom φ.toIntAlgHom)
  rw [h3] at hx
  exact ⟨x, φ.injective (r.g.injective hx)⟩

end RootFieldNumerics
end

-- bundled from Development.WeilBound.CoreStatements.FlagImmersions.SumFundOnRoot
section
noncomputable section

namespace RootFieldNumerics.Sq

open MvPolynomial AlgebraicGeometry CategoryTheory NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp

theorem sum_fundOnRoot {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ} {A : Type} [AddCommGroup A] (a : Ψ × Fin N)
    (f : Ψ × Fin N → A) : ∑ r, fundOnRoot a r • f r = -∑ k ∈ Finset.Iic a.2, f (a.1, k) := by
  obtain ⟨x0, k0⟩ := a
  have h : ∀ r : Ψ × Fin N, fundOnRoot (x0, k0) r • f r = if r.1 = x0 ∧ r.2 ≤ k0 then -f r else 0 := by
    intro r
    simp only [fundOnRoot]
    split_ifs <;> simp_all
  simp only [h]
  rw [Fintype.sum_prod_type, Finset.sum_eq_single x0]
  · simp only [true_and, ← Finset.sum_filter, Finset.sum_neg_distrib]
    congr 2
    ext k
    simp
  · intro x _ hx
    simp [hx]
  · intro hx
    exact absurd (Finset.mem_univ x0) hx

theorem log_combLine {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {J : Type} [Fintype J] (ℓ : J → HermLine ι)
    (n : J → ℤ) {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    Real.log ((Top.combLine ℓ n).h z) = ∑ j, n j • Real.log ((ℓ j).h z) := by
  have hpos : ∀ j, 0 < (ℓ j).h z := fun j => (ℓ j).pos z hz
  show Real.log (∏ j, (ℓ j).h z ^ n j) = _
  rw [Real.log_prod (fun j _ => (zpow_pos (hpos j) _).ne')]
  simp only [Real.log_zpow, zsmul_eq_mul]

theorem sum_root_fund {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ} (r : Ψ × Fin N) (f : Ψ × Fin N → ℝ) :
    ∑ a, rootOnFund r a • -∑ k ∈ Finset.Iic a.2, f (a.1, k) = f r := by
  obtain ⟨x0, k0⟩ := r
  rw [Fintype.sum_prod_type, Finset.sum_eq_single x0]
  rotate_left
  · intro x _ hx
    refine Finset.sum_eq_zero fun j _ => ?_
    simp [rootOnFund, hx]
  · intro h
    exact absurd (Finset.mem_univ x0) h
  have hterm : ∀ j : Fin N, rootOnFund (x0, k0) (x0, j) • -∑ k ∈ Finset.Iic j, f (x0, k) =
      (if j = k0 then ∑ k ∈ Finset.Iic j, f (x0, k) else 0) -
        (if (j : ℕ) + 1 = k0 then ∑ k ∈ Finset.Iic j, f (x0, k) else 0) := by
    intro j
    simp only [rootOnFund, if_true]
    split_ifs <;> simp
  simp only [hterm, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rcases k0 with ⟨k, hk⟩
  cases k with
  | zero =>
    have hsum : ∑ j : Fin N, (if (j : ℕ) + 1 = (0 : ℕ) then ∑ k ∈ Finset.Iic j, f (x0, k) else 0) = 0 :=
      Finset.sum_eq_zero fun j _ => if_neg (by omega)
    have hI : Finset.Iic (⟨0, hk⟩ : Fin N) = {⟨0, hk⟩} := by
      ext j
      simp only [Finset.mem_Iic, Finset.mem_singleton, Fin.le_def, Fin.ext_iff]
      omega
    simp only [Fin.val_mk] at *
    rw [hsum, sub_zero, hI, Finset.sum_singleton]
  | succ k' =>
    have hk' : k' < N := by omega
    have hsum : ∑ j : Fin N, (if (j : ℕ) + 1 = k' + 1 then ∑ k ∈ Finset.Iic j, f (x0, k) else 0) =
        ∑ k ∈ Finset.Iic (⟨k', hk'⟩ : Fin N), f (x0, k) := by
      rw [Finset.sum_eq_single ⟨k', hk'⟩]
      · simp
      · intro j _ hj
        rw [if_neg]
        intro hj'
        apply hj
        ext
        simp only [Fin.val_mk]
        omega
      · intro h
        exact absurd (Finset.mem_univ _) h
    have hI : Finset.Iic (⟨k' + 1, hk⟩ : Fin N) = insert ⟨k' + 1, hk⟩ (Finset.Iic ⟨k', hk'⟩) := by
      ext j
      simp only [Finset.mem_Iic, Finset.mem_insert, Fin.le_def, Fin.ext_iff]
      omega
    have hnot : (⟨k' + 1, hk⟩ : Fin N) ∉ Finset.Iic (⟨k', hk'⟩ : Fin N) := by
      simp [Fin.le_def]
    simp only [Fin.val_mk] at *
    rw [hsum, hI, Finset.sum_insert hnot]
    ring

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l}
  {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
  {RM : Top.RootModel (CMType H) (D.p + D.q)} {Sys : PB.AnSys (Top.dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))}
  {Fx : FixedData Y Sys}


open Classical in
def tieOf (Or : RootOrigin Y S RM Fx) (h₀ : 0 < Sys.t₀) (hvb : Or.𝔐.OmVB)
    (hd : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ NumberField.discr E → p ∈ S) (hA : AlgOver (Or.Re.comap some)) :
    HodgeTie Y S (Module.finrank ℚ c.F) RM where
  A := Or.𝔐
  Fl := Or.Fl
  e := Or.e
  roots := Or.lines
  sing := Or.sing
  sing_deg := Or.sing_deg
  hodge := Or.hodge
  Sy := Sys.comap some
  Re := Or.Re.comap some
  alg := hA
  ref_deg a := by
    refine (Or.fund_deg a.1 a.2).trans ?_
    show _ = ∑ j, _ • (Or.sing j).a
    rw [sum_fundOnRoot]
    simp only [Or.sing_deg]
  sing_eq a x hx := by
    refine Eq.trans ?_ (Or.fund_sing a.1 a.2 x hx).symm
    exact (log_combLine _ _ (Or.Re.R.mem x x (Or.Re.R.mem_U x)).1).trans (sum_fundOnRoot _ _)
  line_eq := by
    filter_upwards [Ioo_mem_nhdsGT h₀] with t ht r z hz
    refine Real.log_injOn_pos ((RM.x t r).pos z hz.1) (HermLine.pos _ z hz.1) ?_
    rw [log_combLine _ _ hz.1]
    refine Eq.trans (sum_root_fund r fun r' => Real.log ((RM.x t r').h z)).symm (Finset.sum_congr rfl fun a _ => ?_)
    exact congrArg _ (Or.fund_reg a.1 a.2 t ht.1 ht.2.le z hz).symm
  δ_eq := Or.δ_eq
  discr := hd
  ht_vb p hp := (hvb p hp).2

end RootFieldNumerics.Sq
end
end

-- bundled from Development.WeilBound.CoreStatements.FlagImmersions.TwoMulThreePowLeFactorial
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace RootFieldNumerics

open GroundTheory.Heights₂.Heights.RestTerms (RestInnerTsumBound.proof)
open GroundTheory.Heights₂.Heights.RestTerms.Elem (primeWeight primeWeight_nonneg prime_partial_le)

theorem two_mul_three_pow_le_factorial (n : ℕ) : (2 : ℝ) * 3 ^ n ≤ ((n + 2).factorial : ℝ) := by
  induction n with
  | zero => norm_num [Nat.factorial]
  | succ n ih =>
    rw [show n + 1 + 2 = (n + 2) + 1 by ring, Nat.factorial_succ]
    push_cast
    have h3 : (0 : ℝ) ≤ 2 * 3 ^ n := by positivity
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    rw [pow_succ]
    nlinarith

theorem factorial_half_power_sum_le (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 (n + 1), (if 2 ≤ k then (1 / 2 : ℝ) ^ (k - 1) / (k.factorial : ℝ) else 0) ≤
      0.3 - 0.3 * (1 / 6 : ℝ) ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), if_pos (by omega)]
    have h1 : (1 / 2 : ℝ) ^ (n + 1 + 1 - 1) / ((n + 1 + 1).factorial : ℝ) ≤ 1 / 4 * (1 / 6) ^ n := by
      have h := two_mul_three_pow_le_factorial n
      have h3 : (0 : ℝ) < 2 * 3 ^ n := by positivity
      calc (1 / 2 : ℝ) ^ (n + 1 + 1 - 1) / ((n + 1 + 1).factorial : ℝ)
          ≤ (1 / 2 : ℝ) ^ (n + 1) / (2 * 3 ^ n) :=
            div_le_div_of_nonneg_left (by positivity) h3 h
        _ = 1 / 4 * (1 / 6) ^ n := by
            rw [show (1 / 6 : ℝ) = 1 / 2 * (1 / 3) by norm_num, mul_pow, pow_succ, one_div_pow (3 : ℝ)]
            field_simp
            norm_num
    rw [pow_succ (1 / 6 : ℝ)]
    linarith

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ}

theorem rest_term_prime_bound (j p : ℕ) (fr : ℕ → Ψ ⊕ Ψ) (k : ℕ) (Q : RP Ψ N) (M : ℝ) (hp : 2 ≤ p) (hk : 2 ≤ k)
    (hM : ∀ σ, |k * degFl (pLie j (k - 1) σ * Q)| ≤ M) :
    |restTerm j p fr k Q| ≤ Real.log p * (M * (2 * ((p : ℝ) ^ k)⁻¹)) := by
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have h := (RestInnerTsumBound.proof p k (fun n => k * degFl (pLie j (k - 1) (fr n) * Q)) M hp' (by omega)
    (fun n => hM _)).2
  unfold restTerm
  rw [if_pos hk, mul_assoc, ← tsum_mul_left, abs_mul, abs_of_nonneg (Real.log_natCast_nonneg p)]
  refine mul_le_mul_of_nonneg_left ?_ (Real.log_natCast_nonneg p)
  refine le_of_eq_of_le ?_ h
  congr 2
  funext n
  rw [mul_comm (n + 1) k, pow_mul, inv_pow]
  ring

theorem rest_sum_primes_bound (j : ℕ) (bad : Finset ℕ) (frob : ℕ → Ψ → ℕ → Ψ ⊕ Ψ) (B : ℕ) (τ : Ψ) (k : ℕ) (Q : RP Ψ N)
    (M b : ℝ) (hb : 0 < b) (hB : b < B + 1) (hk : 2 ≤ k)
    (hM : ∀ σ, |k * degFl (pLie j (k - 1) σ * Q)| ≤ M) :
    |restSum j bad frob B τ k Q| ≤ M * (5.56 / b ^ (k - 1)) := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM (Sum.inl τ))
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
  set K : ℝ := M * 2 / b ^ m with hK
  have hK0 : 0 ≤ K := by positivity
  set w : ℕ → ℝ := fun i => K * (primeWeight b i / (i : ℝ) ^ 2) with hw
  have hw0 : ∀ i, 0 ≤ w i := fun i => mul_nonneg hK0 (div_nonneg (primeWeight_nonneg b i) (by positivity))
  have hpart : ∀ n, ∑ i ∈ Finset.range n, w i ≤ K * (2 * Real.log 4 / b) := fun n => by
    simp only [hw]
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (prime_partial_le b hb n) hK0
  have hws : Summable w := summable_of_sum_range_le hw0 hpart
  have hle : ∀ p : ℕ, ‖(if p.Prime ∧ B < p ∧ p ∉ bad then restTerm j p (frob p τ) (m + 2) Q else 0)‖ ≤ w p := by
    intro p
    split_ifs with h
    · have hbp : b < p := by
        have : (B : ℝ) + 1 ≤ p := by exact_mod_cast h.2.1
        linarith
      have hpw : primeWeight b p = Real.log p := by simp [primeWeight, h.1, hbp]
      have hp0 : (0 : ℝ) < p := hb.trans hbp
      have hl := Real.log_natCast_nonneg p
      rw [Real.norm_eq_abs]
      refine (rest_term_prime_bound j p _ _ Q M h.1.two_le hk hM).trans ?_
      simp only [hw, hK, hpw]
      have h1 : b ^ m ≤ (p : ℝ) ^ m := pow_le_pow_left₀ hb.le hbp.le m
      calc Real.log p * (M * (2 * ((p : ℝ) ^ (m + 2))⁻¹)) = M * 2 / (p : ℝ) ^ m * (Real.log p / (p : ℝ) ^ 2) := by
            field_simp
            ring
        _ ≤ M * 2 / b ^ m * (Real.log p / (p : ℝ) ^ 2) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            exact div_le_div_of_nonneg_left (by positivity) (by positivity) h1
    · simpa using hw0 p
  have h2 := tsum_of_norm_bounded hws.hasSum hle
  rw [Real.norm_eq_abs] at h2
  refine h2.trans ((Real.tsum_le_of_sum_range_le hw0 hpart).trans ?_)
  have h4 : 2 * Real.log 4 ≤ 2.78 := (GroundTheory.Heights₂.Heights.RestTerms.RestConstants.intersectionNumber_baseChange).1
  calc K * (2 * Real.log 4 / b) ≤ K * (2.78 / b) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right h4 hb.le) hK0
    _ = M * (5.56 / b ^ (m + 2 - 1)) := by
        rw [hK, show m + 2 - 1 = m + 1 by omega, pow_succ]
        field_simp
        ring

theorem rest_sum_total_bound : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (j : ℕ) (bad : Finset ℕ) (frob : ℕ → Ψ → ℕ → Ψ ⊕ Ψ) (u : Wt Ψ N) (g : ℝ) (B : ℕ) (Q : Ψ → ℕ → RP Ψ N), 1 ≤ j → j < N → WeightHyp j u g → bigB0 u g < B + 1 → IsDecomp (linRoot u ^ (dimFl Ψ N + 1)) Q → |∑ τ, ∑ k ∈ Finset.Icc 1 N, restSum j bad frob B τ k (Q τ k)| ≤ 2 * (((dimFl Ψ N : ℝ) + 1) * flagDeg u) * ((min j (N - j) : ℕ) * spread u) := by
  intro Ψ _ _ N j bad frob u g B Q hj hjN hW hB hQ
  have hg : 0 < g := hW.1
  have hD : 0 < flagDeg u := (_root_.GlobalTheory.CompanionTheory.Ar.Top.flagDeg_eq_weyl Ψ N u).2.1 hW.2.1
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast (show 2 ≤ N by omega)
  have hH : 0 ≤ ‖u‖ / g := by positivity
  set E : ℝ := ((dimFl Ψ N : ℝ) + 1) * flagDeg u with hE
  have hE0 : 0 ≤ E := by positivity
  set j' : ℝ := ((min j (N - j) : ℕ) : ℝ) with hj'
  have hj0 : 0 ≤ j' := Nat.cast_nonneg _
  have key : ∀ τ, |∑ k ∈ Finset.Icc 1 N, restSum j bad frob B τ k (Q τ k)| ≤
      2 * E * (j' * ((⨆ i, u τ i) - ⨅ i, u τ i)) := by
    intro τ
    have hf : (1 : ℝ) ≤ Fintype.card Ψ := by
      exact_mod_cast (Fintype.card_pos_iff.mpr ⟨τ⟩ : 0 < Fintype.card Ψ)
    set U : ℝ := (⨆ i, u τ i) - ⨅ i, u τ i with hU
    have hU0 : 0 ≤ U := by
      have a : Fin N := ⟨0, by omega⟩
      have h1 := le_ciSup (Set.finite_range (u τ)).bddAbove a
      have h2 := ciInf_le (Set.finite_range (u τ)).bddBelow a
      linarith
    set A : ℝ := N * (1 + 2 * (‖u‖ / g)) with hA
    have hA0 : 0 ≤ A := by positivity
    have hb : 0 < bigB0 u g := by unfold bigB0; positivity
    have hAb : 2 * A / bigB0 u g ≤ 1 / 2 := by
      rw [div_le_iff₀ hb, hA]
      unfold bigB0
      set H := ‖u‖ / g
      have h1 : 2 * (N : ℝ) ≤ Fintype.card Ψ * (N : ℝ) ^ 2 := by nlinarith
      nlinarith
    have hterm : ∀ k ∈ Finset.Icc 1 N, |restSum j bad frob B τ k (Q τ k)| ≤
        5.56 * (E * (j' * U)) * (if 2 ≤ k then (1 / 2 : ℝ) ^ (k - 1) / (k.factorial : ℝ) else 0) := by
      intro k hk
      split_ifs with h2
      · refine (rest_sum_primes_bound j bad frob B τ k (Q τ k) _ _ hb hB h2
          (fun σ => _root_.GlobalTheory.CompanionTheory.Ar.Top.kappa_bound_of_decomp Ψ N j u g Q hj hjN hW hQ τ σ k h2 (Finset.mem_Icc.mp hk).2)).trans ?_
        have h3 : (2 * A / bigB0 u g) ^ (k - 1) ≤ (1 / 2 : ℝ) ^ (k - 1) :=
          pow_le_pow_left₀ (by positivity) hAb _
        calc E * (j' * (2 ^ (k - 1) / (k.factorial : ℝ)) * U * A ^ (k - 1)) * (5.56 / bigB0 u g ^ (k - 1))
            = 5.56 * (E * (j' * U)) * ((2 * A / bigB0 u g) ^ (k - 1) / (k.factorial : ℝ)) := by
              rw [div_pow, mul_pow 2 A]; ring
          _ ≤ _ := by gcongr
      · simp [restSum, restTerm, h2]
    obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
    have hs := factorial_half_power_sum_le n
    have h6 : (0 : ℝ) ≤ (1 / 6 : ℝ) ^ n := by positivity
    have hX : 0 ≤ E * (j' * U) := by positivity
    refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum hterm).trans ?_)
    rw [← Finset.mul_sum]
    nlinarith
  refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun τ _ => key τ).trans (le_of_eq ?_))
  rw [spread, Finset.mul_sum, Finset.mul_sum]

end RootFieldNumerics
end

