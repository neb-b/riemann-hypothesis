module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0036
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.HasMultiplier
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.TowerOrigin
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.SumFundCoMulSumIic
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0043
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0114
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0097
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularizedWeightTendstoC2
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0009
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Objects
public import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0038
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0043

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.MemOpenOfForms
section
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Small.Fund
open AlgebraicGeometry CategoryTheory

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Small.FormsVal

section Val

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {z : Spec (CommRingCat.of ℂ) ⟶ X}

def valRing (ξ : Spec (CommRingCat.of Ω) ⟶ X) (z : Spec (CommRingCat.of ℂ) ⟶ X) (h : genPt ξ ⤳ centre z) :
    Subring (Ω × ℂ) :=
  ((genMap ξ ⟨centre z, h⟩).prod (Scheme.stalkClosedPointTo z).hom).range

theorem mem_valRing_of_valAt (h : genPt ξ ⤳ centre z) {a : Ω} {r : ℂ} (hv : ValAt ξ z a r) :
    (a, r) ∈ valRing ξ z h := by
  obtain ⟨h', s, hs, hr⟩ := hv
  exact ⟨s, Prod.ext hs hr⟩

theorem aeval_mem_valRing (h : genPt ξ ⤳ centre z) {σ : Type} {a : σ → Ω} {r : σ → ℂ}
    (hv : ∀ i, (a i, r i) ∈ valRing ξ z h) (f : MvPolynomial σ ℤ) :
    (aeval a f, aeval r f) ∈ valRing ξ z h := by
  induction f using MvPolynomial.induction_on with
  | C n =>
    have e : (aeval a (C n : MvPolynomial σ ℤ), aeval r (C n : MvPolynomial σ ℤ)) = ((n : Ω × ℂ)) :=
      Prod.ext (by simp) (by simp)
    rw [e]
    exact intCast_mem _ n
  | add f g hf hg =>
    have := add_mem hf hg
    simpa using this
  | mul_X f i hf =>
    have := mul_mem hf (hv i)
    simpa using this

theorem unitAt_of_mem_valRing (h : genPt ξ ⤳ centre z) {a : Ω} {r : ℂ} (hv : (a, r) ∈ valRing ξ z h) (hr : r ≠ 0) :
    unitAt ξ ⟨centre z, h⟩ a := by
  obtain ⟨s, hs⟩ := hv
  have hs1 : genMap ξ ⟨centre z, h⟩ s = a := congrArg Prod.fst hs
  have hs2 : (Scheme.stalkClosedPointTo z).hom s = r := congrArg Prod.snd hs
  have hl : IsLocalHom (Scheme.stalkClosedPointTo z).hom := Scheme.isLocalHom_stalkClosedPointTo z
  have hu : IsUnit s := hl.map_nonunit s ((congrArg IsUnit hs2).mpr hr.isUnit)
  obtain ⟨t, ht⟩ := hu.exists_right_inv
  have h1 : a * genMap ξ ⟨centre z, h⟩ t = 1 := by rw [← hs1, ← map_mul, ht, map_one]
  have ha0 : a ≠ 0 := left_ne_zero_of_mul_eq_one h1
  exact ⟨ha0, ⟨s, hs1⟩, ⟨t, eq_inv_of_mul_eq_one_right h1⟩⟩

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {y : (Σ k, ι k) → Ω}
  {w : (Σ k, ι k) → ℂ}

theorem ratio_mem_valRing (h : genPt ξ ⤳ centre z) (hc : CoordsAt ξ y z w) (c : (k : K) → ι k)
    (hu : ∀ k, w ⟨k, c k⟩ ≠ 0) (p : Σ k, ι k) :
    ((y ⟨p.1, c p.1⟩)⁻¹ * y p, (w ⟨p.1, c p.1⟩)⁻¹ * w p) ∈ valRing ξ z h := by
  obtain ⟨k, i⟩ := p
  obtain ⟨-, hr⟩ := hc.2 k (c k) (hu k).isUnit
  obtain ⟨r, hv, hw⟩ := hr i
  have e1 : (w ⟨k, c k⟩)⁻¹ * w ⟨k, i⟩ = r := by rw [hw]; field_simp [hu k]
  have e2 : (y ⟨k, c k⟩)⁻¹ * y ⟨k, i⟩ = y ⟨k, i⟩ / y ⟨k, c k⟩ := by rw [div_eq_mul_inv, mul_comm]
  show ((y ⟨k, c k⟩)⁻¹ * y ⟨k, i⟩, (w ⟨k, c k⟩)⁻¹ * w ⟨k, i⟩) ∈ _
  rw [e1, e2]
  exact mem_valRing_of_valAt h hv

theorem unitAt_form (h : genPt ξ ⤳ centre z) (hc : CoordsAt ξ y z w) (c : (k : K) → ι k)
    (hu : ∀ k, w ⟨k, c k⟩ ≠ 0) {G : MRing ι} {d : K → ℕ} (hG : IsMultiHomog G d) (hw : aeval w G ≠ 0) :
    unitAt ξ ⟨centre z, h⟩ (aeval y G / ∏ k, y ⟨k, c k⟩ ^ d k) := by
  have hm := aeval_mem_valRing h (ratio_mem_valRing h hc c hu) G
  rw [aeval_scale hG (fun k => (y ⟨k, c k⟩)⁻¹) y, aeval_scale hG (fun k => (w ⟨k, c k⟩)⁻¹) w] at hm
  have e : (∏ k, (y ⟨k, c k⟩)⁻¹ ^ d k) * aeval y G = aeval y G / ∏ k, y ⟨k, c k⟩ ^ d k := by
    simp only [inv_pow, Finset.prod_inv_distrib]
    rw [div_eq_mul_inv, mul_comm]
  rw [e] at hm
  refine unitAt_of_mem_valRing h hm (mul_ne_zero ?_ hw)
  exact Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (inv_ne_zero (hu k))

end Val

section Field

variable {Ω : Type} [Field Ω]

theorem zpow_sum_eq_prod_zpow {R : Type} (Y : Ω) (hY : Y ≠ 0) (s : Finset R) (f : R → ℤ) :
    Y ^ (∑ r ∈ s, f r) = ∏ r ∈ s, Y ^ f r := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert r s hr ih => rw [Finset.sum_insert hr, Finset.prod_insert hr, zpow_add₀ hY, ih]

theorem mono_identity {K R : Type} [Fintype K] [Fintype R] (Y : K → Ω) (hY : ∀ k, Y k ≠ 0) (e : R → Ω)
    (he : ∀ r, e r ≠ 0) (x : R → K → ℤ) (Aa : K → ℤ) (n : R → ℤ) (q : ℕ) (k₀ : K)
    (hA : Aa k₀ = 1 ∧ ∀ k, k ≠ k₀ → Aa k = 0) (a : K → ℤ)
    (ha : ∀ k, a k = -(q : ℤ) * Aa k + ∑ r, -n r * x r k) :
    (∏ k, Y k ^ a k)⁻¹ * ∏ r, e r ^ n r = Y k₀ ^ q / ∏ r, ((∏ k, Y k ^ x r k) • e r) ^ (-n r) := by
  classical
  have h1 : ∏ k, Y k ^ Aa k = Y k₀ := by
    rw [Finset.prod_eq_single k₀ (fun k _ hk => by rw [hA.2 k hk, zpow_zero]) (by simp), hA.1, zpow_one]
  have h2 : ∏ k, Y k ^ a k = (Y k₀ ^ q)⁻¹ * ∏ r, (∏ k, Y k ^ x r k) ^ (-n r) := by
    have e1 : ∀ k, Y k ^ a k = (Y k ^ Aa k) ^ (-(q : ℤ)) * ∏ r, (Y k ^ x r k) ^ (-n r) := fun k => by
      rw [ha k, zpow_add₀ (hY k), zpow_sum_eq_prod_zpow _ (hY k), ← zpow_mul, mul_comm (Aa k)]
      congr 1
      refine Finset.prod_congr rfl fun r _ => ?_
      rw [← zpow_mul, mul_comm (x r k)]
    simp only [e1, Finset.prod_mul_distrib]
    rw [Finset.prod_comm]
    congr 1
    · rw [Finset.prod_zpow, h1, zpow_neg, zpow_natCast]
    · refine Finset.prod_congr rfl fun r _ => ?_
      rw [Finset.prod_zpow]
  have h3 : ∏ r, ((∏ k, Y k ^ x r k) • e r) ^ (-n r) =
      (∏ r, (∏ k, Y k ^ x r k) ^ (-n r)) * (∏ r, e r ^ n r)⁻¹ := by
    rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun r _ => ?_
    rw [smul_eq_mul, mul_zpow, zpow_neg (e r)]
  have h4 : ∏ r, (∏ k, Y k ^ x r k) ^ (-n r) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun r _ => zpow_ne_zero _
      (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hY k))
  have h5 : ∏ r, e r ^ n r ≠ 0 := Finset.prod_ne_zero_iff.2 fun r _ => zpow_ne_zero _ (he r)
  have h6 : Y k₀ ^ q ≠ 0 := pow_ne_zero _ (hY k₀)
  rw [h2, h3]
  field_simp

end Field

theorem mem_open_of_forms : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (RM : RootModel (CMType H) (D.p + D.q)) (Sys : PB.AnSys (dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))) (Fx : FixedData Y Sys) (Or : RootOrigin Y S RM Fx) (n₀ : Option (RootIx D) → ℤ) (N₀ : ℕ), (∀ r, n₀ (some r) = -Fx.n r) → n₀ none = -(Fx.q' : ℤ) → ((N₀ : RM.Ω) * Or.g Fx.sE * ∏ r, Or.e r ^ Fx.n r) ≠ 0 → ∀ (x : Or.Re.R.X) (dg dh : RM.K → ℕ) (G Hf : MRing RM.ι), IsMultiHomog G dg → IsMultiHomog Hf dh → (∀ k, (dg k : ℤ) = dh k + (combLine (RM.line 1) n₀).a k) → aeval RM.y G = ((N₀ : RM.Ω) * Or.g Fx.sE * ∏ r, Or.e r ^ Fx.n r) * aeval RM.y Hf → aeval (Or.Re.R.lift x x) G ≠ 0 → aeval (Or.Re.R.lift x x) Hf ≠ 0 → Or.Re.π x ∈ Sys.open' := by
  intro E _ _ _ H D l Xo c O _ β Y S RM Sys Fx Or n₀ N₀ hn hnone hε x dg dh G Hf hG hH hdeg hy hwG hwH
  classical
  have hmem : Or.Re.R.lift x x ∈ mcPts (mCoordIdeal RM.y) := Or.Re.R.mem x x (Or.Re.R.mem_U x)
  obtain ⟨z, hz, hc⟩ := (mem_mcPts_iff_exists_coordsAt _ _ Or.𝔐.ξ _ _ RM.y Or.𝔐.tie _).1 hmem
  refine (Or.interior x z hc).1 ?_
  by_contra hnab
  choose b hb using hc.1
  have hbw : ∀ k, Or.Re.R.lift x x ⟨k, b k⟩ ≠ 0 := fun k => (hb k).ne_zero
  let p : Cpt Or.𝔐.ξ := ⟨centre z, hz⟩
  have hyc : ∀ k, RM.y ⟨k, b k⟩ ≠ 0 := fun k => (hc.2 k (b k) (hb k)).1
  have hrat : ∀ k i, RM.y ⟨k, i⟩ / RM.y ⟨k, b k⟩ ∈ regAt Or.𝔐.ξ p := by
    intro k i
    obtain ⟨r, ⟨h', s, hs, -⟩, -⟩ := (hc.2 k (b k) (hb k)).2 i
    exact ⟨s, hs⟩
  have hch : InChart Or.𝔐.ξ (fun c' : (k : RM.K) → RM.ι k => ∏ k, RM.y ⟨k, c' k⟩) b p := by
    refine ⟨Finset.prod_ne_zero_iff.2 fun k _ => hyc k, fun c' => ?_⟩
    show (∏ k, RM.y ⟨k, c' k⟩) / ∏ k, RM.y ⟨k, b k⟩ ∈ _
    rw [← Finset.prod_div_distrib]
    exact prod_mem fun k _ => hrat k (c' k)
  have he0 : ∀ r, Or.e r ≠ 0 := fun r => (Or.lines r).1
  have hgen : ∀ r, (Or.Fl.rootLat r).IsGenAt p ((∏ k, RM.y ⟨k, b k⟩ ^ RM.xdeg r k) • Or.e r) := fun r =>
    ⟨smul_ne_zero (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hyc k)) (he0 r),
      (Or.lines r).2 _ trivial b hch⟩
  have ht := GlobalTheory.CompanionTheory.Ar.Chg.CoverEff.tens_isGenAt (fun r => -Fx.n r) hgen
  have ya : Or.g (Fx.yf (Or.ix.symm (b Or.k₀))) = RM.y ⟨Or.k₀, b Or.k₀⟩ := by
    rw [← Or.y_eq, Equiv.apply_symm_apply]
  have hch' : InChart Or.𝔐.ξ (fun i' => Or.g (Fx.yf i')) (Or.ix.symm (b Or.k₀)) p := by
    refine ⟨?_, fun j => ?_⟩
    · show Or.g (Fx.yf (Or.ix.symm (b Or.k₀))) ≠ 0
      rw [ya]; exact hyc _
    · show Or.g (Fx.yf j) / Or.g (Fx.yf (Or.ix.symm (b Or.k₀))) ∈ _
      rw [ya, ← Or.y_eq]
      exact hrat _ _
  have hnat : ∀ m : ℕ, m ≠ 0 → unitAt Or.𝔐.ξ p (m : RM.Ω) := by
    intro m hm
    have e : (((m : RM.Ω), (m : ℂ)) : RM.Ω × ℂ) = ((m : RM.Ω × ℂ)) := Prod.ext (by simp) (by simp)
    have h2 : (((m : RM.Ω), (m : ℂ)) : RM.Ω × ℂ) ∈ valRing Or.𝔐.ξ z hz := by
      rw [e]
      exact natCast_mem _ m
    exact unitAt_of_mem_valRing hz h2 (Nat.cast_ne_zero.2 hm)
  have hp0 : ∀ r : ℕ, r.Prime → ¬ InFibre Or.𝔐.ξ r p := fun r hr hf => hf (hnat r hr.ne_zero)
  obtain ⟨-, hnu⟩ := Or.eff p hp0 _ _ hch' ht
  have hN₀ : N₀ ≠ 0 := by
    rintro rfl
    exact hε (by simp)
  have hA := unitAt_form hz hc b hbw hG hwG
  have hB := unitAt_form hz hc b hbw hH hwH
  have hAB : unitAt Or.𝔐.ξ p ((aeval RM.y G / ∏ k, RM.y ⟨k, b k⟩ ^ dg k) /
      (aeval RM.y Hf / ∏ k, RM.y ⟨k, b k⟩ ^ dh k)) :=
    ⟨div_ne_zero hA.1 hB.1, by rw [div_eq_mul_inv]; exact mul_mem hA.2.1 hB.2.2,
      by rw [inv_div, div_eq_mul_inv]; exact mul_mem hB.2.1 hA.2.2⟩
  have hid := mono_identity (fun k => RM.y ⟨k, b k⟩) hyc Or.e he0 RM.xdeg RM.A.a Fx.n Fx.q' Or.k₀ Or.A_deg
    (combLine (RM.line 1) n₀).a (fun k => by
      simp [combLine, Finset.sum_apply, Fintype.sum_option, RootModel.line, RM.x_deg, hn, hnone])
  have hHf0 : aeval RM.y Hf ≠ 0 := fun h0 => hB.1 (by rw [h0, zero_div])
  have hMh : ∏ k, RM.y ⟨k, b k⟩ ^ dh k ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hyc k)
  have hPa : ∏ k, RM.y ⟨k, b k⟩ ^ (combLine (RM.line 1) n₀).a k ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hyc k)
  have hMg : ∏ k, RM.y ⟨k, b k⟩ ^ dg k =
      (∏ k, RM.y ⟨k, b k⟩ ^ dh k) * ∏ k, RM.y ⟨k, b k⟩ ^ (combLine (RM.line 1) n₀).a k := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← zpow_natCast, hdeg k, zpow_add₀ (hyc k), zpow_natCast]
  have hfin : (aeval RM.y G / ∏ k, RM.y ⟨k, b k⟩ ^ dg k) / (aeval RM.y Hf / ∏ k, RM.y ⟨k, b k⟩ ^ dh k) =
      (Or.g Fx.sE * Or.g (Fx.yf (Or.ix.symm (b Or.k₀))) ^ Fx.q' /
        ∏ r, ((∏ k, RM.y ⟨k, b k⟩ ^ RM.xdeg r k) • Or.e r) ^ (-Fx.n r)) * (N₀ : RM.Ω) := by
    have hid' : (∏ k, RM.y ⟨k, b k⟩ ^ (combLine (RM.line 1) n₀).a k)⁻¹ * ∏ r, Or.e r ^ Fx.n r =
        RM.y ⟨Or.k₀, b Or.k₀⟩ ^ Fx.q' / ∏ r, ((∏ k, RM.y ⟨k, b k⟩ ^ RM.xdeg r k) • Or.e r) ^ (-Fx.n r) := hid
    rw [hy, hMg, ya, mul_div_assoc (Or.g Fx.sE), ← hid']
    field_simp
  rw [hfin] at hAB
  exact hnu hnab (GlobalTheory.CompanionTheory.Ar.Chg.CoverEff.unitAt_of_mul hAB (hnat N₀ hN₀))

end GlobalTheory.CompanionTheory.Ar.Small.FormsVal
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularizedWeightTendstoUniformly
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

namespace GlobalTheory.CompanionTheory.Ar.Cusp

theorem tendstoUniformlyOn_regWeight_of_isTied :
    ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRing J)) (n : ℕ) (M : CxModel P n) (Xo : Set ((Σ k, J k) → ℂ)) (A : HermLine J) (S : LogLogRegularisationSetting M Xo A), S.IsTied → ∀ K' ⊆ S.R.Yo, IsCompact K' → TendstoUniformlyOn S.regWeight S.R.ph (𝓝[>] 0) K' := by
  intro K _ J _ P n M Xo A S hS K' hK'Y hK'
  refine hK'.induction_on (p := fun s => TendstoUniformlyOn S.regWeight S.R.ph (𝓝[>] 0) s)
    ?_ ?_ ?_ ?_
  · intro u _
    simp
  · intro s t hst ht
    exact ht.mono hst
  · intro s t hs ht
    intro u hu
    filter_upwards [hs u hu, ht u hu] with a ha hb y hy
    exact hy.elim (ha y) (hb y)
  · intro x hx
    obtain ⟨j, hj⟩ := M.atlas.cover x
    have hopen : (M.atlas.chart j).source ∈ 𝓝 x := (M.atlas.chart j).open_source.mem_nhds hj
    obtain ⟨C, hCn, hCs, hCc⟩ := local_compact_nhds hopen
    refine ⟨C ∩ K', ?_, ?_⟩
    · exact Filter.inter_mem (mem_nhdsWithin_of_mem_nhds hCn) self_mem_nhdsWithin
    · have hcpt : IsCompact (C ∩ K') := hCc.inter hK'
      have himg : IsCompact ((M.atlas.chart j) '' (C ∩ K')) :=
        hcpt.image_of_continuousOn
          ((M.atlas.chart j).continuousOn.mono fun y hy => hCs hy.1)
      have hsub : (M.atlas.chart j) '' (C ∩ K') ⊆
          (M.atlas.chart j).target ∩ (M.atlas.chart j).symm ⁻¹' S.R.Yo := by
        rintro _ ⟨y, hy, rfl⟩
        refine ⟨(M.atlas.chart j).map_source (hCs hy.1), ?_⟩
        show (M.atlas.chart j).symm ((M.atlas.chart j) y) ∈ S.R.Yo
        rw [(M.atlas.chart j).left_inv (hCs hy.1)]
        exact hK'Y hy.2
      have hu := (_root_.GlobalTheory.CompanionTheory.Ar.Giv.regWeight_tendsto_C2_of_tied K J P n M Xo A S hS j _ hsub himg).1
      rw [Metric.tendstoUniformlyOn_iff] at hu ⊢
      intro ε hε
      filter_upwards [hu ε hε] with t ht y hy
      have h := ht _ (Set.mem_image_of_mem _ hy)
      simpa [Function.comp, (M.atlas.chart j).left_inv (hCs hy.1)] using h

end GlobalTheory.CompanionTheory.Ar.Cusp
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.RootOriginWeightIdentity
section
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Small.Fund

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Small.OriginEps

open AlgebraicGeometry CategoryTheory

section General

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] [CharZero Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

theorem mem_adjoin_rat_of_regular {κ : Type} {x : κ → Ω} (hT : CoordTie ℤ ξ x)
    {c : κ} (hc : x c ≠ 0) {f : Ω}
    (hf : ∀ p : Cpt ξ, InChart ξ x c p → (∀ r : ℕ, r.Prime → ¬ InFibre ξ r p) → f ∈ regAt ξ p) :
    f ∈ Algebra.adjoin ℚ (Set.range fun j => x j / x c) := by
  classical
  set B := Algebra.adjoin ℚ (Set.range fun j => x j / x c) with hB
  have hle : ∀ a ∈ chartRing ℤ x c, a ∈ B := by
    intro a ha
    have h2 : chartRing ℤ x c ≤ B.restrictScalars ℤ := Algebra.adjoin_le Algebra.subset_adjoin
    exact h2 ha
  let I : Ideal (chartRing ℤ x c) :=
    { carrier := {a | (a : Ω) * f ∈ B}
      add_mem' := fun {u v} hu hv => by
        show ((u + v : chartRing ℤ x c) : Ω) * f ∈ B
        rw [Subalgebra.coe_add, add_mul]
        exact add_mem hu hv
      zero_mem' := by
        show ((0 : chartRing ℤ x c) : Ω) * f ∈ B
        simp
      smul_mem' := fun a u hu => by
        show ((a • u : chartRing ℤ x c) : Ω) * f ∈ B
        rw [smul_eq_mul, Subalgebra.coe_mul, _root_.mul_assoc]
        exact mul_mem (hle _ a.2) hu }
  let T : Submonoid (chartRing ℤ x c) :=
    { carrier := {u | ∃ b : ℕ, b ≠ 0 ∧ (u : Ω) = b}
      one_mem' := ⟨1, one_ne_zero, by simp⟩
      mul_mem' := by
        rintro u v ⟨b, hb, hu⟩ ⟨b', hb', hv⟩
        exact ⟨b * b', mul_ne_zero hb hb', by rw [Subalgebra.coe_mul, hu, hv]; push_cast; rfl⟩ }
  by_contra hcon
  have hdisj : Disjoint (I : Set (chartRing ℤ x c)) (T : Set (chartRing ℤ x c)) := by
    rw [Set.disjoint_left]
    rintro u hu ⟨b, hb, hub⟩
    have hu' : (b : Ω) * f ∈ B := by rw [← hub]; exact hu
    apply hcon
    have h2 := B.smul_mem hu' ((b : ℚ)⁻¹)
    have hb0 : (b : Ω) ≠ 0 := Nat.cast_ne_zero.2 hb
    have e : ((b : ℚ)⁻¹) • ((b : Ω) * f) = f := by
      rw [Algebra.smul_def, map_inv₀, map_natCast, ← _root_.mul_assoc, inv_mul_cancel₀ hb0, _root_.one_mul]
    rwa [e] at h2
  obtain ⟨P, hP, hIP, hPT⟩ := Ideal.exists_le_prime_disjoint I T hdisj
  obtain ⟨p, hp, hpP⟩ := TieVB.exists_point hT hc P hP
  have h0 : ∀ r : ℕ, r.Prime → ¬ InFibre ξ r p := by
    intro r hr hfib
    have hrT : (r : chartRing ℤ x c) ∈ T := ⟨r, hr.ne_zero, by simp⟩
    have hnot : (r : chartRing ℤ x c) ∉ P := fun h => Set.disjoint_left.1 hPT h hrT
    have hu := not_not.1 (mt (hpP (r : chartRing ℤ x c)).2 hnot)
    apply hfib
    simpa using hu
  obtain ⟨s, hsA, hsu, hsf⟩ := TieVB.exists_den hT hp (hf p hp h0)
  have hI : (⟨s, hsA⟩ : chartRing ℤ x c) ∈ I := hle _ hsf
  exact (hpP ⟨s, hsA⟩).1 (hIP hI) hsu

theorem adjoin_segre_le {K : Type} [Fintype K] {ι : K → Type} {y : (Σ k, ι k) → Ω} (c : (k : K) → ι k) :
    Algebra.adjoin ℚ (Set.range fun c' : (k : K) → ι k => (∏ k, y ⟨k, c' k⟩) / ∏ k, y ⟨k, c k⟩) ≤
      Algebra.adjoin ℚ (Set.range fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩) := by
  refine Algebra.adjoin_le ?_
  rintro _ ⟨c', rfl⟩
  show (∏ k, y ⟨k, c' k⟩) / ∏ k, y ⟨k, c k⟩ ∈ _
  rw [← Finset.prod_div_distrib]
  exact prod_mem fun k _ => Algebra.subset_adjoin ⟨⟨k, c' k⟩, rfl⟩

theorem zpow_sum_of_ne {R : Type} {a : Ω} (ha : a ≠ 0) (s : Finset R) (f : R → ℤ) :
    a ^ (∑ r ∈ s, f r) = ∏ r ∈ s, a ^ f r := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert r s hr ih => rw [Finset.sum_insert hr, Finset.prod_insert hr, zpow_add₀ ha, ih]

theorem eps_identity {K R : Type} [Fintype K] [Fintype R] {Y : K → Ω} (hY : ∀ k, Y k ≠ 0) (xd : R → K → ℤ)
    {e : R → Ω} (n : R → ℤ) (A : K → ℤ) (k₀ : K) (hA₀ : A k₀ = 1)
    (hA : ∀ k, k ≠ k₀ → A k = 0) (q : ℕ) (s : Ω) :
    (s * ∏ r, e r ^ n r) * ∏ k, Y k ^ (-(∑ r, (-n r) * xd r k + (-(q : ℤ)) * A k)) =
      s * Y k₀ ^ q / ∏ r, ((∏ k, Y k ^ xd r k) * e r) ^ (-n r) := by
  have h1 : ∀ k, Y k ^ (-(∑ r, (-n r) * xd r k + (-(q : ℤ)) * A k)) =
      (∏ r, (Y k ^ xd r k) ^ n r) * Y k ^ ((q : ℤ) * A k) := by
    intro k
    have e1 : -(∑ r, (-n r) * xd r k + (-(q : ℤ)) * A k) = ∑ r, xd r k * n r + (q : ℤ) * A k := by
      rw [neg_add, ← Finset.sum_neg_distrib]
      congr 1
      · exact Finset.sum_congr rfl fun r _ => by ring
      · ring
    rw [e1, zpow_add₀ (hY k), zpow_sum_of_ne (hY k)]
    simp only [zpow_mul]
  have h2 : ∏ k, Y k ^ ((q : ℤ) * A k) = Y k₀ ^ q := by
    rw [Finset.prod_eq_single k₀ (fun k _ hk => by rw [hA k hk]; simp) (fun h => absurd (Finset.mem_univ _) h), hA₀]
    simp
  have h3 : ∏ r, ((∏ k, Y k ^ xd r k) * e r) ^ (-n r) =
      ((∏ k, ∏ r, (Y k ^ xd r k) ^ n r) * ∏ r, e r ^ n r)⁻¹ := by
    simp only [zpow_neg, Finset.prod_inv_distrib]
    congr 1
    simp only [mul_zpow, Finset.prod_mul_distrib]
    congr 1
    rw [Finset.prod_comm]
    exact Finset.prod_congr rfl fun r _ => (Finset.prod_zpow _ _ _).symm
  simp only [h1, Finset.prod_mul_distrib]
  rw [h2, h3, div_inv_eq_mul]
  ring

end General

theorem section_on_model : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (RM : RootModel (CMType H) (D.p + D.q)) (Sys : PB.AnSys (dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))) (Fx : FixedData Y Sys) (Or : RootOrigin Y S RM Fx) (nu : Wt (CMType H) (D.p + D.q)), (∀ r, (Fx.n r : ℝ) = (Fx.kA * Fx.q' : ℕ) * nu r.1 r.2) → ∃ (n₀ : Option (RootIx D) → ℤ) (N₀ : ℕ), (∀ j, (n₀ j : ℝ) = (Fx.kA * Fx.q' : ℕ) * RM.coef nu (-1) j) ∧ 0 < N₀ ∧ ((N₀ : RM.Ω) * Or.g Fx.sE * ∏ r, Or.e r ^ Fx.n r) ≠ 0 ∧ ((N₀ : RM.Ω) * Or.g Fx.sE * ∏ r, Or.e r ^ Fx.n r) ∈ chartLatNm RM.y (combLine (RM.line 1) n₀).a 1 := by
  intro E _ _ _ H D l Xo c O _ β Y S RM Sys Fx o nu hn
  classical
  haveI : CharZero c.F := inferInstance
  haveI : CharZero RM.Ω := charZero_of_injective_ringHom o.𝔐.cst.injective
  have hkA : (RM.kA : ℝ) = Fx.kA := by exact_mod_cast o.kA_eq
  have hkpos : (0 : ℝ) < Fx.kA := by rw [← hkA]; exact_mod_cast RM.kA_pos
  let n₀ : Option (RootIx D) → ℤ := fun j => j.elim (-(Fx.q' : ℤ)) fun r => -Fx.n r
  have hs0 : o.g Fx.sE * ∏ r, o.e r ^ Fx.n r ≠ 0 :=
    mul_ne_zero ((map_ne_zero o.g).2 Fx.sE_ne)
      (Finset.prod_ne_zero_iff.2 fun r _ => zpow_ne_zero _ (o.lines r).1)
  have ha : ∀ k, (combLine (RM.line 1) n₀).a k =
      ∑ r, (-Fx.n r) * RM.xdeg r k + (-(Fx.q' : ℤ)) * RM.A.a k := by
    intro k
    show (∑ j, n₀ j • (RM.line 1 j).a) k = _
    rw [Finset.sum_apply, Fintype.sum_option, add_comm]
    congr 1
    · refine Finset.sum_congr rfl fun r _ => ?_
      simp [n₀, RootModel.line, RM.x_deg]
  have key : ∀ c' : ∀ k, RM.ι k, (∀ k, RM.y ⟨k, c' k⟩ ≠ 0) →
      IsIntegral (Algebra.adjoin ℚ (Set.range fun p : Σ k, RM.ι k => RM.y p / RM.y ⟨p.1, c' p.1⟩))
        ((o.g Fx.sE * ∏ r, o.e r ^ Fx.n r) * ∏ k, RM.y ⟨k, c' k⟩ ^ (-((combLine (RM.line 1) n₀).a k))) := by
    intro c' hc'
    have hx : (∏ k, RM.y ⟨k, c' k⟩) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => hc' k
    have ya : o.g (Fx.yf (o.ix.symm (c' o.k₀))) = RM.y ⟨o.k₀, c' o.k₀⟩ := by
      rw [← o.y_eq, Equiv.apply_symm_apply]
    have hfeq : (o.g Fx.sE * ∏ r, o.e r ^ Fx.n r) * ∏ k, RM.y ⟨k, c' k⟩ ^ (-((combLine (RM.line 1) n₀).a k)) =
        o.g Fx.sE * o.g (Fx.yf (o.ix.symm (c' o.k₀))) ^ Fx.q' /
          ∏ r, ((∏ k, RM.y ⟨k, c' k⟩ ^ RM.xdeg r k) * o.e r) ^ (-Fx.n r) := by
      simp only [ha]
      rw [ya]
      exact eps_identity hc' RM.xdeg Fx.n RM.A.a o.k₀ o.A_deg.1 o.A_deg.2 Fx.q' _
    have hreg : ∀ p : Cpt o.𝔐.ξ, InChart o.𝔐.ξ (fun c'' : (k : RM.K) → RM.ι k => ∏ k, RM.y ⟨k, c'' k⟩) c' p →
        (∀ r : ℕ, r.Prime → ¬ InFibre o.𝔐.ξ r p) →
        o.g Fx.sE * o.g (Fx.yf (o.ix.symm (c' o.k₀))) ^ Fx.q' /
          ∏ r, ((∏ k, RM.y ⟨k, c' k⟩ ^ RM.xdeg r k) * o.e r) ^ (-Fx.n r) ∈ regAt o.𝔐.ξ p := by
      intro p hp hp0
      have hch : InChart o.𝔐.ξ (fun i' => o.g (Fx.yf i')) (o.ix.symm (c' o.k₀)) p := by
        refine ⟨?_, fun j => ?_⟩
        · show o.g (Fx.yf (o.ix.symm (c' o.k₀))) ≠ 0
          rw [ya]; exact hc' _
        · show o.g (Fx.yf j) / o.g (Fx.yf (o.ix.symm (c' o.k₀))) ∈ _
          rw [ya, ← o.y_eq]
          exact Lat.block_ratio_mem hp o.k₀ (o.ix j)
      have ht := GlobalTheory.CompanionTheory.Ar.Chg.CoverEff.tens_isGenAt (Λ := o.Fl.rootLat) (fun r => -Fx.n r) (p := p)
        (s := fun r => (∏ k, RM.y ⟨k, c' k⟩ ^ RM.xdeg r k) * o.e r) fun r =>
          ⟨mul_ne_zero (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hc' k)) (o.lines r).1,
            (o.lines r).2 _ trivial c' hp⟩
      exact (o.eff p hp0 _ _ hch ht).1
    have hB := adjoin_segre_le c' (mem_adjoin_rat_of_regular o.𝔐.tie hx hreg)
    rw [hfeq]
    exact isIntegral_algebraMap (x := (⟨_, hB⟩ : Algebra.adjoin ℚ
      (Set.range fun p : Σ k, RM.ι k => RM.y p / RM.y ⟨p.1, c' p.1⟩)))
  obtain ⟨N₀, hN, hmem⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Small.exists_nat_mul_mem_chartLatNm_of_isIntegral_rat RM.K RM.ι RM.Ω RM.y 0 (combLine (RM.line 1) n₀).a _ key
  refine ⟨n₀, N₀, ?_, hN, ?_, ?_⟩
  · intro j
    cases j with
    | none =>
      show ((-(Fx.q' : ℤ) : ℤ) : ℝ) = ((Fx.kA * Fx.q' : ℕ) : ℝ) * (-1 / (RM.kA : ℝ))
      rw [hkA]
      push_cast
      field_simp
    | some r =>
      show ((-Fx.n r : ℤ) : ℝ) = ((Fx.kA * Fx.q' : ℕ) : ℝ) * (-nu r.1 r.2)
      push_cast
      rw [hn r]
      push_cast
      ring
  · rw [_root_.mul_assoc]
    exact mul_ne_zero (Nat.cast_ne_zero.2 hN.ne') hs0
  · rw [_root_.mul_assoc]
    exact hmem

end GlobalTheory.CompanionTheory.Ar.Small.OriginEps
end
end

