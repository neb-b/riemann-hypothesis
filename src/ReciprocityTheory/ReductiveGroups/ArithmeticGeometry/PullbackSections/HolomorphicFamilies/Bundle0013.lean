module

public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0033
public import Formalism.LocalToGlobal.ProjectiveLattices.ChartDirectionsIntegral
public import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.BiextChangeSecondFactor
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.BiextCoeffSecondLinear
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.IdemDataBasis
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0004
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.DiscrB
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.DiscriminantRealSubfield
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0009
public import Mathlib
public import Formalism.FrobeniusOrbits.HostCorollaries
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ChartValueRamifiedOfLifts
section
noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor

section Jv

variable (T : CDVR) (e : ℕ)

theorem nval_alg_nonneg (r : T.V) : (0 : EReal) ≤ nval T.V e (algebraMap T.V T.Fr r) := by
  by_cases hr : algebraMap T.V T.Fr r = 0
  · rw [hr, nval_zero]
    exact le_top
  · rw [nval_of_ne hr]
    have hv0 : 0 ≤ vV T.V (algebraMap T.V T.Fr r) := by
      unfold Formalism.L2.Pj.vV Formalism.L2.Pj.valV
      have hle := IsDedekindDomain.HeightOneSpectrum.valuation_le_one (K := T.Fr)
        (IsDiscreteValuationRing.maximalIdeal T.V) r
      have hne : (IsDedekindDomain.HeightOneSpectrum.valuation T.Fr (IsDiscreteValuationRing.maximalIdeal T.V))
          (algebraMap T.V T.Fr r) ≠ 0 := (Valuation.ne_zero_iff _).mpr hr
      have hlog := (WithZero.log_le_log hne one_ne_zero).mpr hle
      rw [WithZero.log_one] at hlog
      linarith
    have hv : (0 : ℝ) ≤ (vV T.V (algebraMap T.V T.Fr r) : ℝ) := by exact_mod_cast hv0
    exact EReal.coe_nonneg.mpr (div_nonneg hv (Nat.cast_nonneg e))

def Jv (c : ℝ) : Submodule T.V T.Fr where
  carrier := {x | (((-c : ℝ)) : EReal) ≤ nval T.V e x}
  add_mem' := fun {a b} ha hb => le_trans (le_min ha hb) (nval_add e a b)
  zero_mem' := by
    show _ ≤ nval T.V e 0
    rw [nval_zero]
    exact le_top
  smul_mem' := fun r x hx => by
    show _ ≤ nval T.V e (r • x)
    rw [Algebra.smul_def, nval_mul]
    exact hx.trans (le_add_of_nonneg_left (nval_alg_nonneg T e r))

theorem one_mem_Jv {c : ℝ} (hc : 0 ≤ c) : (1 : T.Fr) ∈ Jv T e c := by
  show ((-c : ℝ) : EReal) ≤ nval T.V e 1
  have h1 := Formalism.L2.Pj.vV_mul (V := T.V) (K' := T.Fr) (x := 1) (y := 1) one_ne_zero one_ne_zero
  rw [mul_one] at h1
  have h0 : vV T.V (1 : T.Fr) = 0 := by omega
  rw [nval_of_ne one_ne_zero, h0]
  simp only [Int.cast_zero, zero_div]
  exact_mod_cast neg_nonpos.mpr hc

theorem mem_Jv_pow {c : ℝ} (_hc : 0 ≤ c) : ∀ (m : ℕ) (x : T.Fr), x ∈ Jv T e c ^ m →
    (((-((m : ℝ) * c)) : ℝ) : EReal) ≤ nval T.V e x := by
  intro m
  induction m with
  | zero =>
    intro x hx
    rw [pow_zero] at hx
    obtain ⟨r, rfl⟩ := Submodule.mem_one.mp hx
    simp only [Nat.cast_zero, zero_mul, neg_zero, EReal.coe_zero]
    exact nval_alg_nonneg T e r
  | succ m ih =>
    intro x hx
    rw [pow_succ] at hx
    refine Submodule.mul_induction_on hx (fun a ha b hb => ?_) (fun y z hy hz => ?_)
    · rw [nval_mul]
      have h1 := ih a ha
      have h2 : ((-c : ℝ) : EReal) ≤ nval T.V e b := hb
      calc (((-(((m + 1 : ℕ) : ℝ) * c)) : ℝ) : EReal)
          = (((-((m : ℝ) * c)) : ℝ) : EReal) + ((-c : ℝ) : EReal) := by
            rw [← EReal.coe_add]
            congr 1
            push_cast
            ring
        _ ≤ _ := add_le_add h1 h2
    · exact le_trans (le_min hy hz) (nval_add e y z)

end Jv

theorem two_pairMin_le {ι π : Type} [Fintype ι] [Fintype π] [DecidableEq π] (c : ι → π) (s : ι → Bool)
    (x : ι →₀ ℕ) : 2 * pairMin c s x ≤ ∑ l, x l := by
  unfold pairMin
  rw [Finset.mul_sum]
  calc ∑ q : π, 2 * min (∑ l ∈ Finset.univ.filter (fun l => c l = q ∧ s l = true), x l)
        (∑ l ∈ Finset.univ.filter (fun l => c l = q ∧ s l = false), x l)
      ≤ ∑ q : π, ((∑ l ∈ Finset.univ.filter (fun l => c l = q ∧ s l = true), x l) +
        (∑ l ∈ Finset.univ.filter (fun l => c l = q ∧ s l = false), x l)) := by
        refine Finset.sum_le_sum (fun q _ => ?_)
        have h1 := min_le_left (∑ l ∈ Finset.univ.filter (fun l => c l = q ∧ s l = true), x l)
          (∑ l ∈ Finset.univ.filter (fun l => c l = q ∧ s l = false), x l)
        have h2 := min_le_right (∑ l ∈ Finset.univ.filter (fun l => c l = q ∧ s l = true), x l)
          (∑ l ∈ Finset.univ.filter (fun l => c l = q ∧ s l = false), x l)
        omega
    _ = ∑ l, x l := by
        simp only [Finset.sum_filter, ← Finset.sum_add_distrib]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun l _ => ?_)
        rw [Finset.sum_eq_single (c l)]
        · cases s l <;> simp
        · intro b _ hb
          have hb' : c l ≠ b := fun h => hb h.symm
          simp [hb']
        · intro h
          exact absurd (Finset.mem_univ _) h

theorem sum_pairMin_le {T : Type} [Fintype T] (rr : T → ℕ) (n : ℕ) {π : Type} [Fintype π] [DecidableEq π]
    (c : T → π) (s : T → Bool) (a : T → ℕ → ℕ) (mo : Formalism.L2.Pj.Letter T rr n →₀ ℕ)
    (hrow : ∀ (σ : T) (i : Fin (rr σ)), ∑ b : Fin n, mo ⟨σ, i, b⟩ = a σ i) :
    ∑ b, pairMin (fun ℓ : (Σ τ : T, Fin (rr τ)) => c ℓ.1) (fun ℓ => s ℓ.1) (colL rr n mo b) ≤
      (∑ σ, ∑ i : Fin (rr σ), a σ i) / 2 := by
  have h2 : 2 * ∑ b, pairMin (fun ℓ : (Σ τ : T, Fin (rr τ)) => c ℓ.1) (fun ℓ => s ℓ.1) (colL rr n mo b) ≤
      ∑ σ, ∑ i : Fin (rr σ), a σ i := by
    rw [Finset.mul_sum]
    calc _ ≤ ∑ b : Fin n, ∑ ℓ : (Σ τ : T, Fin (rr τ)), colL rr n mo b ℓ :=
          Finset.sum_le_sum (fun b _ => two_pairMin_le _ _ _)
      _ = ∑ ℓ : (Σ τ : T, Fin (rr τ)), ∑ b : Fin n, mo ⟨ℓ.1, ℓ.2, b⟩ := by
          rw [Finset.sum_comm]
          rfl
      _ = ∑ σ, ∑ i : Fin (rr σ), a σ i := by
          rw [Fintype.sum_sigma]
          exact Finset.sum_congr rfl (fun σ _ => Finset.sum_congr rfl (fun i _ => hrow σ i))
  omega

end ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.EigenLiftsOfDirectionsBiext
section
set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace Pf.EigA

theorem idem_data {E : Type} [Field E] [NumberField E] {k V : Type} [Field k] [CommRing V] [Algebra V k]
    (ψ : E →+* k) (hint : ∀ x : 𝓞 E, ∃ v : V, algebraMap V k v = ψ (algebraMap (𝓞 E) E x)) (w : V)
    (hw : algebraMap V k w * (((discr E).natAbs : ℕ) : k) = 1) :
    ∃ (n : ℕ) (b : Fin n → 𝓞 E) (c : Fin n → V),
      (∑ i, algebraMap V k (c i) * ψ (algebraMap (𝓞 E) E (b i)) = 1) ∧
      ∀ a : 𝓞 E, ∃ m : Fin n → Fin n → ℤ, (∀ i, a * b i = ∑ j, m i j • b j) ∧
        ∀ j, ∑ i, (m i j : k) * algebraMap V k (c i) = ψ (algebraMap (𝓞 E) E a) * algebraMap V k (c j) := by
  classical
  obtain ⟨b, c, h1, h2⟩ := idem_data_basis ψ hint w hw
  set eq := Fintype.equivFin (Module.Free.ChooseBasisIndex ℤ (𝓞 E))
  refine ⟨_, fun i => b (eq.symm i), fun i => c (eq.symm i), ?_, fun a => ?_⟩
  · rw [Equiv.sum_comp eq.symm (fun x => algebraMap V k (c x) * ψ (algebraMap (𝓞 E) E (b x)))]
    exact h1
  · obtain ⟨m, hm1, hm2⟩ := h2 a
    refine ⟨fun i j => m (eq.symm i) (eq.symm j), fun i => ?_, fun j => ?_⟩
    · rw [hm1, ← Equiv.sum_comp eq.symm (fun x => m (eq.symm i) x • b x)]
    · rw [Equiv.sum_comp eq.symm (fun x => (m x (eq.symm j) : k) * algebraMap V k (c x))]
      exact hm2 _

end Pf.EigA

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ModelLatIn
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.MLI

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj
open scoped Pointwise

theorem absNorm_smul_eq {E : Type} [Field E] [NumberField E] (σ : E ≃ₐ[ℚ] E) (I : Ideal (𝓞 E)) :
    Ideal.absNorm (σ • I) = Ideal.absNorm I := by
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  exact (Nat.card_congr (Ideal.quotientEquiv I (σ • I) (MulSemiringAction.toRingEquiv _ _ σ)
    (by rw [Ideal.pointwise_smul_def]; rfl)).toEquiv).symm

theorem halfDiffNorm : HalfDiffNormSt := by
  intro D
  obtain ⟨hspec, -⟩ := D.host.𝔟_spec

  have hN : Ideal.absNorm (differentIdeal (𝓞 ↥D.host.K) (𝓞 D.host.E)) =
      Ideal.absNorm D.host.𝔟 ^ 2 := by
    rw [hspec, map_mul, absNorm_smul_eq, sq]

  have htow := differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ (𝓞 ↥D.host.K) (𝓞 D.host.E)
  have hne : differentIdeal ℤ (𝓞 D.host.E) ≠ ⊥ := differentIdeal_ne_bot
  have hdisc : Ideal.absNorm (differentIdeal ℤ (𝓞 D.host.E)) = (discr D.host.E).natAbs :=
    NumberField.absNorm_differentIdeal D.host.E (𝓞 D.host.E)
  have hrel0 : differentIdeal (𝓞 ↥D.host.K) (𝓞 D.host.E) ≠ ⊥ := by
    intro h
    apply hne
    rw [htow, h]
    simp
  have hle : Ideal.absNorm (differentIdeal (𝓞 ↥D.host.K) (𝓞 D.host.E)) ≤ (discr D.host.E).natAbs := by
    rw [← hdisc, htow, map_mul]
    apply Nat.le_mul_of_pos_right
    rw [Nat.pos_iff_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]
    intro h
    apply hne
    rw [htow, h]
    simp
  have hpos2 : 0 < Ideal.absNorm D.host.𝔟 ^ 2 := by
    rw [← hN, Nat.pos_iff_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]
    exact hrel0
  have hpos : 0 < Ideal.absNorm D.host.𝔟 := pos_of_ne_zero fun h => by simp [h] at hpos2
  refine ⟨hpos, ?_⟩
  have hsq : ((Ideal.absNorm D.host.𝔟 : ℕ) : ℝ) ^ 2 ≤ |((discr D.host.E : ℤ) : ℝ)| := by
    rw [← Int.cast_abs, ← Int.natCast_natAbs]
    exact_mod_cast hN ▸ hle
  have hlog := Real.log_pow ((Ideal.absNorm D.host.𝔟 : ℕ) : ℝ) 2
  push_cast at hlog
  rw [← hlog]
  exact Real.log_le_log (by positivity) hsq

theorem bb_ne_bot (D : D7) : D.host.𝔟 ≠ ⊥ := by
  intro h
  have h0 := (halfDiffNorm D).1
  rw [h, Ideal.absNorm_bot] at h0
  exact lt_irrefl 0 h0

theorem finrank_E (D : D7) : Module.finrank ℚ D.host.E = 2 * D.R.f := by
  haveI := D.host.galois
  rw [← IsGalois.card_aut_eq_finrank, Nat.card_congr D.host.gal.toEquiv]
  simp only [Formalism.BasicNotions.Ranks.f, Formalism.BasicNotions.Ranks.n, Formalism.HC.Frame.GG, Nat.card_prod]
  have h2 : Nat.card ℤˣ = 2 := by
    first
      | rw [Nat.card_eq_fintype_card, Int.card_units_eq_two]
      | simp
      | (rw [Nat.card_eq_fintype_card]; rfl)
      | (rw [Nat.card_eq_fintype_card]; decide)
  have hA : Nat.card D.R.MA = D.R.ord := by
    unfold Formalism.HC.Frame.MA
    rw [Nat.card_congr Multiplicative.toAdd]
    unfold Formalism.HC.Frame.A Formalism.HC.Idx
    exact Nat.card_fin _
  rw [h2, hA]
  ring

end ReciprocityTheory.ChartRestriction.G.PullbackSections.MLI
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.RigPMaps
section
set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

theorem rig_pmaps {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S S' : Scheme.{0}}
    {t' : SAB H S'} {t : SAB H S} {f : S' ⟶ S} (m : SABMap t' t f) (w : LB.Iso t'.PP.L (t.PP.L.pull m.φ))
    (h : RigIso m w) :
    PMaps w (K := PUnit.{1}) (fun _ => eSec t'.G) (fun _ => eSec t.G) (fun _ => 1) t'.PP.rig t.PP.rig m.cm.e :=
  (maps_iff w _ _ _ t'.PP.rig t.PP.rig m.cm.e (m.cm.rigPull t.PP.L t.PP.rig)
    (rigPull_le m.cm.F m.cm.e m.cm.e_comm t.PP.L) (fun _ => rfl)).1 h.2

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

