module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.EqZeroIffSubsingleton
section
noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM

namespace GlobalTheory.SiegelTor

section Param

variable {o R : Type} [CommRing o] [CommRing R] [IsLocalRing R] {m : ℕ} {b : o →+* R} {t : Fin m → R}

theorem IsRelParam.notMem_sq (h : IsRelParam b t) (i : Fin m) : t i ∉ maximalIdeal R ^ 2 := fun hi => by
  have := h.mem_of_mem_sq (Pi.single i 1) (by simpa [Pi.single_apply] using hi) i
  simp at this

theorem IsRelParam.ne_zero (h : IsRelParam b t) (i : Fin m) : t i ≠ 0 := fun h0 => h.notMem_sq i (h0 ▸ zero_mem _)

theorem IsRelParam.eq_of_dvd (h : IsRelParam b t) {i j : Fin m} (hd : t i ∣ t j) : i = j := by
  by_contra hne
  obtain ⟨c, hc⟩ := hd
  have := h.mem_of_mem_sq (Pi.single j 1 - Pi.single i c)
    (by simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]; simp [Pi.single_apply, hc, mul_comm c]) j
  simp [Ne.symm hne] at this

end Param

section Local

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {m : ℕ}


end Local

section Charts

variable {o : Type} [CommRing o] {ζ : o} {g n : ℕ} {F : SFam g n ζ} {S : Scheme.{0}} {s : S ⟶ Sp o} {j : F.X ⟶ S}
  {G : Over S} [GrpObj G] {e : F.univ.A.left ⟶ G.left}

end Charts

end GlobalTheory.SiegelTor
end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotHasChartOfOfMinEqZero
section
noncomputable section

open AlgebraicGeometry CategoryTheory NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.MumfordChart

namespace GlobalTheory.FanChartTest

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {φ : InvFun (𝓞 E)} {Z : Model Xo c β} {BD : EffCartierData Z.X} {d : ℕ} {x : gen Z}


omit [IsCMField E] in
theorem projective_of_free_int (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X] [Module.Finite (𝓞 E) X] :
    Module.Projective (𝓞 E) X := by
  have : Module.IsTorsionFree (𝓞 E) X := by
    refine Module.IsTorsionFree.of_smul_eq_zero fun a y h => ?_
    by_cases ha : a = 0
    · exact Or.inl ha
    · right
      obtain ⟨b, n, hn, hb⟩ : ∃ (b : 𝓞 E) (n : ℤ), n ≠ 0 ∧ b * a = n := by
        obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {a}))
        refine ⟨b, Ideal.absNorm (Ideal.span {a}), ?_, by simpa using hb⟩
        simpa [Ideal.absNorm_eq_zero_iff] using ha
      have : n • y = 0 := by
        rw [← Int.cast_smul_eq_zsmul (𝓞 E), ← hb, mul_smul, h, smul_zero]
      exact (smul_eq_zero.1 this).resolve_left hn
  have : Module.Flat (𝓞 E) X := inferInstance
  have : Module.FinitePresentation (𝓞 E) X := Module.finitePresentation_of_finite _ _
  exact Module.Flat.projective_of_finitePresentation

theorem pos_of_mem {k : Type} [Field k] {m e : ℕ} {ξ : Sp (ChartRing k m e) ⟶ gen Z}
    (h : ∀ p : Sp (ChartRing k m e), ξ p ∈ genBd Z ↔ ∏ i, bdParam k m e i ∈ p.asIdeal)
    (hx : ξ (closedPoint _) ∈ genBd Z) : 0 < m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have := (h _).1 hx
    rw [Finset.univ_eq_empty, Finset.prod_empty] at this
    exact absurd ((Ideal.eq_top_iff_one _).2 this) (closedPoint _ : PrimeSpectrum _).isPrime.ne_top
  · exact hm

theorem idlAlong_ne_top (hφ : IsPolFan H.bar (min D.p D.q) φ) (hd : 1 ≤ d) (hx : x ∈ genBd Z)
    (h : HasChartOf φ Z BD d x) : FinalTheorems.stalkId BD.idealSheaf (genι Z x) ≠ ⊤ := by
  obtain ⟨k, _, m, e, ξ, t, P, γ, δ, a, rfl, -, -, h₃, -, -, h₀, h₆, h₇, h₈, h₉⟩ := h
  have := projective_of_free_int (E := E) P.D.toPre.X
  let i : Fin m := ⟨0, pos_of_mem h₃ hx⟩
  have hp := (hφ _ h₀).pos _ (h₆.mem i) (h₆.nonneg i) (h₆.linearIndependent.ne_zero i)
  have ha : a i ≠ 0 := by
    have e := h₈ i
    rw [h₇, h₆.evalZ_smul] at e
    have h1 : (0 : ℝ) < d := by exact_mod_cast hd
    have h2 : (0 : ℝ) < l.M' := by exact_mod_cast Nat.pos_of_ne_zero (level_ne_zero l)
    have : (0 : ℝ) < a i := by rw [e]; positivity
    exact_mod_cast this.ne'
  intro ht
  have ht' : FinalTheorems.stalkId BD.idealSheaf ((ξ ≫ genι Z) (closedPoint _)) = ⊤ := ht
  rw [idlAlong, ht', Ideal.map_top, eq_comm, Ideal.span_singleton_eq_top] at h₉
  have hu := (isUnit_pow_iff ha).1 (isUnit_of_dvd_unit (Finset.dvd_prod_of_mem (fun j => bdParam k m e j ^ a j) (Finset.mem_univ i)) h₉)
  simpa [MvPowerSeries.isUnit_iff_constantCoeff] using hu

end GlobalTheory.FanChartTest
end
end

