module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0017
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0068
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0018
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0064
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0019
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0002
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle0018
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0065

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.BoundaryGeneratorUnit
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.SncBase.Mdl.Sep

section Forms

variable {Ω : Type} [Field Ω] {N : ℕ}

theorem aeval_eq_pow_mul {σ : Type} [Fintype σ] {v w : σ → Ω} {t : Ω} (h : ∀ i, w i = t * v i)
    {G : MvPolynomial σ ℤ} {d : ℕ} (hG : G.IsHomogeneous d) :
    MvPolynomial.aeval w G = t ^ d * MvPolynomial.aeval v G := by
  rw [MvPolynomial.aeval_def, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq', MvPolynomial.eval₂_eq',
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hdeg : ∑ i, m i = d := by
    have := hG (MvPolynomial.mem_support_iff.1 hm)
    simpa [Finsupp.weight_apply, Finsupp.sum_fintype] using this
  simp only [h, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdeg]
  ring

theorem ratEval_eq_pow_mul (x : Fin (N + 1) → Ω) {c c' : Fin (N + 1)} (hc : x c ≠ 0)
    {G : MRing (fun _ : Unit => Fin (N + 1))} {d : ℕ} (hG : G.IsHomogeneous d) :
    ratEval x c' G = (x c / x c') ^ d * ratEval x c G := by
  refine aeval_eq_pow_mul (fun i => ?_) hG
  field_simp

theorem ratEval_C (x : Fin (N + 1) → Ω) (c : Fin (N + 1)) (n : ℤ) :
    ratEval x c (MvPolynomial.C n) = (n : Ω) :=
  (MvPolynomial.aeval_C _ n).trans (eq_intCast _ n)

theorem ratEval_X_mul (x : Fin (N + 1) → Ω) (c c' : Fin (N + 1)) (H : MRing (fun _ : Unit => Fin (N + 1))) :
    ratEval x c' (MvPolynomial.X ⟨(), c⟩ * H) = x c / x c' * ratEval x c' H := by
  simp only [map_mul, MvPolynomial.aeval_X]

theorem isHomogeneous_X_mul (c : Fin (N + 1)) {H : MRing (fun _ : Unit => Fin (N + 1))} {d : ℕ}
    (hH : H.IsHomogeneous d) : (MvPolynomial.X ⟨(), c⟩ * H : MRing (fun _ : Unit => Fin (N + 1))).IsHomogeneous (d + 1) := by
  rw [add_comm d 1]
  exact (MvPolynomial.isHomogeneous_X ℤ (⟨(), c⟩ : Σ _ : Unit, Fin (N + 1))).mul hH

theorem exists_form [Algebra ℚ Ω] (x : Fin (N + 1) → Ω) {c : Fin (N + 1)} (hc : x c ≠ 0) {a : Ω}
    (ha : a ∈ chartQ x c) :
    ∃ (m d : ℕ) (H : MRing (fun _ : Unit => Fin (N + 1))),
      m ≠ 0 ∧ H.IsHomogeneous d ∧ ratEval x c H = m * a := by
  haveI : CharZero Ω := algebraRat.charZero Ω
  induction ha using Algebra.adjoin_induction with
  | mem a ha =>
    obtain ⟨j, rfl⟩ := ha
    exact ⟨1, 1, MvPolynomial.X ⟨(), j⟩, one_ne_zero, MvPolynomial.isHomogeneous_X _ _, by simp⟩
  | algebraMap r =>
    refine ⟨r.den, 0, MvPolynomial.C r.num, r.den_nz, MvPolynomial.isHomogeneous_C _ _, ?_⟩
    have hd : (r.den : Ω) ≠ 0 := Nat.cast_ne_zero.2 r.den_nz
    rw [eq_ratCast (algebraMap ℚ Ω) r, Rat.cast_def]
    rw [ratEval_C]
    field_simp
  | add a b _ _ ha hb =>
    obtain ⟨m₁, d₁, H₁, hm₁, hH₁, hv₁⟩ := ha
    obtain ⟨m₂, d₂, H₂, hm₂, hH₂, hv₂⟩ := hb
    have hX : (MvPolynomial.X ⟨(), c⟩ : MRing (fun _ : Unit => Fin (N + 1))).IsHomogeneous 1 :=
      MvPolynomial.isHomogeneous_X _ _
    refine ⟨m₁ * m₂, d₁ + d₂,
      MvPolynomial.C (m₂ : ℤ) * H₁ * MvPolynomial.X ⟨(), c⟩ ^ d₂ +
        MvPolynomial.C (m₁ : ℤ) * H₂ * MvPolynomial.X ⟨(), c⟩ ^ d₁,
      mul_ne_zero hm₁ hm₂, ?_, ?_⟩
    · refine MvPolynomial.IsHomogeneous.add ?_ ?_
      · simpa using ((MvPolynomial.isHomogeneous_C _ (m₂ : ℤ)).mul hH₁).mul (hX.pow d₂)
      · simpa [add_comm] using ((MvPolynomial.isHomogeneous_C _ (m₁ : ℤ)).mul hH₂).mul (hX.pow d₁)
    · simp only [map_add (f := _), map_mul, map_pow, MvPolynomial.aeval_X, ratEval_C, hv₁, hv₂, div_self hc]
      push_cast
      ring
  | mul a b _ _ ha hb =>
    obtain ⟨m₁, d₁, H₁, hm₁, hH₁, hv₁⟩ := ha
    obtain ⟨m₂, d₂, H₂, hm₂, hH₂, hv₂⟩ := hb
    refine ⟨m₁ * m₂, d₁ + d₂, H₁ * H₂, mul_ne_zero hm₁ hm₂, hH₁.mul hH₂, ?_⟩
    simp only [map_mul, hv₁, hv₂]
    push_cast
    ring

end Forms

section Pts

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {N : ℕ}

theorem ratEval_regular {x : Fin (N + 1) → Ω} {c : Fin (N + 1)} {p : Cpt ξ} (hc : InChart ξ x c p)
    (g : MRing (fun _ : Unit => Fin (N + 1))) : ratEval x c g ∈ regAt ξ p := by
  induction g using MvPolynomial.induction_on with
  | C a => simpa using intCast_mem (regAt ξ p) a
  | add a b ha hb => simpa using (regAt ξ p).add_mem ha hb
  | mul_X a i ha => simpa using (regAt ξ p).mul_mem ha (hc.2 i.2)

theorem inChart_of_unitAt {x : Fin (N + 1) → Ω} {c c' : Fin (N + 1)} {q : Cpt ξ} (hc : x c ≠ 0)
    (hc' : InChart ξ x c' q) (ht : unitAt ξ q (x c / x c')) : InChart ξ x c q := by
  refine ⟨hc, fun j => ?_⟩
  have e : x j / x c = x j / x c' * (x c / x c')⁻¹ := by
    have := hc'.1
    field_simp
  rw [e]
  exact (regAt ξ q).mul_mem (hc'.2 j) ht.2.2

theorem not_unitAt_form [CharZero Ω] {x : Fin (N + 1) → Ω} {c c' : Fin (N + 1)} {q : Cpt ξ} {a : Ω}
    (hc : x c ≠ 0) (hq0 : Char0 ξ q) (hc' : InChart ξ x c' q) (har : InChart ξ x c q → a ∈ regAt ξ q)
    (hnon : InChart ξ x c q → ¬ unitAt ξ q a) {m d : ℕ} {H : MRing (fun _ : Unit => Fin (N + 1))} (hm : m ≠ 0)
    (hH : H.IsHomogeneous d) (hv : ratEval x c H = m * a) :
    ¬ unitAt ξ q (ratEval x c' (MvPolynomial.X ⟨(), c⟩ * H)) := by
  intro hunit
  have ht : x c / x c' ∈ regAt ξ q := hc'.2 c
  have h₁ := hunit
  rw [ratEval_X_mul] at h₁
  have htu : unitAt ξ q (x c / x c') := unitAt_of_mul_left h₁ ht (ratEval_regular hc' H)
  have hcq : InChart ξ x c q := inChart_of_unitAt hc hc' htu
  have hr : a ∈ regAt ξ q := har hcq
  have hmu := Char0.unitAt_natCast hq0 hm
  have h₂ := hunit
  rw [ratEval_eq_pow_mul x hc (isHomogeneous_X_mul c hH), ratEval_X_mul, div_self hc, _root_.one_mul, hv] at h₂
  have hma : unitAt ξ q ((m : Ω) * a) :=
    unitAt_of_mul_right h₂ ((regAt ξ q).pow_mem ht _) ((regAt ξ q).mul_mem hmu.2.1 hr)
  exact hnon hcq (unitAt_of_mul_right hma hmu.2.1 hr)

end Pts

section Sep

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] [CharZero Ω] {ξ : Sp Ω ⟶ X} {N : ℕ}

theorem exists_form_sep {x : Fin (N + 1) → Ω} {c : Fin (N + 1)} {B : Set (Cpt ξ)} {p : Cpt ξ} {a : Ω}
    (hB : ∀ q ∈ B, Char0 ξ q) (hp : Char0 ξ p) (hc : InChart ξ x c p)
    (hreg : ∀ q : Cpt ξ, Char0 ξ q → InChart ξ x c q → a ∈ regAt ξ q) (hu : unitAt ξ p a)
    (hnon : ∀ q ∈ B, InChart ξ x c q → ¬ unitAt ξ q a) {m d : ℕ}
    {H : MRing (fun _ : Unit => Fin (N + 1))} (hm : m ≠ 0) (hH : H.IsHomogeneous d)
    (hv : ratEval x c H = m * a) : ∃ G ∈ bdGens ξ x B, unitAt ξ p (ratEval x c G) := by
  have hmem : MvPolynomial.X ⟨(), c⟩ * H ∈ bdGens ξ x B :=
    ⟨d + 1, isHomogeneous_X_mul c hH, fun c' q hq hc' =>
      not_unitAt_form hc.1 (hB q hq) hc' (hreg q (hB q hq)) (hnon q hq) hm hH hv⟩
  refine ⟨_, hmem, ?_⟩
  rw [ratEval_X_mul, div_self hc.1, _root_.one_mul, hv]
  exact unitAt_mul (Char0.unitAt_natCast hp hm) hu

end Sep

theorem exists_bdGens_unitAt : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (X : Scheme.{0}) (ξ : Sp Ω ⟶ X) (N : ℕ) (x : Fin (N + 1) → Ω) (c : Fin (N + 1)) (B : Set (Cpt ξ)) (p : Cpt ξ) (a : Ω), (∀ q ∈ B, Char0 ξ q) → Char0 ξ p → InChart ξ x c p → a ∈ Mdl.chartQ x c → unitAt ξ p a → (∀ q ∈ B, InChart ξ x c q → ¬ unitAt ξ q a) → ∃ G ∈ Mdl.bdGens ξ x B, unitAt ξ p (Mdl.ratEval x c G) := by
  intro Ω _ _ X ξ N x c B p a hB hp hc ha hu hnon
  obtain ⟨m, d, H, hm, hH, hv⟩ := exists_form x hc.1 ha
  exact exists_form_sep hB hp hc (fun q hq hcq => chartQ_le hq hcq ha) hu hnon hm hH hv

end GlobalTheory.CompanionTheory.Ar.SncBase.Mdl.Sep
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.BoundaryPointsCoords
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.SncBase.Mdl

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase

theorem eval_map_mul_of_isHomogeneous {σ : Type} [Fintype σ] {G : MvPolynomial σ ℤ} {d : ℕ} (hG : G.IsHomogeneous d)
    (r : σ → ℂ) (t : ℂ) :
    MvPolynomial.eval (fun i => r i * t) (MvPolynomial.map (Int.castRingHom ℂ) G) =
      t ^ d * MvPolynomial.eval r (MvPolynomial.map (Int.castRingHom ℂ) G) := by
  have hP : (MvPolynomial.map (Int.castRingHom ℂ) G).IsHomogeneous d := hG.map _
  rw [MvPolynomial.eval_eq', MvPolynomial.eval_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hd : ∑ i, m i = d := by
    have := hP (MvPolynomial.mem_support_iff.1 hm)
    simpa [Finsupp.weight_apply, Finsupp.sum_fintype] using this
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hd]
  ring

theorem exists_ratEval_val {Ω : Type} [Field Ω] {N : ℕ} {S : Subring Ω} (φ : S →+* ℂ) (x : Fin (N + 1) → Ω)
    (c : Fin (N + 1)) (r : Fin (N + 1) → ℂ) (hreg : ∀ i, x i / x c ∈ S) (hval : ∀ i, φ ⟨_, hreg i⟩ = r i)
    (G : MRing (fun _ : Unit => Fin (N + 1))) :
    ∃ ha : ratEval x c G ∈ S, φ ⟨_, ha⟩ =
      MvPolynomial.eval (fun p : (Σ _ : Unit, Fin (N + 1)) => r p.2) (MvPolynomial.map (Int.castRingHom ℂ) G) := by
  induction G using MvPolynomial.induction_on with
  | C n =>
    have h : ratEval x c (MvPolynomial.C n) = ((n : S) : Ω) := by simp [ratEval]
    refine ⟨h ▸ (n : S).2, ?_⟩
    have e : (⟨ratEval x c (MvPolynomial.C n), h ▸ (n : S).2⟩ : S) = (n : S) := Subtype.ext h
    rw [e]
    simp
  | add f g hf hg =>
    obtain ⟨ha, hA⟩ := hf
    obtain ⟨hb, hB⟩ := hg
    have h : ratEval x c (f + g) = ((⟨_, ha⟩ + ⟨_, hb⟩ : S) : Ω) := by simp [ratEval]
    refine ⟨h ▸ (⟨_, ha⟩ + ⟨_, hb⟩ : S).2, ?_⟩
    have e : (⟨ratEval x c (f + g), h ▸ (⟨_, ha⟩ + ⟨_, hb⟩ : S).2⟩ : S) = ⟨_, ha⟩ + ⟨_, hb⟩ := Subtype.ext h
    rw [e, map_add (f := _), hA, hB]
    simp
  | mul_X f i hf =>
    obtain ⟨ha, hA⟩ := hf
    have h : ratEval x c (f * MvPolynomial.X i) = ((⟨_, ha⟩ * ⟨_, hreg i.2⟩ : S) : Ω) := by simp [ratEval]
    refine ⟨h ▸ (⟨_, ha⟩ * ⟨_, hreg i.2⟩ : S).2, ?_⟩
    have e : (⟨ratEval x c (f * MvPolynomial.X i), h ▸ (⟨_, ha⟩ * ⟨_, hreg i.2⟩ : S).2⟩ : S) =
        ⟨_, ha⟩ * ⟨_, hreg i.2⟩ := Subtype.ext h
    rw [e, map_mul, hA, hval]
    simp

theorem mem_mcPts_span_bdGens_iff : ∀ (Ω : Type) [Field Ω] (X : Scheme.{0}) (ξ : Sp Ω ⟶ X) (N : ℕ)
    (x : Fin (N + 1) → Ω) (B : Set (Cpt ξ)), IsCptGen ξ →
    (∀ c (p : Cpt ξ), Char0 ξ p → InChart ξ x c p → p ∉ B → ∃ G ∈ Mdl.bdGens ξ x B, unitAt ξ p (Mdl.ratEval x c G)) →
    ∀ (z : Spec (CommRingCat.of ℂ) ⟶ X) w, CoordsAt ξ (fun p : (Σ _ : Unit, Fin (N + 1)) => x p.2) z w →
      (w ∈ mcPts (Ideal.span (Mdl.bdGens ξ x B)) ↔ ∃ h : genPt ξ ⤳ centre z, (⟨centre z, h⟩ : Cpt ξ) ∈ B) := by
  intro Ω _ X ξ N x B hξ hB z w hC
  obtain ⟨hu, hco⟩ := hC
  obtain ⟨c, hc⟩ := hu ()
  obtain ⟨hxc, hr⟩ := hco () c hc
  choose r hrV hrw using hr
  obtain ⟨h, -⟩ := hrV c
  obtain ⟨φ, hφ, hφu⟩ := ValHom.exists_valAt_hom X Ω ξ ℂ z h hξ
  have hreg : ∀ i, x i / x c ∈ regAt ξ ⟨centre z, h⟩ := fun i => ((hφ _ _).1 (hrV i)).choose
  have hval : ∀ i, φ ⟨_, hreg i⟩ = r i := fun i => ((hφ _ _).1 (hrV i)).choose_spec
  have hchart : InChart ξ x c ⟨centre z, h⟩ := ⟨hxc, hreg⟩
  have hp0 : Char0 ξ ⟨centre z, h⟩ := char_zero_centre_complex_point Ω X ξ z h hξ
  have hw0 : w ⟨(), c⟩ ≠ 0 := hc.ne_zero
  have hw : w = fun p : (Σ _ : Unit, Fin (N + 1)) => r p.2 * w ⟨(), c⟩ := by
    funext ⟨u, i⟩
    exact hrw i

  have key : ∀ (G : MRing (fun _ : Unit => Fin (N + 1))) (d : ℕ), G.IsHomogeneous d →
      (MvPolynomial.eval w (MvPolynomial.map (Int.castRingHom ℂ) G) = 0 ↔
        ¬ unitAt ξ ⟨centre z, h⟩ (ratEval x c G)) := by
    intro G d hG
    obtain ⟨ha, hA⟩ := exists_ratEval_val φ x c r hreg hval G
    have hu' := hφu ⟨_, ha⟩
    rw [hw, eval_map_mul_of_isHomogeneous hG, ← hA]
    simp only [mul_eq_zero, pow_eq_zero_iff', hw0, false_and, false_or]
    rw [← show IsUnit (φ ⟨_, ha⟩) ↔ unitAt ξ ⟨centre z, h⟩ (ratEval x c G) from hu', isUnit_iff_ne_zero, not_not]
  constructor
  · rintro ⟨-, hv⟩
    refine ⟨h, ?_⟩
    by_contra hpB
    obtain ⟨G, hG, hGu⟩ := hB c ⟨centre z, h⟩ hp0 hchart hpB
    obtain ⟨d, hd, -⟩ := id hG
    exact (key G d hd).1 (hv G (Ideal.subset_span hG)) hGu
  · rintro ⟨h', hpB⟩
    refine ⟨fun _ => ⟨c, hw0⟩, fun f hf => ?_⟩
    induction hf using Submodule.span_induction with
    | mem G hG =>
      obtain ⟨d, hd, hv⟩ := hG
      exact (key G d hd).2 (hv c _ hpB hchart)
    | zero => simp
    | add f g _ _ hf hg => simp [hf, hg]
    | smul a f _ hf => simp [hf]

end GlobalTheory.CompanionTheory.Ar.SncBase.Mdl
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CharZeroIffNonzeroUnitsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.char_zero_iff_nonzero_units : ∀ (F : Type) [Field F] [NumberField F] (Ω : Type) [Field Ω] [Algebra (𝓞 F) Ω] (X : Scheme.{0}) (ξ : Sp Ω ⟶ X) (κ : Type) (t : κ → Ω), CoordTie (𝓞 F) ξ t → ∀ p : Cpt ξ, Char0 ξ p ↔ ∀ d : 𝓞 F, d ≠ 0 → unitAt ξ p (algebraMap (𝓞 F) Ω d) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SncBase.CharTie.char_zero_iff_integers_units | exact GlobalTheory.CompanionTheory.Ar.SncBase.CharTie.char_zero_iff_integers_units | (intros; apply GlobalTheory.CompanionTheory.Ar.SncBase.CharTie.char_zero_iff_integers_units <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ChartPrimeGivesComponent
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase

namespace GlobalTheory.CompanionTheory.Ar.SncBase.Mdl

section Alg

variable {Ω : Type} [Field Ω] [CharZero Ω] [Algebra ℚ Ω] {κ : Type}

abbrev chartZ (x : κ → Ω) (c : κ) : Subalgebra ℤ Ω :=
  Algebra.adjoin ℤ (Set.range fun j => x j / x c)

theorem chartZ_le (x : κ → Ω) (c : κ) {t : Ω} (ht : t ∈ chartZ x c) : t ∈ chartQ x c := by
  induction ht using Algebra.adjoin_induction with
  | mem a ha => exact Algebra.subset_adjoin ha
  | algebraMap r => simpa using intCast_mem (chartQ x c) r
  | add a b _ _ ha hb => exact add_mem ha hb
  | mul a b _ _ ha hb => exact mul_mem ha hb

theorem exists_natCast_mul_mem (x : κ → Ω) (c : κ) {s : Ω} (hs : s ∈ chartQ x c) :
    ∃ m : ℕ, m ≠ 0 ∧ (m : Ω) * s ∈ chartZ x c := by
  induction hs using Algebra.adjoin_induction with
  | mem a ha => exact ⟨1, one_ne_zero, by simpa using Algebra.subset_adjoin ha⟩
  | algebraMap r =>
    refine ⟨r.den, r.den_nz, ?_⟩
    have hd : (r.den : Ω) ≠ 0 := Nat.cast_ne_zero.2 r.den_nz
    have e : (r.den : Ω) * algebraMap ℚ Ω r = (r.num : Ω) := by
      rw [eq_ratCast, Rat.cast_def]
      field_simp
    rw [e]
    exact intCast_mem _ _
  | add a b _ _ ha hb =>
    obtain ⟨k, hk0, hk⟩ := ha
    obtain ⟨l, hl0, hl⟩ := hb
    refine ⟨k * l, mul_ne_zero hk0 hl0, ?_⟩
    have e : ((k * l : ℕ) : Ω) * (a + b) = (l : Ω) * ((k : Ω) * a) + (k : Ω) * ((l : Ω) * b) := by
      push_cast
      ring
    rw [e]
    exact add_mem (mul_mem (natCast_mem _ _) hk) (mul_mem (natCast_mem _ _) hl)
  | mul a b _ _ ha hb =>
    obtain ⟨k, hk0, hk⟩ := ha
    obtain ⟨l, hl0, hl⟩ := hb
    refine ⟨k * l, mul_ne_zero hk0 hl0, ?_⟩
    have e : ((k * l : ℕ) : Ω) * (a * b) = ((k : Ω) * a) * ((l : Ω) * b) := by
      push_cast
      ring
    rw [e]
    exact mul_mem hk hl

def chartIncl (x : κ → Ω) (c : κ) : chartZ x c →+* chartQ x c :=
  ((chartZ x c).val : chartZ x c →+* Ω).codRestrict (chartQ x c) fun t => chartZ_le x c t.2

theorem natCast_notMem_chartQ (x : κ → Ω) (c : κ) {I : Ideal (chartQ x c)} (hI : I.IsPrime) {m : ℕ}
    (hm : m ≠ 0) : (m : chartQ x c) ∉ I := by
  intro h
  apply hI.ne_top
  rw [Ideal.eq_top_iff_one]
  have hd : (m : Ω) ≠ 0 := Nat.cast_ne_zero.2 hm
  have hi : (m : Ω)⁻¹ ∈ chartQ x c := by
    have := (chartQ x c).algebraMap_mem ((m : ℚ)⁻¹)
    simpa using this
  have e : (⟨(m : Ω)⁻¹, hi⟩ : chartQ x c) * (m : chartQ x c) = 1 :=
    Subtype.ext (by simp [hd])
  rw [← e]
  exact I.mul_mem_left _ h

theorem natCast_mul_notMem_iff (x : κ → Ω) (c : κ) {I : Ideal (chartQ x c)} (hI : I.IsPrime) {m : ℕ}
    (hm : m ≠ 0) (s : chartQ x c) : (m : chartQ x c) * s ∉ I ↔ s ∉ I := by
  refine not_congr ⟨fun h => ?_, fun h => I.mul_mem_left _ h⟩
  exact (hI.mem_or_mem h).resolve_left (natCast_notMem_chartQ x c hI hm)

end Alg

section Pts

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] [CharZero Ω] [Algebra ℚ Ω] {κ : Type}

theorem notMem_comap_iff {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (I : Ideal B) (P : A → Prop)
    (h : ∀ t, t ∉ I.comap f ↔ P t) (t : A) : f t ∉ I ↔ P t := by
  rw [← h t, Ideal.mem_comap]

theorem algebraMap_mem_regAt {ξ : Spec (CommRingCat.of Ω) ⟶ X} {p : Cpt ξ} (hp : Char0 ξ p) (r : ℚ) :
    algebraMap ℚ Ω r ∈ regAt ξ p := by
  have e : algebraMap ℚ Ω r = (r.num : Ω) * ((r.den : Ω))⁻¹ := by
    rw [eq_ratCast, Rat.cast_def, div_eq_mul_inv]
  rw [e]
  exact (regAt ξ p).mul_mem (intCast_mem _ _) (Char0.unitAt_natCast hp r.den_nz).2.2

theorem chartQ_le_regAt {ξ : Spec (CommRingCat.of Ω) ⟶ X} {x : κ → Ω} {c : κ} {p : Cpt ξ} (hp : Char0 ξ p)
    (hc : InChart ξ x c p) {s : Ω} (hs : s ∈ chartQ x c) : s ∈ regAt ξ p := by
  induction hs using Algebra.adjoin_induction with
  | mem a ha => obtain ⟨j, rfl⟩ := ha; exact hc.2 j
  | algebraMap r => exact algebraMap_mem_regAt hp r
  | add a b _ _ ha hb => exact (regAt ξ p).add_mem ha hb
  | mul a b _ _ ha hb => exact (regAt ξ p).mul_mem ha hb

theorem char_zero_of_chart_inclusion {ξ : Spec (CommRingCat.of Ω) ⟶ X} {x : κ → Ω} {c : κ} {I : Ideal (chartQ x c)}
    (hI : I.IsPrime) {p : Cpt ξ} (hp : ∀ t : chartZ x c, chartIncl x c t ∉ I ↔ unitAt ξ p (t : Ω)) :
    Char0 ξ p := by
  intro r hr hF
  apply hF
  have h := (hp ⟨(r : Ω), natCast_mem _ r⟩).1
  apply h
  have e : chartIncl x c ⟨(r : Ω), natCast_mem _ r⟩ = (r : chartQ x c) := Subtype.ext (by simp [chartIncl])
  rw [e]
  exact natCast_notMem_chartQ x c hI hr.ne_zero

theorem notMem_iff_unitAt {ξ : Spec (CommRingCat.of Ω) ⟶ X} {x : κ → Ω} {c : κ} {I : Ideal (chartQ x c)}
    (hI : I.IsPrime) {p : Cpt ξ} (hchar : Char0 ξ p) (hc : InChart ξ x c p)
    (hp : ∀ t : chartZ x c, chartIncl x c t ∉ I ↔ unitAt ξ p (t : Ω)) (s : chartQ x c) :
    s ∉ I ↔ unitAt ξ p (s : Ω) := by
  obtain ⟨m, hm, hms⟩ := exists_natCast_mul_mem x c s.2
  have e : chartIncl x c ⟨_, hms⟩ = (m : chartQ x c) * s := Subtype.ext (by simp [chartIncl])
  have h1 := hp ⟨_, hms⟩
  rw [e, natCast_mul_notMem_iff x c hI hm] at h1
  rw [h1]
  constructor
  · intro h
    exact unitAt_of_mul_right h (natCast_mem _ m) (chartQ_le_regAt hchar hc s.2)
  · intro h
    exact unitAt_mul (Char0.unitAt_natCast hchar hm) h

theorem isLocAt_of_unit {ξ : Spec (CommRingCat.of Ω) ⟶ X} {x : κ → Ω} {c : κ} {I : Ideal (chartQ x c)}
    {p : Cpt ξ} (hchar : Char0 ξ p) (hc : InChart ξ x c p)
    (hreg : ∀ a : Ω, a ∈ regAt ξ p ↔ ∃ s ∈ chartZ x c, unitAt ξ p s ∧ s * a ∈ chartZ x c)
    (hunit : ∀ s : chartQ x c, s ∉ I ↔ unitAt ξ p (s : Ω)) : IsLocAt (chartQ x c) I (regAt ξ p) := by
  refine fun a => ⟨fun ha => ?_, ?_⟩
  · obtain ⟨s, hs, hsu, hsa⟩ := (hreg a).1 ha
    exact ⟨⟨s, chartZ_le x c hs⟩, (hunit _).2 hsu, chartZ_le x c hsa⟩
  · rintro ⟨s, hs, hsa⟩
    have hu := (hunit s).1 hs
    have e : a = (s : Ω)⁻¹ * ((s : Ω) * a) := by
      rw [inv_mul_cancel_left₀ hu.1]
    rw [e]
    exact (regAt ξ p).mul_mem hu.2.2 (chartQ_le_regAt hchar hc hsa)

theorem chart_prime_component_point (ξ : Spec (CommRingCat.of Ω) ⟶ X) (x : κ → Ω) (c : κ)
    (hT : CoordTie ℤ ξ x) (hc0 : x c ≠ 0) (I : Ideal (chartQ x c)) (hI : I.IsPrime) :
    ∃ p : Cpt ξ, Char0 ξ p ∧ InChart ξ x c p ∧ (∀ s : chartQ x c, s ∉ I ↔ unitAt ξ p (s : Ω)) ∧
      IsLocAt (chartQ x c) I (regAt ξ p) := by
  have hJ : (I.comap (chartIncl x c)).IsPrime := Ideal.comap_isPrime _ _
  obtain ⟨p, ⟨hc, hp⟩, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.chart_point_of_prime X Ω ξ ℤ κ x hT c hc0 _ hJ
  have hp' := notMem_comap_iff (chartIncl x c) I (fun t => unitAt ξ p (t : Ω)) hp
  have hchar : Char0 ξ p := char_zero_of_chart_inclusion hI hp'
  have hunit := notMem_iff_unitAt hI hchar hc hp'
  exact ⟨p, hchar, hc, hunit, isLocAt_of_unit hchar hc (_root_.GlobalTheory.CompanionTheory.Ar.regAt_iff_exists_chart_fraction X Ω ξ ℤ κ x hT c p hc) hunit⟩

end Pts

theorem chartPrime_point : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (X : Scheme.{0}) (ξ : Sp Ω ⟶ X) (κ : Type) (x : κ → Ω) (c : κ), CoordTie ℤ ξ x → x c ≠ 0 → ∀ I : Ideal (Mdl.chartQ x c), I.IsPrime → ∃ p : Cpt ξ, Char0 ξ p ∧ InChart ξ x c p ∧ (∀ s : Mdl.chartQ x c, s ∉ I ↔ unitAt ξ p (s : Ω)) ∧ IsLocAt (Mdl.chartQ x c) I (regAt ξ p) :=
  fun _ _ _ _ ξ _ x c hT hc0 I hI => chart_prime_component_point ξ x c hT hc0 I hI

end GlobalTheory.CompanionTheory.Ar.SncBase.Mdl
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComplexPointsDenseNonvanishing
section
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem nonvanishing_dense : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (d : ℕ) (f : MRing ι), IsArithVar P d → f ∉ P → mcPts P ⊆ closure {z | z ∈ mcPts P ∧ evC z f ≠ 0} := by
  exact @PositivityTheory.Xgn.nonvanishing_points_dense

end GlobalTheory.CompanionTheory.Ar.Flat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordsSingleBlockSegreStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coords_single_block_segre : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (N : ℕ) (x : Fin (N + 1) → Ω), CoordTie ℤ ξ x → CoordTie ℤ ξ (fun c' : (k : Unit) → (fun _ : Unit => Fin (N + 1)) k => ∏ k, (fun p : (Σ _ : Unit, Fin (N + 1)) => x p.2) ⟨k, c' k⟩) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SncBase.Reindex.coordTie_one_block | exact GlobalTheory.CompanionTheory.Ar.SncBase.Reindex.coordTie_one_block | (intros; apply GlobalTheory.CompanionTheory.Ar.SncBase.Reindex.coordTie_one_block <;> assumption)
end

