module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsLatFamilyCongr
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0017
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0068
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0014
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0019
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0002
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0017
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0056
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0062
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0066
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0032
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0036
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.StalkSpecializesBijective
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0037
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0012

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CmEmbeddingConjugateCompat
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Num.FamEx.Lab

theorem exists_labelEmbedding : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (t : CMType H ⊕ CMType H), ∃ σ : E →+* Ω, (∀ a : 𝓞 E, σ (a : E) = 𝔐.emb t a) ∧ (∀ a : 𝓞 E, (σ.comp (HT.cmConj E).toRingHom) (a : E) = 𝔐.emb t.swap a) ∧ ∀ σ' : E →+* Ω, (∀ a : 𝓞 E, σ' (a : E) = 𝔐.emb t a) → σ' = σ := by
  intro E _ _ _ H D l Xo c O₀ _ β Y S Ω _ K _ J y 𝔐 t
  have uniq : ∀ f g : E →+* Ω, (∀ a : 𝓞 E, f (a : E) = g (a : E)) → f = g := by
    intro f g h
    apply IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E))
    ext a
    exact h a
  rcases t with τ | τ
  · let σ : E →+* Ω := 𝔐.cst.comp (τ.1.codRestrict c.F (c.conj τ.1))
    have h1 : ∀ a : 𝓞 E, σ (a : E) = 𝔐.emb (Sum.inl τ) a := fun a => rfl
    refine ⟨σ, h1, ?_, fun σ' h => uniq _ _ (fun a => (h a).trans (h1 a).symm)⟩
    intro a
    change 𝔐.cst (τ.1.codRestrict c.F (c.conj τ.1) (NumberField.IsCMField.complexConj E (a : E))) =
      𝔐.cst (τ.1.codRestrict c.F (c.conj τ.1) ((H.bar a : 𝓞 E) : E))
    rw [H.bar_eq a]
  · let σ : E →+* Ω :=
      𝔐.cst.comp ((τ.1.codRestrict c.F (c.conj τ.1)).comp (GlobalTheory.CompanionTheory.Ar.HT.cmConj E).toRingHom)
    have h1 : ∀ a : 𝓞 E, σ (a : E) = 𝔐.emb (Sum.inr τ) a := by
      intro a
      change 𝔐.cst (τ.1.codRestrict c.F (c.conj τ.1) (NumberField.IsCMField.complexConj E (a : E))) =
        𝔐.cst (τ.1.codRestrict c.F (c.conj τ.1) ((H.bar a : 𝓞 E) : E))
      rw [H.bar_eq a]
    refine ⟨σ, h1, ?_, fun σ' h => uniq _ _ (fun a => (h a).trans (h1 a).symm)⟩
    intro a
    change 𝔐.cst (τ.1.codRestrict c.F (c.conj τ.1)
        (NumberField.IsCMField.complexConj E (NumberField.IsCMField.complexConj E (a : E)))) =
      𝔐.cst (τ.1.codRestrict c.F (c.conj τ.1) (a : E))
    rw [NumberField.IsCMField.complexConj_apply_apply]

end GlobalTheory.CompanionTheory.Ar.Num.FamEx.Lab
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentGivesChartPrime
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.SncBase.Mdl

theorem adjoin_int_le_chartQ {Ω : Type} [Field Ω] [Algebra ℚ Ω] {κ : Type} (x : κ → Ω) (c : κ) {a : Ω}
    (ha : a ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c)) : a ∈ chartQ x c := by
  induction ha using Algebra.adjoin_induction with
  | mem a ha => exact Algebra.subset_adjoin ha
  | algebraMap r => simpa using intCast_mem (chartQ x c) r
  | add a b _ _ ha hb => exact (chartQ x c).add_mem ha hb
  | mul a b _ _ ha hb => exact (chartQ x c).mul_mem ha hb

theorem exists_prime_of_chart {Ω : Type} [Field Ω] [Algebra ℚ Ω] {X : Scheme.{0}}
    {ξ : Spec (CommRingCat.of Ω) ⟶ X} {κ : Type} {x : κ → Ω} {c : κ} (hξ : IsCptGen ξ) {p : Cpt ξ}
    (hle : ∀ s ∈ chartQ x c, s ∈ regAt ξ p)
    (hdict : ∀ a ∈ regAt ξ p, ∃ s ∈ chartQ x c, unitAt ξ p s ∧ s * a ∈ chartQ x c) :
    ∃ I : Ideal (chartQ x c), I.IsPrime ∧ (∀ s : chartQ x c, s ∉ I ↔ unitAt ξ p (s : Ω)) ∧
      IsLocAt (chartQ x c) I (regAt ξ p) := by
  haveI hloc : IsLocalRing (regAt ξ p) := (regAt_isLocalRing_isFractionRing_stalk X Ω ξ hξ p).1
  have hmem : ∀ s : chartQ x c, (s : Ω) ∈ regAt ξ p := fun s => hle _ s.2
  let f : chartQ x c →+* regAt ξ p :=
    ((chartQ x c).val : chartQ x c →+* Ω).codRestrict (regAt ξ p) hmem
  have hI : (Ideal.comap f (IsLocalRing.maximalIdeal (regAt ξ p))).IsPrime := inferInstance
  have hu : ∀ s : chartQ x c,
      s ∉ Ideal.comap f (IsLocalRing.maximalIdeal (regAt ξ p)) ↔ unitAt ξ p (s : Ω) := by
    intro s
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]
    constructor
    · intro hu
      obtain ⟨b, hb⟩ := hu.exists_right_inv
      have e1 : (s : Ω) * (b : Ω) = 1 := congrArg Subtype.val hb
      have h0 : (s : Ω) ≠ 0 := fun h0 => by simp [h0] at e1
      refine ⟨h0, hmem s, ?_⟩
      rw [inv_eq_of_mul_eq_one_right e1]
      exact b.2
    · rintro ⟨h0, -, hinv⟩
      exact isUnit_iff_exists_inv.2 ⟨⟨_, hinv⟩, Subtype.ext (mul_inv_cancel₀ h0)⟩
  refine ⟨_, hI, hu, fun a => ⟨fun ha => ?_, ?_⟩⟩
  · obtain ⟨s, hs, hus, hsa⟩ := hdict a ha
    exact ⟨⟨s, hs⟩, (hu ⟨s, hs⟩).2 hus, hsa⟩
  · rintro ⟨s, hs, hsa⟩
    have hus := (hu s).1 hs
    have e : a = ((s : Ω) * a) * (s : Ω)⁻¹ := by
      field_simp [hus.1]
    rw [e]
    exact (regAt ξ p).mul_mem (hle _ hsa) hus.2.2

theorem exists_prime_chartQ : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (X : Scheme.{0}) (ξ : Sp Ω ⟶ X) (κ : Type) (x : κ → Ω) (c : κ), CoordTie ℤ ξ x → ∀ p : Cpt ξ, Char0 ξ p → InChart ξ x c p → ∃ I : Ideal (Mdl.chartQ x c), I.IsPrime ∧ (∀ s : Mdl.chartQ x c, s ∉ I ↔ unitAt ξ p (s : Ω)) ∧ IsLocAt (Mdl.chartQ x c) I (regAt ξ p) := by
  intro Ω _ _ X ξ κ x c hT p hp hc
  refine exists_prime_of_chart hT.gen (fun s hs => chartQ_le hp hc hs) fun a ha => ?_
  obtain ⟨s, hs, hus, hsa⟩ := (_root_.GlobalTheory.CompanionTheory.Ar.regAt_iff_exists_chart_fraction X Ω ξ ℤ κ x hT c p hc a).1 ha
  exact ⟨s, adjoin_int_le_chartQ x c hs, hus, adjoin_int_le_chartQ x c hsa⟩

end GlobalTheory.CompanionTheory.Ar.SncBase.Mdl
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsIsometricHermLine
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver)

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem twist_line : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MvPolynomial (Σ k, ι k) ℤ)) (D : ℕ), IsArithVar P (D + 1) → ∀ (S : Finset Nat.Primes) (T : LocPair ι ℤ Unit), T.IsVertOff P S → ∀ A : HermLine ι, A.a = T.x () → IsSmoothHerm A → IsConjInvariantH A → ∃ A' : HermLine ι, IsSmoothHerm A' ∧ IsConjInvariantH A' ∧ T.IsIsometric P (fun _ => A) (fun _ => A') := by
  intro K _ _ ι _ P D hP S T hT A hAx hAs hAc
  obtain ⟨_, ⟨hPp, hPh, _⟩, _, _⟩ := hP
  have hPh' := _root_.GlobalTheory.CompanionTheory.Ggeo.CompMem.comp_mem K ι P hPh
  obtain ⟨⟨bf, bg, hf, hg, hdeg⟩, hfP, hgP, hW⟩ := hT ()
  generalize hfd : T.f () = f at *
  generalize hgd : T.g () = g at *
  let Q : (K → ℕ) → (K → ℕ) → MvPolynomial (Σ k, ι k) ℤ → MvPolynomial (Σ k, ι k) ℤ → Prop :=
    fun a b u v => GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog u a ∧
      GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog v b ∧ a + bf = b + bg ∧ u * f - v * g ∈ P
  have hQmul : ∀ (a b d : K → ℕ) (u v m : MvPolynomial (Σ k, ι k) ℤ), Q a b u v →
      GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog m d → Q (a + d) (b + d) (u * m) (v * m) := by
    rintro a b d u v m ⟨hu, hv, hab, hr⟩ hm
    refine ⟨hu.mul hm, hv.mul hm, ?_, ?_⟩
    · rw [add_right_comm, hab, add_right_comm]
    · have : u * m * f - v * m * g = m * (u * f - v * g) := by ring
      rw [this]
      exact P.mul_mem_left _ hr
  have hcompP : ∀ z ∈ mcPts P, ∀ (a : K → ℕ) (s : MvPolynomial (Σ k, ι k) ℤ),
      eval z (MvPolynomial.map (Int.castRingHom ℂ) s) ≠ 0 → s ∉ P := fun z hz _ s hs hm =>
    hs (hz.2 s hm)
  have hin : ∀ z ∈ mcPts P, (∃ (a b : K → ℕ) (u v : MvPolynomial (Σ k, ι k) ℤ), Q a b u v ∧
        eval z (MvPolynomial.map (Int.castRingHom ℂ) u) ≠ 0) ∧
      (∃ (a b : K → ℕ) (u v : MvPolynomial (Σ k, ι k) ℤ), Q a b u v ∧
        eval z (MvPolynomial.map (Int.castRingHom ℂ) v) ≠ 0) := by
    intro z hz
    obtain ⟨W, hWp, hPW, hWr, hWc, hWs⟩ := _root_.GlobalTheory.CompanionTheory.Ggeo.TorusOrbit.exists_orbit_prime K ι P z hPh' hz
    obtain ⟨u₀, v₀, hu₀, hv₀, hr⟩ := hW W hWp hPW hWr (fun p _ => hWc p)
    constructor
    · obtain ⟨a, ha⟩ := hWs u₀ hu₀
      obtain ⟨b, v, hv, hab, hr'⟩ := _root_.GlobalTheory.CompanionTheory.Ggeo.multihomog_component_relation K ι P hPp hPh' f g u₀ v₀ bf bg a hf hg hfP hr
        (hcompP z hz a _ ha)
      exact ⟨a, b, _, v, ⟨weightedHomogeneousComponent_isWeightedHomogeneous a u₀, hv, hab, hr'⟩, ha⟩
    · obtain ⟨b, hb⟩ := hWs v₀ hv₀
      have hr₂ : v₀ * g - u₀ * f ∈ P := by
        have := P.neg_mem hr
        rwa [neg_sub] at this
      obtain ⟨a, u, hu, hab, hr'⟩ := _root_.GlobalTheory.CompanionTheory.Ggeo.multihomog_component_relation K ι P hPp hPh' g f v₀ u₀ bg bf b hg hf hgP hr₂
        (hcompP z hz b _ hb)
      refine ⟨a, b, u, _, ⟨hu, weightedHomogeneousComponent_isWeightedHomogeneous b v₀, hab.symm, ?_⟩, hb⟩
      have := P.neg_mem hr'
      rwa [neg_sub] at this
  have hout : ∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → z ∉ mcPts P →
      ∃ (a b : K → ℕ) (u v : MvPolynomial (Σ k, ι k) ℤ), Q a b u v ∧
        eval z (MvPolynomial.map (Int.castRingHom ℂ) u) ≠ 0 ∧
        eval z (MvPolynomial.map (Int.castRingHom ℂ) v) ≠ 0 := by
    intro z hc hz
    have : ∃ q ∈ P, eval z (MvPolynomial.map (Int.castRingHom ℂ) q) ≠ 0 := by
      by_contra hne
      push_neg at hne
      exact hz ⟨hc, hne⟩
    obtain ⟨q, hq, hqz⟩ := this
    obtain ⟨a, b, u, v, hu, hv, hab, huP, hvP, huz, hvz⟩ := _root_.GlobalTheory.CompanionTheory.Ggeo.TwistLine.forms_off_vanishing_locus K ι P bf bg z q hPh' hc hq hqz
    refine ⟨a, b, u, v, ⟨hu, hv, hab, ?_⟩, huz, hvz⟩
    exact P.sub_mem (P.mul_mem_right _ huP) (P.mul_mem_right _ hvP)
  obtain ⟨Aₐ, B, n, u, v, hAB, hQ, hu, hv⟩ := _root_.GlobalTheory.CompanionTheory.Ar.TwistLine.finite_pairs_common_bidegree K ι Q bf bg hQmul (fun a b u v h => ⟨h.1, h.2.1, h.2.2.1⟩)
    (fun z hc => by
      by_cases hz : z ∈ mcPts P
      · exact (hin z hz).1
      · obtain ⟨a, b, u, v, h, h1, _⟩ := hout z hc hz
        exact ⟨a, b, u, v, h, h1⟩)
    (fun z hc => by
      by_cases hz : z ∈ mcPts P
      · exact (hin z hz).2
      · obtain ⟨a, b, u, v, h, _, h1⟩ := hout z hc hz
        exact ⟨a, b, u, v, h, h1⟩)
  obtain ⟨A', ha', hs', hc', hh'⟩ := _root_.GlobalTheory.CompanionTheory.TwistLine.twisted_hermitian_line K ι A Aₐ B n u v (fun j => (hQ j).1) (fun j => (hQ j).2.1)
    hu hv hAs hAc
  refine ⟨A', hs', hc', fun _ => ⟨hAx, ?_, fun z hz => ?_⟩⟩
  · rw [ha', hAx]
    funext k
    have h1 := congrFun hdeg k
    have h2 : (Aₐ k : ℤ) + bf k = B k + bg k := by exact_mod_cast congrFun hAB k
    simp only [Pi.sub_apply] at h1
    linarith
  · show ‖eval z (MvPolynomial.map (Int.castRingHom ℂ) (T.f ()))‖ * A'.h z =
      ‖eval z (MvPolynomial.map (Int.castRingHom ℂ) (T.g ()))‖ * A.h z
    rw [hfd, hgd, hh']
    set fz := eval z (MvPolynomial.map (Int.castRingHom ℂ) f)
    set gz := eval z (MvPolynomial.map (Int.castRingHom ℂ) g)
    have hrel : ∀ j, ‖eval z (MvPolynomial.map (Int.castRingHom ℂ) (u j))‖ ^ 2 * ‖fz‖ ^ 2 =
        ‖eval z (MvPolynomial.map (Int.castRingHom ℂ) (v j))‖ ^ 2 * ‖gz‖ ^ 2 := by
      intro j
      have h0 := hz.2 _ (hQ j).2.2.2
      simp only [map_sub, map_mul] at h0
      have h1 := sub_eq_zero.mp h0
      have h2 := congrArg norm h1
      rw [norm_mul, norm_mul] at h2
      rw [← mul_pow, ← mul_pow, h2]
    have hD : 0 < ∑ j, ‖eval z (MvPolynomial.map (Int.castRingHom ℂ) (v j))‖ ^ 2 := by
      obtain ⟨j, hj⟩ := hv z hz.1
      exact Finset.sum_pos' (fun _ _ => by positivity) ⟨j, Finset.mem_univ _, by positivity⟩
    have hsum : (∑ j, ‖eval z (MvPolynomial.map (Int.castRingHom ℂ) (u j))‖ ^ 2) * ‖fz‖ ^ 2 =
        (∑ j, ‖eval z (MvPolynomial.map (Int.castRingHom ℂ) (v j))‖ ^ 2) * ‖gz‖ ^ 2 := by
      rw [Finset.sum_mul, Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => hrel j
    have key : ‖fz‖ * Real.sqrt ((∑ j, ‖eval z (MvPolynomial.map (Int.castRingHom ℂ) (u j))‖ ^ 2) /
        (∑ j, ‖eval z (MvPolynomial.map (Int.castRingHom ℂ) (v j))‖ ^ 2)) = ‖gz‖ := by
      rw [← Real.sqrt_sq (norm_nonneg fz), ← Real.sqrt_mul (by positivity)]
      rw [show ‖fz‖ ^ 2 * ((∑ j, ‖eval z (MvPolynomial.map (Int.castRingHom ℂ) (u j))‖ ^ 2) /
        (∑ j, ‖eval z (MvPolynomial.map (Int.castRingHom ℂ) (v j))‖ ^ 2)) = ‖gz‖ ^ 2 by
        field_simp
        linarith]
      exact Real.sqrt_sq (norm_nonneg gz)
    calc ‖fz‖ * (A.h z * _) = (‖fz‖ * Real.sqrt _) * A.h z := by ring
      _ = ‖gz‖ * A.h z := by rw [key]

end GlobalTheory.CompanionTheory.Ar.Num
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsPrimeDividingUniformizer
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Rescar

theorem exists_prime_natCast_mem {R : Type*} [CommRing R] (P : Ideal R) [hP : P.IsPrime]
    (n : ℕ) (hn : n ≠ 0) (hmem : (n : R) ∈ P) : ∃ ℓ : ℕ, ℓ.Prime ∧ (ℓ : R) ∈ P := by
  induction n using Nat.recOnMul with
  | zero => exact absurd rfl hn
  | one =>
    exact absurd (by simpa using hmem : (1 : R) ∈ P) (fun h => hP.ne_top ((Ideal.eq_top_iff_one P).2 h))
  | prime p hp => exact ⟨p, hp, hmem⟩
  | mul a b iha ihb =>
    have ha : a ≠ 0 := fun h => hn (by simp [h])
    have hb : b ≠ 0 := fun h => hn (by simp [h])
    rw [Nat.cast_mul] at hmem
    rcases hP.mem_or_mem hmem with h | h
    · exact iha ha h
    · exact ihb hb h

theorem exists_prime_div_uniformiser (F' : Type) [Field F'] [NumberField F']
    (v : HeightOneSpectrum (𝓞 F')) (π : F') (hπ : v.valuation F' π = WithZero.exp (-1 : ℤ)) :
    ∃ ℓ : ℕ, ℓ.Prime ∧ v.valuation F' ((ℓ : F') / π) ≤ 1 := by
  have hne : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact v.ne_bot
  have hmem : ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 F') ∈ v.asIdeal := by
    simpa using Ideal.absNorm_mem v.asIdeal
  obtain ⟨ℓ, hℓ, hℓmem⟩ := exists_prime_natCast_mem v.asIdeal _ hne hmem
  refine ⟨ℓ, hℓ, ?_⟩
  have hlt : v.valuation F' (ℓ : F') < 1 := by
    have := (v.valuation_lt_one_iff_mem (K := F') (ℓ : 𝓞 F')).2 hℓmem
    simpa using this
  have hle : v.valuation F' (ℓ : F') ≤ WithZero.exp (-1 : ℤ) := by
    rcases eq_or_ne (v.valuation F' (ℓ : F')) 0 with h0 | h0
    · rw [h0]; exact zero_le'
    · obtain ⟨a, ha⟩ : ∃ a : ℤ, v.valuation F' (ℓ : F') = WithZero.exp a :=
        ⟨WithZero.log _, (WithZero.exp_log h0).symm⟩
      rw [ha] at hlt ⊢
      have h1 : a < 0 := by
        rw [← WithZero.exp_zero] at hlt
        exact WithZero.exp_lt_exp.1 hlt
      exact WithZero.exp_le_exp.2 (by omega)
  rw [map_div₀, hπ]
  exact div_le_one_of_le₀ hle zero_le'

end GlobalTheory.CompanionTheory.Ar.Rescar
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExteriorCoeffBaseChangeCompat
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.LinePull

theorem wedge_eq_span_pull {X₀ X : Scheme.{0}} {Ω₀ Ω : Type} [Field Ω₀] [Field Ω]
    {ξ₀ : Spec (CommRingCat.of Ω₀) ⟶ X₀} {ξ : Spec (CommRingCat.of Ω) ⟶ X} {f : X ⟶ X₀} {i : Ω₀ →+* Ω}
    {V₀ V : Type} [AddCommGroup V₀] [Module Ω₀ V₀] [AddCommGroup V] [Module Ω V] {j : V₀ →+ V}
    (hD : GlobalTheory.CompanionTheory.Ar.Dominates ξ ξ₀ f i) (hE : IsExtOver i j) {L₀ : Lat ξ₀ V₀} {L : Lat ξ V} {n : ℕ}
    {a₀ : ⋀[Ω₀]^n V₀} {a : ⋀[Ω]^n V} (x : Cpt ξ) (h : genPt ξ₀ ⤳ f x.1) {u : Fin n → V₀} {α : Ω₀} (hα : α ≠ 0)
    (hF : L₀.IsFrameAt u ⟨f x.1, h⟩) (hL : L x = L₀.pull ξ f j x)
    (hW : L₀.wedge n ⟨f x.1, h⟩ = Submodule.span (regAt ξ₀ ⟨f x.1, h⟩) {α • a₀})
    (hP : CptIn.IsPullWedge i j a₀ a) :
    L.wedge n x = Submodule.span (regAt ξ x) {i α • a} := by
  obtain ⟨_, hreg, -⟩ := pull_reg_and_gen X₀ Ω₀ ξ₀ X Ω ξ f i hD x
  have hF' := FlagPull.pull_isFrameAt hD hE x h hF
  have hFr : L.IsFrameAt (fun k => j (u k)) x := ⟨hF'.1, hL.trans hF'.2⟩
  obtain ⟨hw, -⟩ := WedgeFrame.wedge_eq_span_ιMulti _ _ _ _ L n _ x hFr
  obtain ⟨hw₀, hne⟩ := WedgeFrame.wedge_eq_span_ιMulti _ _ _ _ L₀ n u _ hF
  obtain ⟨ε, hε, e⟩ := ZUnit.exists_of_span_eq hne (hw₀.symm.trans hW)
  have hεα : ε * α ≠ 0 := mul_ne_zero hε.1 hα
  have ha₀ : a₀ = (ε * α)⁻¹ • exteriorPower.ιMulti Ω₀ n u := by
    rw [e, smul_smul, smul_smul, mul_assoc, inv_mul_cancel₀ hεα, one_smul]
  have ha := hP u _ ha₀
  have hne' : i ε ≠ 0 := (map_ne_zero i).2 hε.1
  have hiα : i α ≠ 0 := (map_ne_zero i).2 hα
  have e2 : exteriorPower.ιMulti Ω n (fun k => j (u k)) = i ε • i α • a := by
    rw [ha, smul_smul, smul_smul, ← map_mul, ← map_mul, mul_inv_cancel₀ hεα, map_one, one_smul]
  rw [hw, e2]
  have hu : i ε ∈ regAt ξ x := hreg _ hε.2.1
  have hv : (i ε)⁻¹ ∈ regAt ξ x := by
    rw [← map_inv₀]
    exact hreg _ hε.2.2
  refine le_antisymm ?_ ?_ <;> rw [Submodule.span_singleton_le_iff_mem, Submodule.mem_span_singleton]
  · exact ⟨⟨i ε, hu⟩, rfl⟩
  · refine ⟨⟨(i ε)⁻¹, hv⟩, ?_⟩
    show (i ε)⁻¹ • i ε • i α • a = i α • a
    rw [inv_smul_smul₀ hne']

theorem isCoeffAt_pull : ∀ (X₀ X : Scheme.{0}) (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] (ξ₀ : Spec (CommRingCat.of Ω₀) ⟶ X₀) (ξ : Spec (CommRingCat.of Ω) ⟶ X) (f : X ⟶ X₀) (i : Ω₀ →+* Ω) (V₀ V : Type) [AddCommGroup V₀] [Module Ω₀ V₀] [AddCommGroup V] [Module Ω V] (j : V₀ →+ V) (A₀ B₀ : Lat ξ₀ V₀) (A B : Lat ξ V) (p q : ℕ) (a₀ : ⋀[Ω₀]^p V₀) (b₀ : ⋀[Ω₀]^q V₀) (a : ⋀[Ω]^p V) (b : ⋀[Ω]^q V) (x : Cpt ξ) (x₀ : Cpt ξ₀) (u₁ : Fin p → V₀) (u₂ : Fin q → V₀), IsCptGen ξ₀ → IsCptGen ξ → Dominates ξ ξ₀ f i → IsExtOver i j → x₀.1 = f x.1 → A₀.IsFrameAt u₁ x₀ → B₀.IsFrameAt u₂ x₀ → A x = A₀.pull ξ f j x → B x = B₀.pull ξ f j x → IsCoeffAt A₀ B₀ p q a₀ b₀ x₀ 1 → CptIn.IsPullWedge i j a₀ a → CptIn.IsPullWedge i j b₀ b → IsCoeffAt A B p q a b x 1 := by
  intro X₀ X Ω₀ Ω _ _ ξ₀ ξ f i V₀ V _ _ _ _ j A₀ B₀ A B p q a₀ b₀ a b x x₀ u₁ u₂ _ _ hD hE hx hF₁ hF₂ hA hB hC hPa hPb
  obtain ⟨α, β, hα, -, hAw, hBw, hαβ⟩ := hC
  rw [one_mul] at hαβ
  subst hαβ
  obtain ⟨y, hy⟩ := x₀
  obtain rfl : y = f x.1 := hx
  exact ⟨i α, i α, (map_ne_zero i).2 hα, (map_ne_zero i).2 hα,
    wedge_eq_span_pull hD hE x hy hα hF₁ hA hAw hPa, wedge_eq_span_pull hD hE x hy hα hF₂ hB hBw hPb, one_mul _⟩

end GlobalTheory.CompanionTheory.Ar.Flat.LinePull
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteTypeOverIntegersModel
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.ChartFType

theorem finiteType_of_equiv {A B C : Type} [CommRing A] [CommRing B] [CommRing C] [Algebra ℤ C]
    [Algebra.FiniteType ℤ C] (E : B ≃+* C) (g : ℤ →+* A) (f : A →+* B) : f.FiniteType := by
  have hC : (algebraMap ℤ C).FiniteType := RingHom.finiteType_algebraMap.2 inferInstance
  have hE : (E.symm.toRingHom).FiniteType := RingHom.FiniteType.of_surjective _ E.symm.surjective
  have h1 : ((E.symm.toRingHom).comp (algebraMap ℤ C)).FiniteType := hE.comp hC
  have h2 : f.comp (Int.castRingHom A) = (E.symm.toRingHom).comp (algebraMap ℤ C) := RingHom.ext_int _ _
  rw [← h2] at h1
  exact RingHom.FiniteType.of_comp_finiteType h1

theorem main : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (κ : Type) [Finite κ] (x : κ → Ω), (∀ q : X, genPt ξ ⤳ q) → CoordTie ℤ ξ x → ∃ s : X ⟶ Spec (CommRingCat.of ℤ), LocallyOfFiniteType s ∧ QuasiCompact s ∧ ξ ≫ s = Spec.map (CommRingCat.ofHom (algebraMap ℤ Ω)) := by
  intro X Ω _ ξ κ _ x hall T
  refine ⟨specZIsTerminal.from X, ?_, ?_, specZIsTerminal.hom_ext _ _⟩
  · have hQ := (RingHom.finiteType_stableUnderComposition.stableUnderCompositionWithLocalizationAway
      RingHom.finiteType_holdsForLocalizationAway).1
    rw [HasRingHomProperty.iff_exists_appLE (P := @LocallyOfFiniteType) hQ]
    intro q
    obtain ⟨c, hcq⟩ := T.cover ⟨q, hall q⟩
    obtain ⟨U, hUa, hU⟩ := T.affine c hcq.1
    have hqU : q ∈ U := (hU q).2 ⟨hall q, hcq⟩
    have hg : genPt ξ ∈ U := (hall q).mem_open U.isOpen hqU
    obtain ⟨E, -⟩ := GlobalTheory.CompanionTheory.Ar.ChartSmooth.exists_secEquiv hall T hcq.1 hU hg
    haveI : Algebra.FiniteType ℤ (Algebra.adjoin ℤ (Set.range fun j => x j / x c)) :=
      (Subalgebra.fg_iff_finiteType _).1 (Subalgebra.fg_def.2 ⟨_, Set.finite_range _, rfl⟩)
    exact ⟨⟨⊤, isAffineOpen_top _⟩, ⟨U, hUa⟩, hqU, by simp, finiteType_of_equiv E (Int.castRingHom _) _⟩
  · rw [quasiCompact_iff_compactSpace]
    choose U hUa hU using T.affine
    refine ⟨?_⟩
    have hcov : (Set.univ : Set X) = ⋃ (c : κ) (hc : x c ≠ 0), (U c hc : Set X) := by
      ext q
      simp only [Set.mem_univ, Set.mem_iUnion, true_iff]
      obtain ⟨c, hcq⟩ := T.cover ⟨q, hall q⟩
      exact ⟨c, hcq.1, (hU c hcq.1 q).2 ⟨hall q, hcq⟩⟩
    rw [hcov]
    exact isCompact_iUnion fun c => isCompact_iUnion fun hc => (hUa c hc).isCompact

end GlobalTheory.CompanionTheory.Ar.ChartFType
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FromNAdd
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt

open GlobalTheory.CompanionTheory.Ar.BT

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O₀ : Type} [CommRing O₀] {β : O₀ →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
  {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω}
  {F : Type} [Field F]

abbrev NAdd (E : Type) [Field E] [NumberField E] (n p : ℕ) : Type := Fin n → (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)})

def toNAdd {n p : ℕ} (sc : F →+ (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)})) : (Fin n → F) →+ NAdd E n p where
  toFun a i := sc (a i)
  map_zero' := by ext i; simp
  map_add' a b := by ext i; simp

def fromNAdd {n p : ℕ} (pq : (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)}) →+* F) : NAdd E n p →+ (Fin n → F) where
  toFun t i := pq (t i)
  map_zero' := by ext i; simp
  map_add' a b := by ext i; simp

def bcLin (C : Type) [Field C] [Algebra Ω C] {m n : ℕ} (f : (Fin m → Ω) →ₗ[Ω] (Fin n → Ω)) :
    (Fin m → C) →ₗ[C] (Fin n → C) :=
  Matrix.toLin' ((LinearMap.toMatrix' f).map (algebraMap Ω C))

variable {𝔐 : HodgeCpt Y S y} {p : ℕ} {G : GenTors 𝔐 p} {O : Type} [CommRing O] [Algebra O Ω] {c' : ∀ k, J k}

def testOrd (P : ChartPack G O c') {C : Type} [Field C] [Algebra O C] [Algebra Ω C] (RC : Subalgebra O C) :
    Submodule RC (NAdd E (D.p + D.q) p → C) :=
  Submodule.span RC {f | ∃ g ∈ P.Γ₁.btOrder ⊤, f = fun x =>
    algebraMap Ω C ((g (Multiplicative.ofAdd x) : CR O y c') : Ω)}

def testOrdW (P : ChartPack G O c') (sc : F →+ (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)})) {C : Type} [Field C] [Algebra O C]
    [Algebra Ω C] (RC : Subalgebra O C) : Submodule RC ((Fin (D.p + D.q) → F) → C) :=
  (testOrd P RC).map (LinearMap.funLeft RC C (toNAdd sc : (Fin (D.p + D.q) → F) → NAdd E (D.p + D.q) p))

end GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LogHermitianSumBoundedStatement
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Ht
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_hermitian_sum_bounded : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (J : Type) (A : HermLine ι) (B : J → HermLine ι) (T : Finset J), IsSmoothHerm A → (∀ j, IsSmoothHerm (B j)) → A.a = -∑ j ∈ T, (B j).a → ∃ C : ℝ, ∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ a, z ⟨k, a⟩ ≠ 0) → |Real.log (A.h z) + ∑ j ∈ T, Real.log ((B j).h z)| ≤ C := by
  first | exact @GlobalTheory.CompanionTheory.Ar.CancelBound.log_metrics_bounded | exact GlobalTheory.CompanionTheory.Ar.CancelBound.log_metrics_bounded | (intros; apply GlobalTheory.CompanionTheory.Ar.CancelBound.log_metrics_bounded <;> assumption)
end

