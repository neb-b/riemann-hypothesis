module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0097
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0104
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginCoordField
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.Chg
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Chg.CoverEff

section Gen

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

theorem unitAt_div_of_isGenAt {Λ : Lat ξ Ω} {p : Cpt ξ} {s s' : Ω} (h : Λ.IsGenAt p s) (h' : Λ.IsGenAt p s') :
    unitAt ξ p (s' / s) := by
  obtain ⟨h0, e⟩ := h
  obtain ⟨h0', e'⟩ := h'
  have m1 : s' ∈ Submodule.span (regAt ξ p) {s} := by
    rw [← e, e']; exact Submodule.mem_span_singleton_self s'
  have m2 : s ∈ Submodule.span (regAt ξ p) {s'} := by
    rw [← e', e]; exact Submodule.mem_span_singleton_self s
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 m1
  obtain ⟨r', hr'⟩ := Submodule.mem_span_singleton.1 m2
  have hr1 : (r : Ω) * s = s' := hr
  have hr2 : (r' : Ω) * s' = s := hr'
  refine ⟨div_ne_zero h0' h0, ?_, ?_⟩
  · rw [(div_eq_iff h0).2 hr1.symm]; exact r.2
  · rw [inv_div, (div_eq_iff h0').2 hr2.symm]; exact r'.2

theorem tens_isGenAt {I : Type} [Fintype I] {Λ : I → Lat ξ Ω} (a : I → ℤ) {p : Cpt ξ} {s : I → Ω}
    (h : ∀ i, (Λ i).IsGenAt p (s i)) : (Lat.tens Λ a).IsGenAt p (∏ i, s i ^ a i) := by
  refine ⟨Finset.prod_ne_zero_iff.2 fun i _ => zpow_ne_zero _ (h i).1, le_antisymm ?_ ?_⟩
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨s', hs', rfl⟩
    have hu : unitAt ξ p (∏ i, (s' i / s i) ^ a i) :=
      unitAt.prod _ fun i _ => (unitAt_div_of_isGenAt (h i) (hs' i)).zpow _
    have e : ∏ i, s' i ^ a i = (∏ i, (s' i / s i) ^ a i) * ∏ i, s i ^ a i := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [← mul_zpow, div_mul_cancel₀ _ (h i).1]
    rw [e]
    exact Submodule.mem_span_singleton.2 ⟨⟨_, hu.2.1⟩, rfl⟩
  · refine Submodule.span_mono ?_
    rintro _ rfl
    exact ⟨s, h, rfl⟩

theorem exists_gen_of_tens {I : Type} [Fintype I] {Λ : I → Lat ξ Ω} {a : I → ℤ} {p : Cpt ξ} {t : Ω}
    (h : (Lat.tens Λ a).IsGenAt p t) : ∃ s : I → Ω, ∀ i, (Λ i).IsGenAt p (s i) := by
  by_contra hn
  have hE : {t | ∃ s : I → Ω, (∀ i, (Λ i).IsGenAt p (s i)) ∧ t = ∏ i, s i ^ a i} = ∅ :=
    Set.eq_empty_of_forall_notMem fun _ ⟨s, hs, _⟩ => hn ⟨s, hs⟩
  have m : t ∈ (Lat.tens Λ a) p := by
    rw [h.2]; exact Submodule.mem_span_singleton_self t
  have m' : t ∈ Submodule.span (regAt ξ p) (∅ : Set Ω) := by
    rw [← hE]; exact m
  rw [Submodule.span_empty, Submodule.mem_bot] at m'
  exact h.1 m'

theorem unitAt_of_mul {p : Cpt ξ} {a b : Ω} (hab : unitAt ξ p (a * b)) (hb : unitAt ξ p b) : unitAt ξ p a := by
  have ha : a ≠ 0 := left_ne_zero_of_mul hab.1
  refine ⟨ha, ?_, ?_⟩
  · have e : a = a * b * b⁻¹ := by field_simp [hb.1]
    rw [e]; exact mul_mem hab.2.1 hb.2.2
  · have e : a⁻¹ = (a * b)⁻¹ * b := by field_simp [hb.1]
    rw [e]; exact mul_mem hab.2.2 hb.2.1

end Gen

section Below

variable {X X₀ : Scheme.{0}} {Ω Ω₀ : Type} [Field Ω] [Field Ω₀] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {ξ₀ : Spec (CommRingCat.of Ω₀) ⟶ X₀}

theorem inChart_below {p : Cpt ξ} {p₀ : Cpt ξ₀} (i : Ω₀ →+* Ω)
    (hU : ∀ a : Ω₀, a ∈ regAt ξ₀ p₀ → unitAt ξ p (i a) → unitAt ξ₀ p₀ a)
    (hR : ∀ a : Ω₀, a ∈ regAt ξ₀ p₀ → i a ∈ regAt ξ p) {κ : Type} {x : κ → Ω₀} {a a₀ : κ}
    (h₀ : InChart ξ₀ x a₀ p₀) (h : InChart ξ (fun k => i (x k)) a p) : InChart ξ₀ x a p₀ := by
  have hx : x a ≠ 0 := fun e => h.1 (by simp [e])
  have hu : unitAt ξ₀ p₀ (x a / x a₀) := by
    refine hU _ (h₀.2 a) ⟨(map_ne_zero i).2 (div_ne_zero hx h₀.1), hR _ (h₀.2 a), ?_⟩
    rw [← map_inv₀, inv_div, map_div₀]
    exact h.2 a₀
  refine ⟨hx, fun c => ?_⟩
  have e : x c / x a = x c / x a₀ * (x a / x a₀)⁻¹ := by
    have := h₀.1
    field_simp
  rw [e]
  exact mul_mem (h₀.2 c) hu.2.2

end Below

theorem rootLat_isGenAt {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
    {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
    {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω} {𝔐 : HodgeCpt Y S y}
    (Fl : 𝔐.Flag) (r : RootIx D) {p : Cpt 𝔐.ξ} {g : Ω}
    (hg : ((𝔐.V (HodgeCpt.rootIdx D r).1).gr (Fl.b (HodgeCpt.rootIdx D r).1) (HodgeCpt.rootIdx D r).2).IsGenAt p g) :
    (Fl.rootLat r).IsGenAt p (g ^ HodgeCpt.rootSgn D r) := by
  have := tens_isGenAt (I := Unit)
    (Λ := fun _ => (𝔐.V (HodgeCpt.rootIdx D r).1).gr (Fl.b (HodgeCpt.rootIdx D r).1) (HodgeCpt.rootIdx D r).2)
    (fun _ => HodgeCpt.rootSgn D r) (p := p) (s := fun _ => g) fun _ => hg
  simpa [HodgeCpt.Flag.rootLat] using this

theorem section_on_cover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (Sys : PB.AnSys (Top.dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))) (Fx : FixedData Y Sys) (R : Top.RootModel (CMType H) (D.p + D.q)) (S₀ S : Finset ℕ) (o : RootOrigin Y S₀ R Fx) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (bk : R.K → K) (bx : ∀ k, R.ι k ≃ J (bk k)) (𝔐 : HodgeCpt Y S y) (i : R.Ω →+* Ω) (h : 𝔐.X ⟶ o.𝔐.X) (hd : GlobalTheory.CompanionTheory.Ar.Dominates 𝔐.ξ o.𝔐.ξ h i) (Fl : 𝔐.Flag) (xdeg : RootIx D → K → ℤ) (e : RootIx D → Ω), (∀ k a, y ⟨bk k, bx k a⟩ = i (R.y ⟨k, a⟩)) → GenPull o.Fl Fl i hd → Fl.RootLines xdeg e → (∀ (p : Cpt 𝔐.ξ) (a : R.Ω), a ∈ regAt o.𝔐.ξ (pushCpt hd p) → unitAt 𝔐.ξ p (i a) → unitAt o.𝔐.ξ (pushCpt hd p) a) → (∀ (p : Cpt 𝔐.ξ) (a : R.Ω), a ∈ regAt o.𝔐.ξ (pushCpt hd p) → i a ∈ regAt 𝔐.ξ p) → (∀ x : 𝔐.X, x ∈ abLocus 𝔐.t.G ↔ h x ∈ abLocus o.𝔐.t.G) → ∀ p : Cpt 𝔐.ξ, (∀ r : ℕ, r.Prime → ¬ InFibre 𝔐.ξ r p) → ∀ (a : Fin (Fx.m + 1)) (t : Ω), InChart 𝔐.ξ (fun i' => (i.comp o.g) (Fx.yf i')) a p → (Lat.tens Fl.rootLat fun r => -Fx.n r).IsGenAt p t → (i.comp o.g) Fx.sE * (i.comp o.g) (Fx.yf a) ^ Fx.q' / t ∈ regAt 𝔐.ξ p ∧ (p.1 ∉ abLocus 𝔐.t.G → ¬ unitAt 𝔐.ξ p ((i.comp o.g) Fx.sE * (i.comp o.g) (Fx.yf a) ^ Fx.q' / t)) := by
  intro E _ _ _ H D l Xo c O _ β Y Sys Fx R S₀ S o Ω _ K _ J _ y bk bx 𝔐 i h hd Fl xdeg e hy hG hL hU hR hab p hp a t
    hch ht
  have hp0 : ∀ r : ℕ, r.Prime → ¬ InFibre o.𝔐.ξ r (pushCpt hd p) := by
    intro r hr hf
    apply hf
    have u : unitAt 𝔐.ξ p (r : Ω) := not_not.1 (hp r hr)
    exact hU p (r : R.Ω) (natCast_mem _ r) (by rw [map_natCast]; exact u)
  obtain ⟨c₀, hc₀⟩ := o.𝔐.tie.cover (pushCpt hd p)
  have hprod : ∀ k, R.y ⟨k, c₀ k⟩ ≠ 0 := fun k => (Finset.prod_ne_zero_iff.1 hc₀.1) k (Finset.mem_univ k)
  have ya₀ : o.g (Fx.yf (o.ix.symm (c₀ o.k₀))) = R.y ⟨o.k₀, c₀ o.k₀⟩ := by
    rw [← o.y_eq, Equiv.apply_symm_apply]
  have hch₀ : InChart o.𝔐.ξ (fun i' => o.g (Fx.yf i')) (o.ix.symm (c₀ o.k₀)) (pushCpt hd p) := by
    refine ⟨?_, fun j => ?_⟩
    · show o.g (Fx.yf (o.ix.symm (c₀ o.k₀))) ≠ 0
      rw [ya₀]; exact hprod _
    · show o.g (Fx.yf j) / o.g (Fx.yf (o.ix.symm (c₀ o.k₀))) ∈ _
      rw [ya₀, ← o.y_eq]
      exact Lat.block_ratio_mem hc₀ o.k₀ (o.ix j)
  have hcha : InChart o.𝔐.ξ (fun i' => o.g (Fx.yf i')) a (pushCpt hd p) :=
    inChart_below i (hU p) (hR p) hch₀ hch
  have gens : ∀ r : RootIx D, ∃ g : R.Ω, ((o.𝔐.V (HodgeCpt.rootIdx D r).1).gr (o.Fl.b (HodgeCpt.rootIdx D r).1)
      (HodgeCpt.rootIdx D r).2).IsGenAt (pushCpt hd p) g := by
    intro r
    have hgen : (o.Fl.rootLat r).IsGenAt (pushCpt hd p) ((∏ k, R.y ⟨k, c₀ k⟩ ^ R.xdeg r k) • o.e r) :=
      ⟨smul_ne_zero (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hprod k)) (o.lines r).1,
        (o.lines r).2 _ trivial c₀ hc₀⟩
    obtain ⟨s, hs⟩ := exists_gen_of_tens hgen
    exact ⟨s (), hs ()⟩
  choose g hg using gens
  have ht₀ := tens_isGenAt (fun r => -Fx.n r) fun r => rootLat_isGenAt o.Fl r (hg r)
  have ht₁ : (Lat.tens Fl.rootLat fun r => -Fx.n r).IsGenAt p
      (i (∏ r, (g r ^ HodgeCpt.rootSgn D r) ^ (-Fx.n r))) := by
    have := tens_isGenAt (Λ := Fl.rootLat) (fun r => -Fx.n r) fun r =>
      rootLat_isGenAt Fl r (hG p hp _ _ _ (hg r))
    simpa only [map_prod, map_zpow₀] using this
  have hv := unitAt_div_of_isGenAt ht ht₁
  obtain ⟨hreg, hnu⟩ := o.eff (pushCpt hd p) hp0 a _ hcha ht₀
  have key : (i.comp o.g) Fx.sE * (i.comp o.g) (Fx.yf a) ^ Fx.q' / t =
      i (o.g Fx.sE * o.g (Fx.yf a) ^ Fx.q' / ∏ r, (g r ^ HodgeCpt.rootSgn D r) ^ (-Fx.n r)) *
        (i (∏ r, (g r ^ HodgeCpt.rootSgn D r) ^ (-Fx.n r)) / t) := by
    have h1 := ht₁.1
    have h2 := ht.1
    rw [map_div₀ i (o.g Fx.sE * o.g (Fx.yf a) ^ Fx.q'), div_mul_div_cancel₀ h1, map_mul, map_pow]
    rfl
  rw [key]
  refine ⟨mul_mem (hR p _ hreg) hv.2.1, fun hnab hu => ?_⟩
  exact hnu (fun hm => hnab ((hab p.1).2 hm)) (hU p _ hreg (unitAt_of_mul hu hv))

end GlobalTheory.CompanionTheory.Ar.Chg.CoverEff
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SmoothGenericFibreOfSnc
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncSmooth

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω]

theorem exists_mul_pow_mem (T : Set Ω) {f : Ω} (hf0 : f ≠ 0) {x : Ω}
    (hx : x ∈ Algebra.adjoin ℚ (insert f⁻¹ T)) (hf : f ∈ Algebra.adjoin ℚ T) :
    ∃ n : ℕ, x * f ^ n ∈ Algebra.adjoin ℚ T := by
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    rcases hx with rfl | hx
    · exact ⟨1, by simpa [hf0] using (Algebra.adjoin ℚ T).one_mem⟩
    · exact ⟨0, by simpa using Algebra.subset_adjoin hx⟩
  | algebraMap r => exact ⟨0, by simpa using (Algebra.adjoin ℚ T).algebraMap_mem r⟩
  | add x y _ _ hx hy =>
    obtain ⟨n, hn⟩ := hx
    obtain ⟨m, hm⟩ := hy
    refine ⟨n + m, ?_⟩
    have : (x + y) * f ^ (n + m) = x * f ^ n * f ^ m + y * f ^ m * f ^ n := by ring
    rw [this]
    exact add_mem (mul_mem hn (pow_mem hf m)) (mul_mem hm (pow_mem hf n))
  | mul x y _ _ hx hy =>
    obtain ⟨n, hn⟩ := hx
    obtain ⟨m, hm⟩ := hy
    refine ⟨n + m, ?_⟩
    have : x * y * f ^ (n + m) = x * f ^ n * (y * f ^ m) := by ring
    rw [this]
    exact mul_mem hn hm

theorem isLocalization_away (A S : Subalgebra ℚ Ω) (hle : A ≤ S) (f : A) (hf0 : (f : Ω) ≠ 0)
    (hinv : (f : Ω)⁻¹ ∈ S) (hs : ∀ x ∈ S, ∃ n : ℕ, x * (f : Ω) ^ n ∈ A) :
    @IsLocalization.Away A _ f S _ (Subalgebra.inclusion hle).toRingHom.toAlgebra := by
  letI := (Subalgebra.inclusion hle).toRingHom.toAlgebra
  have hmap : ∀ a : A, ((algebraMap A S a : S) : Ω) = a := fun a => rfl
  have hunit : IsUnit (algebraMap A S f) := by
    refine IsUnit.of_mul_eq_one (⟨(f : Ω)⁻¹, hinv⟩ : S) ?_
    apply Subtype.ext
    rw [Subalgebra.coe_mul, hmap]
    exact mul_inv_cancel₀ hf0
  refine IsLocalization.Away.mk _ hunit ?_ ?_
  · rintro ⟨x, hx⟩
    obtain ⟨n, hn⟩ := hs x hx
    refine ⟨n, ⟨x * (f : Ω) ^ n, hn⟩, ?_⟩
    apply Subtype.ext
    rw [hmap, Subalgebra.coe_mul, Subalgebra.coe_pow, hmap]
  · intro a b hab
    refine ⟨0, ?_⟩
    have : (a : Ω) = b := by rw [← hmap a, ← hmap b, hab]
    rw [Subtype.ext this]

theorem smooth_of_cover (A : Subalgebra ℚ Ω) {m : ℕ} (f a : Fin m → Ω) (hf : ∀ l, f l ∈ A) (ha : ∀ l, a l ∈ A)
    (hsum : ∑ l, a l * f l = 1) (S : Fin m → Subalgebra ℚ Ω) (hle : ∀ l, A ≤ S l)
    (hinv : ∀ l, f l ≠ 0 → (f l)⁻¹ ∈ S l) (hs : ∀ l, f l ≠ 0 → ∀ x ∈ S l, ∃ n : ℕ, x * f l ^ n ∈ A)
    (hsm : ∀ l, f l ≠ 0 → Algebra.Smooth ℚ (S l)) : Algebra.Smooth ℚ A := by
  let s : Set A := {x | (x : Ω) ≠ 0 ∧ ∃ l, (x : Ω) = f l}
  have hspan : Ideal.span s = ⊤ := by
    rw [Ideal.eq_top_iff_one]
    have h1 : (1 : A) = ∑ l, (⟨a l, ha l⟩ : A) * (⟨f l, hf l⟩ : A) := by
      apply Subtype.ext
      rw [Subalgebra.coe_one, ← hsum, AddSubmonoidClass.coe_finsetSum]
      rfl
    rw [h1]
    refine Ideal.sum_mem _ fun l _ => ?_
    by_cases h0 : f l = 0
    · have : (⟨f l, hf l⟩ : A) = 0 := Subtype.ext h0
      rw [this, mul_zero]
      exact Ideal.zero_mem _
    · exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨h0, l, rfl⟩)
  rw [← RingHom.smooth_algebraMap]
  refine RingHom.OfLocalizationSpanTarget.ofIsLocalization RingHom.Smooth.ofLocalizationSpanTarget
    RingHom.Smooth.respectsIso _ s hspan ?_
  rintro ⟨x, hx0, l, hl⟩
  have hx0' : f l ≠ 0 := hl ▸ hx0
  letI alg := (Subalgebra.inclusion (hle l)).toRingHom.toAlgebra
  have hloc : IsLocalization.Away x (S l) :=
    isLocalization_away A (S l) (hle l) x hx0 (hl ▸ hinv l hx0') (hl ▸ hs l hx0')
  refine ⟨S l, inferInstance, alg, hloc, ?_⟩
  have hcomp : (algebraMap A (S l)).comp (algebraMap ℚ A) = algebraMap ℚ (S l) := Subsingleton.elim _ _
  rw [hcomp]
  exact RingHom.smooth_algebraMap.mpr (hsm l hx0')

theorem smoothGenericFibreM_of_isSncModel (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type)
    [Field Ω] [Algebra ℚ Ω] (y : (Σ k, J k) → Ω) (e : ℕ) (bd : Ideal (MRing J))
    (h : Cmp.IsSncModel y e bd) : SmoothGenericFibreM y := by
  intro c hc
  obtain ⟨m, f, a, hf, ha, hsum, hS⟩ := h c hc
  exact smooth_of_cover _ f a hf ha hsum (fun l => Algebra.adjoin ℚ (insert (f l)⁻¹ _))
    (fun l => Algebra.adjoin_mono (Set.subset_insert _ _))
    (fun l _ => Algebra.subset_adjoin (Set.mem_insert _ _))
    (fun l h0 x hx => exists_mul_pow_mem _ h0 hx (hf l))
    (fun l h0 => (hS l h0 _ rfl).1)

end GlobalTheory.CompanionTheory.Ar.Cmp.SncSmooth
end
end

