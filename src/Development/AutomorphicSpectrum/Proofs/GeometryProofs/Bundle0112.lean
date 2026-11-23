module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0097
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0104
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0026
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0100
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0057
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0107
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LeftEqIffLieVecSmul
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0106
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0012
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCompDescentSecond
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.Chg
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Chg.GP

section Frames

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {E : Type} [AddCommGroup E] [Module Ω E]

theorem exists_coeff {r : ℕ} (b b₀ : Fin r → E) (h : ∀ i, GlobalTheory.CompanionTheory.Ar.flagStep Ω b i = GlobalTheory.CompanionTheory.Ar.flagStep Ω b₀ i)
    (hli : LinearIndependent Ω b) (i : Fin r) :
    ∃ t : Ω, t ≠ 0 ∧ b i - t • b₀ i ∈ GlobalTheory.CompanionTheory.Ar.flagStep Ω b₀ i := by
  have hni : b i ∉ GlobalTheory.CompanionTheory.Ar.flagStep Ω b i := hli.notMem_span_image (by simp)
  have h1 : b i ∈ GlobalTheory.CompanionTheory.Ar.flagStep Ω b₀ (i+1) := by rw [← h]; exact Submodule.subset_span ⟨i, by simp, rfl⟩
  rw [GlobalTheory.CompanionTheory.Ar.Flag.step_succ] at h1
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 h1
  obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hz
  have ht : t ≠ 0 := by rintro rfl; apply hni; rw [h, ← hyz]; simpa using hy
  exact ⟨t, ht, by rw [← hyz]; simpa using hy⟩

theorem gr_isGen_of_frame (L : GlobalTheory.CompanionTheory.Ar.Lat ξ E) {r : ℕ} (b b₀ : Fin r → E) (p : Cpt ξ)
    (h : ∀ i, GlobalTheory.CompanionTheory.Ar.flagStep Ω b i = GlobalTheory.CompanionTheory.Ar.flagStep Ω b₀ i) (hb : L.IsFrameAt b p) (i : Fin r) {t : Ω}
    (ht : t ≠ 0) (hy : b i - t • b₀ i ∈ GlobalTheory.CompanionTheory.Ar.flagStep Ω b₀ i) : (L.gr b₀ i).IsGenAt p t := by
  refine ⟨ht, le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_mono ?_)⟩
  · rintro s ⟨e, he, hs⟩
    rw [hb.2] at he
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 he
    have h2 : (∑ k, c k • b k) - (s / t) • b i ∈ GlobalTheory.CompanionTheory.Ar.flagStep Ω b i := by
      rw [h]
      have : (∑ k, c k • b k) - (s / t) • b i =
          ((∑ k, c k • b k) - s • b₀ i) - (s / t) • (b i - t • b₀ i) := by
        rw [smul_sub, smul_smul, div_mul_cancel₀ _ ht]; abel
      rw [this]; exact sub_mem hs (Submodule.smul_mem _ _ hy)
    obtain ⟨φ, hφ⟩ : ∃ φ : E →ₗ[Ω] Ω, ∀ k, φ (b k) = if k = i then 1 else 0 := by
      obtain ⟨g, hg⟩ := (Fintype.linearCombination Ω b).exists_leftInverse_of_injective
        (LinearMap.ker_eq_bot.2 (by rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']; intro m hm; funext k; exact Fintype.linearIndependent_iff.1 hb.1 m (by simpa [Fintype.linearCombination_apply] using hm) k))
      refine ⟨(LinearMap.proj i).comp g, fun k => ?_⟩
      have := LinearMap.congr_fun hg (Pi.single k 1)
      simp [Fintype.linearCombination_apply_single] at this
      simp [this, Pi.single_apply, eq_comm]
    have h3 : GlobalTheory.CompanionTheory.Ar.flagStep Ω b i ≤ LinearMap.ker φ := Submodule.span_le.2 (by
      rintro _ ⟨k, hk, rfl⟩
      have : k ≠ i := by rintro rfl; simp at hk
      simp [hφ, this])
    have h4 := h3 h2
    have h5 : ∀ k, φ (c k • b k) = (c k : Ω) * φ (b k) := fun k => φ.map_smul (c k : Ω) (b k)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [LinearMap.mem_ker, map_sub, map_sum, h5, map_smul, hφ] at h4
    simp at h4
    refine Submodule.mem_span_singleton.2 ⟨c i, ?_⟩
    show (c i : Ω) * t = s
    rw [sub_eq_zero.1 h4, div_mul_cancel₀ _ ht]
  · rintro _ rfl
    exact ⟨b i, by rw [hb.2]; exact Submodule.subset_span ⟨i, rfl⟩, hy⟩

theorem gen_ratio {Λ : GlobalTheory.CompanionTheory.Ar.Lat ξ Ω} {p : Cpt ξ} {s t : Ω} (hs : Λ.IsGenAt p s) (ht : Λ.IsGenAt p t) :
    ∃ u : Ω, u ∈ regAt ξ p ∧ u⁻¹ ∈ regAt ξ p ∧ s = u * t := by
  have a1 : s ∈ Submodule.span (regAt ξ p) {t} := by
    rw [← ht.2, hs.2]; exact Submodule.mem_span_singleton_self _
  have a2 : t ∈ Submodule.span (regAt ξ p) {s} := by
    rw [← hs.2, ht.2]; exact Submodule.mem_span_singleton_self _
  obtain ⟨u, hu⟩ := Submodule.mem_span_singleton.1 a1
  obtain ⟨v, hv⟩ := Submodule.mem_span_singleton.1 a2
  have hu' : (u : Ω) * t = s := hu
  have hv' : (v : Ω) * s = t := hv
  have e : (v : Ω) * (u : Ω) = 1 := by
    refine mul_right_cancel₀ ht.1 ?_
    rw [_root_.mul_assoc, hu', hv', _root_.one_mul]
  refine ⟨u, u.2, ?_, hu'.symm⟩
  rw [← eq_inv_of_mul_eq_one_left e]
  exact v.2

theorem gen_mul {Λ : GlobalTheory.CompanionTheory.Ar.Lat ξ Ω} {p : Cpt ξ} {t u : Ω} (h : Λ.IsGenAt p t) (h0 : u ≠ 0)
    (hu : u ∈ regAt ξ p) (hu' : u⁻¹ ∈ regAt ξ p) : Λ.IsGenAt p (u * t) := by
  refine ⟨mul_ne_zero h0 h.1, ?_⟩
  rw [h.2]
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
  · rintro _ rfl
    exact Submodule.mem_span_singleton.2 ⟨⟨u⁻¹, hu'⟩, inv_mul_cancel_left₀ h0 _⟩
  · rintro _ rfl
    exact Submodule.mem_span_singleton.2 ⟨⟨u, hu⟩, rfl⟩

end Frames

section Pull

variable {X X₀ : Scheme.{0}} {Ω Ω₀ : Type} [Field Ω] [Field Ω₀] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {ξ₀ : Spec (CommRingCat.of Ω₀) ⟶ X₀} {E E₀ : Type} [AddCommGroup E] [Module Ω E] [AddCommGroup E₀] [Module Ω₀ E₀]

theorem mem_flagStep_pull {i : Ω₀ →+* Ω} {j : E₀ →+ E} (hj : ∀ (a : Ω₀) e, j (a • e) = i a • j e) {r : ℕ}
    {y : Fin r → E₀} {n : ℕ} {x : E₀} (hx : x ∈ GlobalTheory.CompanionTheory.Ar.flagStep Ω₀ y n) :
    j x ∈ GlobalTheory.CompanionTheory.Ar.flagStep Ω (fun k => j (y k)) n := by
  unfold GlobalTheory.CompanionTheory.Ar.flagStep at hx
  induction hx using Submodule.span_induction with
  | mem x h =>
    obtain ⟨k, hk, rfl⟩ := h
    exact Submodule.subset_span ⟨k, hk, rfl⟩
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul a x _ hx => rw [hj]; exact Submodule.smul_mem _ _ hx

theorem flagStep_pull_le {i : Ω₀ →+* Ω} {j : E₀ →+ E} (hj : ∀ (a : Ω₀) e, j (a • e) = i a • j e) {r : ℕ}
    {x y : Fin r → E₀} {n : ℕ} (h : GlobalTheory.CompanionTheory.Ar.flagStep Ω₀ x n ≤ GlobalTheory.CompanionTheory.Ar.flagStep Ω₀ y n) :
    GlobalTheory.CompanionTheory.Ar.flagStep Ω (fun k => j (x k)) n ≤ GlobalTheory.CompanionTheory.Ar.flagStep Ω (fun k => j (y k)) n := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨k, hk, rfl⟩
  exact mem_flagStep_pull hj (h (Submodule.subset_span ⟨k, hk, rfl⟩))

theorem isFrameAt_pull {i : Ω₀ →+* Ω} {j : E₀ →+ E} {L₀ : GlobalTheory.CompanionTheory.Ar.Lat ξ₀ E₀} {L : GlobalTheory.CompanionTheory.Ar.Lat ξ E}
    {p₀ : Cpt ξ₀} {p : Cpt ξ} (hreg : ∀ a, a ∈ regAt ξ₀ p₀ → i a ∈ regAt ξ p)
    (hj : ∀ (a : Ω₀) e, j (a • e) = i a • j e)
    (hli : ∀ (n : ℕ) (b : Fin n → E₀), LinearIndependent Ω₀ b → LinearIndependent Ω fun k => j (b k))
    (hL : L p = Submodule.span (regAt ξ p) (j '' (L₀ p₀ : Set E₀))) {r : ℕ} {b : Fin r → E₀}
    (hb : L₀.IsFrameAt b p₀) : L.IsFrameAt (fun k => j (b k)) p := by
  refine ⟨hli _ _ hb.1, ?_⟩
  rw [hL]
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_mono ?_)
  · rintro _ ⟨e, he, rfl⟩
    have he' : e ∈ L₀ p₀ := he
    rw [hb.2] at he'
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 he'
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine sum_mem fun k _ => ?_
    have e1 : j (c k • b k) = (⟨i (c k), hreg _ (c k).2⟩ : regAt ξ p) • j (b k) := hj (c k : Ω₀) (b k)
    rw [e1]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  · rintro _ ⟨k, rfl⟩
    refine ⟨b k, ?_, rfl⟩
    show b k ∈ L₀ p₀
    rw [hb.2]
    exact Submodule.subset_span ⟨k, rfl⟩

theorem isGenAt_pull (i : Ω₀ →+* Ω) (j : E₀ →+ E) {L₀ : GlobalTheory.CompanionTheory.Ar.Lat ξ₀ E₀} {L : GlobalTheory.CompanionTheory.Ar.Lat ξ E}
    {p₀ : Cpt ξ₀} {p : Cpt ξ} (hreg : ∀ a, a ∈ regAt ξ₀ p₀ → i a ∈ regAt ξ p)
    (hj : ∀ (a : Ω₀) e, j (a • e) = i a • j e)
    (hli : ∀ (n : ℕ) (b : Fin n → E₀), LinearIndependent Ω₀ b → LinearIndependent Ω fun k => j (b k))
    {r : ℕ} {c₀ : Fin r → E₀} {c : Fin r → E} (hc : ∀ a, j (c₀ a) = c a)
    (hL : L p = Submodule.span (regAt ξ p) (j '' (L₀ p₀ : Set E₀)))
    (hf : L₀.IsFlagVBOn Set.univ c₀) (a : Fin r) {t₀ : Ω₀} (h : (L₀.gr c₀ a).IsGenAt p₀ t₀) :
    (L.gr c a).IsGenAt p (i t₀) := by
  obtain ⟨U, hU, b₁, hb, hfr⟩ := hf p₀ trivial
  have hfr' := hfr p₀ trivial hU
  obtain ⟨t₁, ht₁, hy⟩ := exists_coeff b₁ c₀ hb hfr'.1 a
  have g₁ := gr_isGen_of_frame L₀ b₁ c₀ p₀ hb hfr' a ht₁ hy
  obtain ⟨u, hu, hu', rfl⟩ := gen_ratio h g₁
  have hc' : c = fun k => j (c₀ k) := funext fun a => (hc a).symm
  subst hc'
  have hframe : L.IsFrameAt (fun k => j (b₁ k)) p := isFrameAt_pull hreg hj hli hL hfr'
  have hadapt : ∀ n, GlobalTheory.CompanionTheory.Ar.flagStep Ω (fun k => j (b₁ k)) n = GlobalTheory.CompanionTheory.Ar.flagStep Ω (fun k => j (c₀ k)) n :=
    fun n => le_antisymm (flagStep_pull_le hj (hb n).le) (flagStep_pull_le hj (hb n).ge)
  have hy' : j (b₁ a) - i t₁ • j (c₀ a) ∈ GlobalTheory.CompanionTheory.Ar.flagStep Ω (fun k => j (c₀ k)) a := by
    have := mem_flagStep_pull hj hy
    rwa [map_sub, hj] at this
  have g := gr_isGen_of_frame L (fun k => j (b₁ k)) (fun k => j (c₀ k)) p hadapt hframe a
    ((map_ne_zero i).2 ht₁) hy'
  have hu0 : u ≠ 0 := left_ne_zero_of_mul h.1
  rw [map_mul]
  refine gen_mul g ((map_ne_zero i).2 hu0) (hreg _ hu) ?_
  rw [← map_inv₀]
  exact hreg _ hu'

end Pull

theorem genPull_of_frames : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S₀ S : Finset ℕ) (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] (K₀ K : Type) [Fintype K₀] [Fintype K] (J₀ : K₀ → Type) (J : K → Type) [∀ k, Fintype (J₀ k)] [∀ k, Fintype (J k)] (y₀ : (Σ k, J₀ k) → Ω₀) (y : (Σ k, J k) → Ω) (𝔐₀ : HodgeCpt Y S₀ y₀) (𝔐 : HodgeCpt Y S y) (i : Ω₀ →+* Ω) (h : 𝔐.X ⟶ 𝔐₀.X) (hd : GlobalTheory.CompanionTheory.Ar.Dominates 𝔐.ξ 𝔐₀.ξ h i) (Fl₀ : 𝔐₀.Flag) (Fl : 𝔐.Flag) (j : 𝔐₀.Li →+ 𝔐.Li), (∀ (p : Cpt 𝔐.ξ) (a : Ω₀), a ∈ regAt 𝔐₀.ξ (pushCpt hd p) → i a ∈ regAt 𝔐.ξ p) → (∀ (a : Ω₀) e, j (a • e) = i a • j e) → (∀ (n : ℕ) (b : Fin n → 𝔐₀.Li), LinearIndependent Ω₀ b → LinearIndependent Ω fun k => j (b k)) → (∀ s a, j (Fl₀.b s a) = Fl.b s a) → (∀ q : Cpt 𝔐.ξ, (∀ r : ℕ, r.Prime → ¬ InFibre 𝔐.ξ r q) → ∀ s, 𝔐.V s q = Submodule.span (regAt 𝔐.ξ q) (j '' (𝔐₀.V s (pushCpt hd q) : Set 𝔐₀.Li))) → GenPull Fl₀ Fl i hd := by
  intro E _ _ _ H D l Xo c O _ β Y S₀ S Ω₀ Ω _ _ K₀ K _ _ J₀ J _ _ y₀ y 𝔐₀ 𝔐 i h hd Fl₀ Fl j hr hj hli hb hV
  intro q hq s a t₀ hg
  exact isGenAt_pull i j (hr q) hj hli (hb s) (hV q hq s) (Fl₀.sub s) a hg

end GlobalTheory.CompanionTheory.Ar.Chg.GP
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.KillsOverOfAdicCompletion
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.KillsAdic

theorem ext_of_quotients {A : Type} [CommRing A] {Y Z : Scheme.{0}} {f g : Sp A ⟶ Y} (s : Y ⟶ Z) [IsSeparated s]
    (h : f ≫ s = g ≫ s) {N : Type} (I : N → Ideal A) (hI : ∀ x : A, (∀ n, x ∈ I n) → x = 0)
    (hU : ∀ n, spMap (Ideal.Quotient.mk (I n)) ≫ f = spMap (Ideal.Quotient.mk (I n)) ≫ g) : f = g :=
  _root_.UpperTheory.Reformulated.B.MorphismExtOfSpecQuotients.main s h I hI hU

variable {S : Scheme.{0}} {X : Type} [AddCommGroup X]

theorem charVal_comp {A A' : Type} [CommRing A] [CommRing A'] {a : Sp A ⟶ S} {a' : Sp A' ⟶ S} (h : A →+* A')
    (e : spMap h ≫ a = a') (t : Over.mk a ⟶ splitTorus S X) (χ : X) :
    charVal ((Over.homMk (spMap h) e : Over.mk a' ⟶ Over.mk a) ≫ t) χ = h (charVal t χ) := by
  subst e
  exact (_root_.GlobalTheory.CompanionTheory.Ar.TorusPoints.main S X A a).2.2.2.2.2 A' h t _ (by simp) χ

theorem exists_factor {M : Type} [CommMonoid M] (Y : AddSubgroup X) (f : X → M) (h0 : f 0 = 1)
    (hadd : ∀ x y, f (x + y) = f x * f y) (hY : ∀ y ∈ Y, f y = 1) :
    ∃ v : Multiplicative (X ⧸ Y) →* M, ∀ χ : X, v (Multiplicative.ofAdd (χ : X ⧸ Y)) = f χ := by
  have key : ∀ x x' : X, (x : X ⧸ Y) = x' → f x = f x' := by
    intro x x' e
    have hm : -x + x' ∈ Y := QuotientAddGroup.eq.1 e
    have : x' = x + (-x + x') := by abel
    rw [this, hadd, hY _ hm, _root_.mul_one]
  refine ⟨{ toFun := fun q => f (Quotient.out (Multiplicative.toAdd q))
            map_one' := ?_
            map_mul' := ?_ }, fun χ => ?_⟩
  · rw [← h0]
    exact key _ _ (by simp)
  · intro p q
    rw [← hadd]
    exact key _ _ (by simp)
  · exact key _ _ (by simp)

theorem comp_one_over {T T' M : Over S} [GrpObj M] (f : T' ⟶ T) : f ≫ (1 : T ⟶ M) = 1 := by
  rw [Hom.one_def, Hom.one_def, ← Category.assoc, toUnit_unique (f ≫ toUnit T) (toUnit T')]

theorem universal_one {G : Over S} [GrpObj G] [IsSeparated G.hom] (u : splitTorus S X ⟶ G) (Y : AddSubgroup X)
    {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (b : Sp R ⟶ S)
    (hk : ∀ n : ℕ, KillsOver u Y (spMap (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n + 1))) ≫ b))
    (t₀ : Over.mk (spMap (algebraMap R (AddMonoidAlgebra R (X ⧸ Y))) ≫ b) ⟶ splitTorus S X)
    (ht₀ : ∀ χ : X, charVal t₀ χ = AddMonoidAlgebra.single (χ : X ⧸ Y) 1) : t₀ ≫ u = 1 := by
  let c := algebraMap R (AddMonoidAlgebra R (X ⧸ Y))
  let I : ℕ → Ideal (AddMonoidAlgebra R (X ⧸ Y)) := fun n =>
    Ideal.map c (IsLocalRing.maximalIdeal R ^ (n + 1))
  have hI : ∀ x, (∀ n, x ∈ I n) → x = 0 := fun x hx =>
    GlobalTheory.CompanionTheory.KrullGroupAlg.eq_zero_of_mem_map_pow R (X ⧸ Y) x fun n =>
      Ideal.map_mono (Ideal.pow_le_pow_right (Nat.le_succ n)) (hx n)
  refine Over.OverMorphism.ext (ext_of_quotients G.hom ?_ I hI fun n => ?_)
  · rw [Over.w, Over.w]
  · let J := IsLocalRing.maximalIdeal R ^ (n + 1)
    let gn : R ⧸ J →+* AddMonoidAlgebra R (X ⧸ Y) ⧸ I n :=
      Ideal.quotientMap (I n) c Ideal.le_comap_map
    have e : spMap (Ideal.Quotient.mk (I n)) ≫ spMap c ≫ b = spMap gn ≫ spMap (Ideal.Quotient.mk J) ≫ b := by
      rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
      rfl
    let m : Over.mk (spMap gn ≫ spMap (Ideal.Quotient.mk J) ≫ b) ⟶ Over.mk (spMap c ≫ b) :=
      Over.homMk (spMap (Ideal.Quotient.mk (I n))) e
    have hone := hk n _ gn (m ≫ t₀) (fun y hy => by
      rw [charVal_comp, ht₀, (QuotientAddGroup.eq_zero_iff y).2 hy]
      exact map_one _)
    have h4 : m ≫ (t₀ ≫ u) = m ≫ (1 : Over.mk (spMap c ≫ b) ⟶ G) := by
      exact (Category.assoc m t₀ u).symm.trans (hone.trans (comp_one_over m).symm)
    exact congrArg (fun w => w.left) h4

theorem killsOver_of_forall_pow : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsSeparated G.hom] (X : Type) [AddCommGroup X] (u : splitTorus S X ⟶ G) (Y : AddSubgroup X) (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (b : Sp R ⟶ S), (∀ n : ℕ, KillsOver u Y (spMap (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n + 1))) ≫ b)) → KillsOver u Y b := by
  intro S G _ _ X _ u Y R _ _ _ b hk A _ g t ht
  let c := algebraMap R (AddMonoidAlgebra R (X ⧸ Y))
  let w₀ : Multiplicative X →* AddMonoidAlgebra R (X ⧸ Y) :=
    (AddMonoidAlgebra.of R (X ⧸ Y)).comp (AddMonoidHom.toMultiplicative (QuotientAddGroup.mk' Y))
  obtain ⟨t₀, ht₀⟩ := (_root_.GlobalTheory.CompanionTheory.Ar.TorusPoints.main S X _ (spMap c ≫ b)).2.2.2.2.1 w₀
  have ht₀' : ∀ χ : X, charVal t₀ χ = AddMonoidAlgebra.single (χ : X ⧸ Y) 1 := fun χ => ht₀ χ
  have hone := universal_one u Y b hk t₀ ht₀'
  have hpts := (_root_.GlobalTheory.CompanionTheory.Ar.TorusPoints.main S X A (spMap g ≫ b))
  obtain ⟨v, hv⟩ := exists_factor Y (charVal t) (hpts.2.2.2.1 t).1 (hpts.2.2.2.1 t).2 ht
  let h : AddMonoidAlgebra R (X ⧸ Y) →+* A :=
    AddMonoidAlgebra.liftNCRingHom g v (fun _ _ => Commute.all _ _)
  have hc : h.comp c = g := by
    ext r
    simp [h, c]
  have e : spMap h ≫ spMap c ≫ b = spMap g ≫ b := by
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hc]
  let m : Over.mk (spMap g ≫ b) ⟶ Over.mk (spMap c ≫ b) := Over.homMk (spMap h) e
  have htm : t = m ≫ t₀ := hpts.1 _ _ fun χ => by
    rw [charVal_comp, ht₀']
    simp [h, AddMonoidAlgebra.liftNCRingHom_single, hv]
  rw [htm, Category.assoc, hone, comp_one_over]

end GlobalTheory.CompanionTheory.Ar.KillsAdic
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LogResolutionPotentialPullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.Chg
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Chg.Twist

section Holo

variable {e e' : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

theorem continuousAt_holo (A : FinHolAtlas e X) {W : Set X} {g : X → ℂ} (hg : A.HoloOn W g) {x : X}
    (hx : x ∈ W) : ContinuousAt g x := by
  obtain ⟨j, hj⟩ := A.cover x
  have h1 : ContinuousAt (g ∘ (A.chart j).symm) (A.chart j x) :=
    (hg j _ ⟨(A.chart j).map_source hj, by simpa [(A.chart j).left_inv hj] using hx⟩).continuousAt
  have h3 : ContinuousAt ((g ∘ (A.chart j).symm) ∘ A.chart j) x :=
    ContinuousAt.comp (g := g ∘ (A.chart j).symm) h1 ((A.chart j).continuousAt hj)
  refine h3.congr ?_
  filter_upwards [(A.chart j).open_source.mem_nhds hj] with y hy
  simp [Function.comp, (A.chart j).left_inv hy]

theorem holoOn_comp {A : FinHolAtlas e X} {B : FinHolAtlas e' Y} {h : Y → X} (hh : HoloMap B A h) {U : Set X}
    {g : X → ℂ} (hg : A.HoloOn U g) : B.HoloOn (h ⁻¹' U) (fun y => g (h y)) := by
  rintro j y ⟨hy, hyU⟩
  obtain ⟨k, hk⟩ := A.cover (h ((B.chart j).symm y))
  have a1 : AnalyticAt ℂ (A.chart k ∘ h ∘ (B.chart j).symm) y := hh.2 j k y ⟨hy, hk⟩
  have a2 : AnalyticAt ℂ (g ∘ (A.chart k).symm) ((A.chart k ∘ h ∘ (B.chart j).symm) y) :=
    hg k _ ⟨(A.chart k).map_source hk, by
      simpa [Function.comp, (A.chart k).left_inv hk] using hyU⟩
  refine (a2.comp a1).congr ?_
  filter_upwards [((B.chart j).isOpen_inter_preimage_symm
    ((A.chart k).open_source.preimage hh.1)).mem_nhds ⟨hy, hk⟩] with y' hy'
  simp [Function.comp, (A.chart k).left_inv hy'.2]

theorem exists_log (A : FinHolAtlas e X) {W : Set X} (hW : IsOpen W) {c : X → ℂ} (hc : A.HoloOn W c) {x : X}
    (hx : x ∈ W) (h0 : c x ≠ 0) :
    ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ V ⊆ W ∧ ∃ L : X → ℂ, A.HoloOn V L ∧
      ∀ y ∈ V, c y ≠ 0 ∧ (L y).re = Real.log ‖c y‖ := by
  have hcont : ContinuousOn (fun y => c y / c x) W := fun y hy =>
    ((continuousAt_holo A hc hy).div_const _).continuousWithinAt
  have hV : IsOpen (W ∩ (fun y => c y / c x) ⁻¹' Complex.slitPlane) :=
    hcont.isOpen_inter_preimage hW Complex.isOpen_slitPlane
  refine ⟨_, hV, ⟨hx, ?_⟩, Set.inter_subset_left, fun y => Complex.log (c y / c x) + (Real.log ‖c x‖ : ℂ), ?_, ?_⟩
  · simp [div_self h0]
  · rintro j z ⟨hz, hzW, hzs⟩
    have a1 : AnalyticAt ℂ (c ∘ (A.chart j).symm) z := hc j z ⟨hz, hzW⟩
    have a2 : AnalyticAt ℂ (fun z => (c ∘ (A.chart j).symm) z / c x) z := a1.div analyticAt_const h0
    exact (a2.clog hzs).add analyticAt_const
  · rintro y ⟨-, hy⟩
    have hy' : c y / c x ≠ 0 := Complex.slitPlane_ne_zero hy
    have hcy : c y ≠ 0 := fun e => hy' (by simp [e])
    refine ⟨hcy, ?_⟩
    simp only [Complex.add_re, Complex.log_re, Complex.ofReal_re, norm_div]
    rw [Real.log_div (norm_ne_zero_iff.2 hcy) (norm_ne_zero_iff.2 h0)]
    ring

end Holo

variable {K₀ K : Type} [Fintype K₀] [Fintype K] {J₀ : K₀ → Type} {J : K → Type}
  [∀ k, Fintype (J₀ k)] [∀ k, Fintype (J k)] {κ : K₀ → K} {v : (Σ k, J₀ k) → Σ k, J k}
  {P₀ Jd₀ : Ideal (MRing J₀)} {P Jd : Ideal (MRing J)} {D : ℕ}

theorem orbit_key (R₀ : AnLogRes P₀ Jd₀ D) (R : AnLogRes P Jd D) (hv : IsBlockMap κ v) (h : R.X → R₀.X)
    (ho : ∀ x, SameOrbit (R₀.lift (h x) (h x)) (fun p => R.lift x x (v p))) {x y : R.X} (hy : y ∈ R.U x)
    (hy₀ : h y ∈ R₀.U (h x)) :
    ∃ c : K₀ → ℂ, (∀ k, c k ≠ 0) ∧ ∀ p, R.lift x y (v p) = c p.1 * R₀.lift (h x) (h y) p := by
  obtain ⟨c₁, h₁, e₁⟩ := R.compat x y y ⟨hy, R.mem_U y⟩
  obtain ⟨c₂, h₂, e₂⟩ := ho y
  obtain ⟨c₃, h₃, e₃⟩ := R₀.compat (h x) (h y) (h y) ⟨hy₀, R₀.mem_U _⟩
  refine ⟨fun k => c₁ (κ k) / (c₃ k * c₂ k), fun k => div_ne_zero (h₁ _) (mul_ne_zero (h₃ k) (h₂ k)), fun p => ?_⟩
  have a₁ := congrFun e₁ (v p)
  have a₂ := congrFun e₂ p
  have a₃ := congrFun e₃ p
  simp only at a₁ a₂ a₃
  have n₂ := h₂ p.1
  have n₃ := h₃ p.1
  rw [a₃, a₂, a₁, hv.2.2.1 p]
  field_simp

theorem exists_coeff_log (R₀ : AnLogRes P₀ Jd₀ D) (R : AnLogRes P Jd D) (hv : IsBlockMap κ v) (h : R.X → R₀.X)
    (hh : HoloMap R.A R₀.A h)
    (ho : ∀ x, SameOrbit (R₀.lift (h x) (h x)) (fun p => R.lift x x (v p))) (x : R.X) (k : K₀) :
    ∃ V : Set R.X, IsOpen V ∧ x ∈ V ∧ V ⊆ R.U x ∩ h ⁻¹' R₀.U (h x) ∧ ∃ L : R.X → ℂ, R.A.HoloOn V L ∧
      ∀ y ∈ V, ∀ c : K₀ → ℂ, (∀ k, c k ≠ 0) →
        (∀ p, R.lift x y (v p) = c p.1 * R₀.lift (h x) (h y) p) → (L y).re = Real.log ‖c k‖ := by
  have oW : IsOpen (R.U x ∩ h ⁻¹' R₀.U (h x)) := (R.isOpen_U x).inter ((R₀.isOpen_U _).preimage hh.1)
  have mW : x ∈ R.U x ∩ h ⁻¹' R₀.U (h x) := ⟨R.mem_U x, R₀.mem_U _⟩
  obtain ⟨i, hi⟩ := (R₀.mem (h x) (h x) (R₀.mem_U _)).1 k
  obtain ⟨cx, hcx, ecx⟩ := orbit_key R₀ R hv h ho (R.mem_U x) (R₀.mem_U (h x))
  have hn : R.A.HoloOn (R.U x ∩ h ⁻¹' R₀.U (h x)) (fun y => R.lift x y (v ⟨k, i⟩)) := fun j z hz =>
    R.holo x (v ⟨k, i⟩) j z ⟨hz.1, hz.2.1⟩
  have hd : R.A.HoloOn (R.U x ∩ h ⁻¹' R₀.U (h x)) (fun y => R₀.lift (h x) (h y) ⟨k, i⟩) := fun j z hz =>
    holoOn_comp hh (R₀.holo (h x) ⟨k, i⟩) j z ⟨hz.1, hz.2.2⟩
  have hnx : R.lift x x (v ⟨k, i⟩) ≠ 0 := by
    rw [ecx ⟨k, i⟩]
    exact mul_ne_zero (hcx k) hi
  obtain ⟨Vn, oVn, mVn, sVn, Ln, hLn, eLn⟩ := exists_log R.A oW hn mW hnx
  obtain ⟨Vd, oVd, mVd, -, Ld, hLd, eLd⟩ := exists_log R.A oW hd mW hi
  refine ⟨Vn ∩ Vd, oVn.inter oVd, ⟨mVn, mVd⟩, Set.inter_subset_left.trans sVn, fun y => Ln y - Ld y, ?_, ?_⟩
  · rintro j z ⟨hz, hzn, hzd⟩
    exact (hLn j z ⟨hz, hzn⟩).sub (hLd j z ⟨hz, hzd⟩)
  · rintro y ⟨hyn, hyd⟩ c hc ec
    obtain ⟨-, e1⟩ := eLn y hyn
    obtain ⟨d0, e2⟩ := eLd y hyd
    simp only [Complex.sub_re, e1, e2]
    rw [ec ⟨k, i⟩, norm_mul, Real.log_mul (norm_ne_zero_iff.2 (hc k)) (norm_ne_zero_iff.2 d0)]
    ring

theorem samePot_twist : ∀ (K₀ K : Type) [Fintype K₀] [Fintype K] (J₀ : K₀ → Type) (J : K → Type) [∀ k, Fintype (J₀ k)] [∀ k, Fintype (J k)] (κ : K₀ → K) (v : (Σ k, J₀ k) → Σ k, J k) (P₀ Jd₀ : Ideal (MRing J₀)) (P Jd : Ideal (MRing J)) (D : ℕ) (R₀ : AnLogRes P₀ Jd₀ D) (R : AnLogRes P Jd D) (X : Type) [TopologicalSpace X] (B : FinHolAtlas D X) (Θ : LocPot X) (A₀ : HermLine J₀) (T : HermLine J) (π : R₀.X → X) (hπ : HoloMap R₀.A B π) (h : R.X → R₀.X) (hv : IsBlockMap κ v) (hc : Continuous (π ∘ h)), HoloMap R.A R₀.A h → (∀ x, SameOrbit (R₀.lift (h x) (h x)) (fun p => R.lift x x (v p))) → SamePot R₀.A Set.univ (potOf R₀ A₀) (Θ.pullback π hπ.1) → IsFlatOn R T → SamePot R.A Set.univ (potOf R ((pullHerm hv A₀).tensor T)) (Θ.pullback (π ∘ h) hc) := by
  intro K₀ K _ _ J₀ J _ _ κ v P₀ Jd₀ P Jd D R₀ R X _ B Θ A₀ T π hπ h hv hc hh ho h0 hF x _
  obtain ⟨V₀, oV₀, mV₀, G₀, hG₀, e₀⟩ := h0 (h x) trivial
  obtain ⟨V₁, oV₁, mV₁, G₁, hG₁, e₁⟩ := hF x trivial
  choose Vk oVk mVk sVk L hL eL using exists_coeff_log R₀ R hv h hh ho x
  refine ⟨(⋂ k, Vk k) ∩ ((h ⁻¹' V₀ ∩ V₁) ∩ (R.U x ∩ h ⁻¹' R₀.U (h x))),
    (isOpen_iInter_of_finite oVk).inter (((oV₀.preimage hh.1).inter oV₁).inter
      ((R.isOpen_U x).inter ((R₀.isOpen_U _).preimage hh.1))),
    ⟨Set.mem_iInter.2 mVk, ⟨mV₀, mV₁⟩, R.mem_U x, R₀.mem_U _⟩,
    fun y => G₀ (h y) + G₁ y + ∑ k, ((A₀.a k : ℝ) : ℂ) * L k y, ?_, ?_⟩
  · rintro j z ⟨hz, hzk, ⟨hz₀, hz₁⟩, -⟩
    have t0 : AnalyticAt ℂ (fun z => G₀ (h ((R.A.chart j).symm z))) z := holoOn_comp hh hG₀ j z ⟨hz, hz₀⟩
    have t1 : AnalyticAt ℂ (fun z => G₁ ((R.A.chart j).symm z)) z := hG₁ j z ⟨hz, hz₁⟩
    have t2 : ∀ k ∈ (Finset.univ : Finset K₀),
        AnalyticAt ℂ (fun z => ((A₀.a k : ℝ) : ℂ) * L k ((R.A.chart j).symm z)) z := fun k _ =>
      analyticAt_const.mul (hL k j z ⟨hz, Set.mem_iInter.1 hzk k⟩)
    exact (t0.add t1).add (Finset.analyticAt_fun_sum _ t2)
  · rintro y ⟨hyk, ⟨hy₀, hy₁⟩, hyU, hyU₀⟩
    obtain ⟨c, hc0, ec⟩ := orbit_key R₀ R hv h ho hyU hyU₀
    have E0 : Real.log (A₀.h (R₀.lift (h x) (h y))) - Θ.φ (π (h x)) (π (h y)) = (G₀ (h y)).re := e₀ (h y) hy₀
    have E1 : Real.log (T.h (R.lift x y)) - 0 = (G₁ y).re := e₁ y hy₁
    have E2 : (fun p => R.lift x y (v p)) = fun p => c p.1 * R₀.lift (h x) (h y) p := funext ec
    show Real.log (((pullHerm hv A₀).tensor T).h (R.lift x y)) - Θ.φ (π (h x)) (π (h y)) = _
    rw [log_tensor_pull hv A₀ T (R.mem x y hyU).1, E2, log_h_smul A₀ hc0 (R₀.mem _ _ hyU₀).1]
    simp only [Complex.add_re, Complex.re_sum, Complex.re_ofReal_mul, ← E0, ← E1,
      fun k => eL k y (Set.mem_iInter.1 hyk k) c hc0 ec]
    ring

end GlobalTheory.CompanionTheory.Ar.Chg.Twist
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorusExtensionModuleStructureStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torus_extension_module_structure : ∀ (K : Type) [Field K] (G : Over (Sp K)) [GrpObj G] (τ : TorusExtension G) (O : Type) [CommRing O] (act : OAct O G), letI := τ.addCommGroup; letI := τ.grpB; (∀ a, ∃ b : τ.B ⟶ τ.B, IsMonHom b ∧ act.act a ≫ τ.q = τ.q ≫ b) → ∃ m : Module O τ.X, letI := m; ∀ a, (GlobalTheory.Diag.diagAct (Sp K) O τ.X).act a ≫ τ.i = τ.i ≫ act.act a := by
  first | exact @GlobalTheory.CompanionTheory.TorusAct.exists_module_diagAct | exact GlobalTheory.CompanionTheory.TorusAct.exists_module_diagAct | (intros; apply GlobalTheory.CompanionTheory.TorusAct.exists_module_diagAct <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorusExtensionRankBoundStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torus_extension_rank_bound : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (u : splitTorus S X ⟶ G) [IsMonHom u] (k : Type) [Field k] (x : Sp k ⟶ S), (∀ (A : Type) [CommRing A] (g : k →+* A) (t : Over.mk (spMap g ≫ x) ⟶ splitTorus S X), t ≫ u = 1 → t = 1) → ∀ (Gk : Over (Sp k)) [GrpObj Gk] (ψ : Gk.left ⟶ G.left), IsGrpPullback Gk G x ψ → ∀ τ : TorusExtension Gk, (letI := τ.addCommGroup; Module.finrank ℤ τ.X ≤ Module.finrank ℤ X) → letI := τ.grpB; ∀ (A : Type) [CommRing A] (g : k →+* A) (p : Over.mk (spMap g) ⟶ Gk), p ≫ τ.q = 1 ↔ ∃ t : Over.mk (spMap g ≫ x) ⟶ splitTorus S X, (t ≫ u).left = p.left ≫ ψ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.MaxTorus.kernel_eq_of_rank_le | exact GlobalTheory.CompanionTheory.Ar.MaxTorus.kernel_eq_of_rank_le | (intros; apply GlobalTheory.CompanionTheory.Ar.MaxTorus.kernel_eq_of_rank_le <;> assumption)
end

