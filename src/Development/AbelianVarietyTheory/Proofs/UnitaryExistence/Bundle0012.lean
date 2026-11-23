module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0004

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FormallyUnramifiedMulN
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.MulUnramified

def affineComb {A R : Type} [CommRing A] [CommRing R] (a b c : A →+* R)
    (h : ∀ s t, (a s - c s) * (b t - c t) = 0) : A →+* R where
  toFun s := a s + b s - c s
  map_one' := by simp
  map_zero' := by simp
  map_add' s t := by simp only [map_add (f := _)]; ring
  map_mul' s t := by
    simp only [map_mul]
    linear_combination - h s t - h t s

lemma appLE_congr {T X : Scheme.{0}} {f g : T ⟶ X} (h : f = g) (V : X.Opens) (W : T.Opens)
    (hf : W ≤ f ⁻¹ᵁ V) (hg : W ≤ g ⁻¹ᵁ V) : f.appLE V W hf = g.appLE V W hg := by
  subst h; rfl

lemma preimage_eq {T₀ T X : Scheme.{0}} (i : T₀ ⟶ T) (hi : Function.Surjective i) {f g : T ⟶ X}
    (h : i ≫ f = i ≫ g) (V : X.Opens) : f ⁻¹ᵁ V = g ⁻¹ᵁ V := by
  ext x
  obtain ⟨x, rfl⟩ := hi x
  have : f (i x) = g (i x) := congr($h x)
  simp [this]

lemma app_sub_eq_zero {T₀ T X : Scheme.{0}} (i : T₀ ⟶ T) {f g : T ⟶ X}
    (h : i ≫ f = i ≫ g) (V : X.Opens) (W : T.Opens)
    (hf : W ≤ f ⁻¹ᵁ V) (hg : W ≤ g ⁻¹ᵁ V) (s : Γ(X, V)) :
    i.app W (f.appLE V W hf s - g.appLE V W hg s) = 0 := by
  rw [map_sub, sub_eq_zero, ← CategoryTheory.comp_apply, ← CategoryTheory.comp_apply,
    Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE,
    appLE_congr h]

lemma comp_appLE_apply {T P X : Scheme.{0}} (a : T ⟶ P) (p : P ⟶ X) {x : T ⟶ X} (h : a ≫ p = x)
    (V : X.Opens) (V' : P.Opens) (W : T.Opens) (h₁ : V' ≤ p ⁻¹ᵁ V) (h₂ : W ≤ a ⁻¹ᵁ V')
    (h₃ : W ≤ x ⁻¹ᵁ V) (s : Γ(X, V)) :
    a.appLE V' W h₂ (p.appLE V V' h₁ s) = x.appLE V W h₃ s := by
  rw [← CategoryTheory.comp_apply, Scheme.Hom.appLE_comp_appLE, appLE_congr h]

lemma le_preimage_of_comp {T P X : Scheme.{0}} (a : T ⟶ P) (p : P ⟶ X)
    {V : X.Opens} {V' : P.Opens} {W : T.Opens} (h₁ : V' ≤ p ⁻¹ᵁ V) (h₂ : W ≤ a ⁻¹ᵁ V') :
    W ≤ (a ≫ p) ⁻¹ᵁ V := fun _ hx ↦ h₁ (h₂ hx)

lemma parallelogram {T P X : Scheme.{0}} (p q : P ⟶ X)
    (hpq : ∀ (Z : Scheme.{0}) (u v : Z ⟶ P), u ≫ p = v ≫ p → u ≫ q = v ≫ q → u = v)
    (a b c d : T ⟶ P) (hap : a ≫ p = d ≫ p) (hbp : b ≫ p = c ≫ p)
    (haq : a ≫ q = c ≫ q) (hbq : b ≫ q = d ≫ q)
    {V : X.Opens} (hV : IsAffineOpen V) {V' : P.Opens} (hV' : IsAffineOpen V')
    {W : T.Opens} (hW : IsAffineOpen W) (hp : V' ≤ p ⁻¹ᵁ V) (hq : V' ≤ q ⁻¹ᵁ V)
    (ha : W ≤ a ⁻¹ᵁ V') (hb : W ≤ b ⁻¹ᵁ V') (hc : W ≤ c ⁻¹ᵁ V') (hd : W ≤ d ⁻¹ᵁ V')
    (h : ∀ s t, (a.appLE V' W ha s - c.appLE V' W hc s) *
      (b.appLE V' W hb t - c.appLE V' W hc t) = 0) (s : Γ(P, V')) :
    d.appLE V' W hd s = a.appLE V' W ha s + b.appLE V' W hb s - c.appLE V' W hc s := by
  let φ : Γ(P, V') ⟶ Γ(T, W) :=
    CommRingCat.ofHom (affineComb (a.appLE V' W ha).hom (b.appLE V' W hb).hom (c.appLE V' W hc).hom h)
  have hφ : ∀ s, φ s = a.appLE V' W ha s + b.appLE V' W hb s - c.appLE V' W hc s := fun _ ↦ rfl
  have key : Spec.map (d.appLE V' W hd) ≫ hV'.fromSpec = Spec.map φ ≫ hV'.fromSpec := by
    apply hpq
    · rw [Category.assoc, Category.assoc, ← hV.SpecMap_appLE_fromSpec p hV' hp,
        ← Spec.map_comp_assoc, ← Spec.map_comp_assoc]
      congr 2
      ext s
      simp only [CommRingCat.hom_comp, RingHom.comp_apply]
      rw [hφ, comp_appLE_apply a p hap _ _ _ _ _ (le_preimage_of_comp d p hp hd),
        comp_appLE_apply d p rfl _ _ _ _ _ (le_preimage_of_comp d p hp hd),
        comp_appLE_apply b p hbp _ _ _ _ _ (le_preimage_of_comp c p hp hc),
        comp_appLE_apply c p rfl _ _ _ _ _ (le_preimage_of_comp c p hp hc)]
      ring
    · rw [Category.assoc, Category.assoc, ← hV.SpecMap_appLE_fromSpec q hV' hq,
        ← Spec.map_comp_assoc, ← Spec.map_comp_assoc]
      congr 2
      ext s
      simp only [CommRingCat.hom_comp, RingHom.comp_apply]
      rw [hφ, comp_appLE_apply a q haq _ _ _ _ _ (le_preimage_of_comp c q hq hc),
        comp_appLE_apply d q rfl _ _ _ _ _ (le_preimage_of_comp d q hq hd),
        comp_appLE_apply b q hbq _ _ _ _ _ (le_preimage_of_comp d q hq hd),
        comp_appLE_apply c q rfl _ _ _ _ _ (le_preimage_of_comp c q hq hc)]
      ring
  rw [cancel_mono, Spec.map_inj] at key
  rw [key, hφ]

variable {S : Scheme.{0}}

lemma comp_mulN (G : Over S) [GrpObj G] {T : Over S} (x : T ⟶ G) (n : ℕ) :
    x ≫ mulN G n = x ^ n := by
  induction n with
  | zero => simp [mulN, Hom.one_def]
  | succ n ih => rw [mulN, pow_succ, Hom.mul_def, ← ih, comp_lift_assoc, Category.comp_id]

lemma eq_one_of_pow_eq_one (G : Over S) [GrpObj G] {T₀ T : Over S} (j : T₀ ⟶ T)
    (hj : Function.Surjective j.left)
    (hsq : ∀ (W : T.left.Opens), IsAffineOpen W → ∀ s t : Γ(T.left, W),
      j.left.app W s = 0 → j.left.app W t = 0 → s * t = 0)
    (n : ℕ) (hn : IsUnit (n : Γ(S, ⊤))) (z : T ⟶ G) (hz : j ≫ z = 1) (hzn : z ^ n = 1) :
    z = 1 := by
  apply Over.OverMorphism.ext
  refine Scheme.hom_ext_of_forall _ _ fun t ↦ ?_
  let e : T ⟶ G := 1
  have he : j ≫ e = 1 := by simp [e]
  obtain ⟨_, ⟨V, hV, rfl⟩, htV, -⟩ :=
    G.left.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (e.left t)) isOpen_univ
  have hcp : (lift e e).left ≫ (fst G G).left = e.left := by rw [← Over.comp_left, lift_fst]
  have hcq : (lift e e).left ≫ (snd G G).left = e.left := by rw [← Over.comp_left, lift_snd]
  have hcm : (lift e e).left ≫ (μ[G]).left = e.left := by
    rw [← Over.comp_left, ← Hom.mul_def, _root_.mul_one]
  obtain ⟨_, ⟨V', hV', rfl⟩, htV', hV'V : V' ≤ _⟩ :=
    (G ⊗ G).left.isBasis_affineOpens.exists_subset_of_mem_open (a := (lift e e).left t)
      (u := ((fst G G).left ⁻¹ᵁ V ⊓ (snd G G).left ⁻¹ᵁ V ⊓ (μ[G]).left ⁻¹ᵁ V : (G ⊗ G).left.Opens))
      ⟨⟨show ((lift e e).left ≫ (fst G G).left) t ∈ V by rwa [hcp],
        show ((lift e e).left ≫ (snd G G).left) t ∈ V by rwa [hcq]⟩,
        show ((lift e e).left ≫ (μ[G]).left) t ∈ V by rwa [hcm]⟩ (TopologicalSpace.Opens.isOpen _)
  have hp : V' ≤ (fst G G).left ⁻¹ᵁ V := hV'V.trans (inf_le_left.trans inf_le_left)
  have hq : V' ≤ (snd G G).left ⁻¹ᵁ V := hV'V.trans (inf_le_left.trans inf_le_right)
  have hm : V' ≤ (μ[G]).left ⁻¹ᵁ V := hV'V.trans inf_le_right
  obtain ⟨_, ⟨W, hW, rfl⟩, htW, hc : W ≤ (lift e e).left ⁻¹ᵁ V'⟩ :=
    T.left.isBasis_affineOpens.exists_subset_of_mem_open (a := t)
      (u := (lift e e).left ⁻¹ᵁ V') htV' (TopologicalSpace.Opens.isOpen _)
  refine ⟨W, htW, ?_⟩
  have heW : W ≤ e.left ⁻¹ᵁ V := hcp ▸ le_preimage_of_comp _ _ hp hc
  have near : ∀ x : T ⟶ G, j ≫ x = 1 → j.left ≫ x.left = j.left ≫ e.left := fun x hx ↦ by
    rw [← Over.comp_left, ← Over.comp_left, hx, he]
  have near₂ : ∀ x y : T ⟶ G, j ≫ x = 1 → j ≫ y = 1 →
      j.left ≫ (lift x y).left = j.left ≫ (lift e e).left := fun x y hx hy ↦ by
    rw [← Over.comp_left, ← Over.comp_left, comp_lift, comp_lift, hx, hy, he]
  have hW₁ : ∀ x : T ⟶ G, j ≫ x = 1 → W ≤ x.left ⁻¹ᵁ V := fun x hx ↦ by
    rw [preimage_eq j.left hj (near x hx)]; exact heW
  have hW₂ : ∀ x y : T ⟶ G, j ≫ x = 1 → j ≫ y = 1 → W ≤ (lift x y).left ⁻¹ᵁ V' :=
    fun x y hx hy ↦ by rw [preimage_eq j.left hj (near₂ x y hx hy)]; exact hc
  have add : ∀ (x y : T ⟶ G) (hx : j ≫ x = 1) (hy : j ≫ y = 1) (hxy : j ≫ (x * y) = 1)
      (s : Γ(G.left, V)), (x * y).left.appLE V W (hW₁ _ hxy) s =
        x.left.appLE V W (hW₁ _ hx) s + y.left.appLE V W (hW₁ _ hy) s - e.left.appLE V W heW s := by
    intro x y hx hy hxy s
    have := parallelogram (fst G G).left (snd G G).left
      (fun Z u v h₁ h₂ ↦ pullback.hom_ext h₁ h₂)
      (lift x e).left (lift e y).left (lift e e).left (lift x y).left
      (by simp only [← Over.comp_left, lift_fst]) (by simp only [← Over.comp_left, lift_fst])
      (by simp only [← Over.comp_left, lift_snd]) (by simp only [← Over.comp_left, lift_snd])
      hV hV' hW hp hq (hW₂ _ _ hx he) (hW₂ _ _ he hy) hc (hW₂ _ _ hx hy)
      (fun s t ↦ hsq W hW _ _ (app_sub_eq_zero _ (near₂ _ _ hx he) _ _ _ _ _)
        (app_sub_eq_zero _ (near₂ _ _ he hy) _ _ _ _ _)) ((μ[G]).left.appLE V V' hm s)
    rwa [comp_appLE_apply _ _ (x := (x * y).left) (by rw [← Over.comp_left, ← Hom.mul_def])
        _ _ _ _ _ (hW₁ _ hxy),
      comp_appLE_apply _ _ (x := x.left) (by rw [← Over.comp_left, ← Hom.mul_def, _root_.mul_one])
        _ _ _ _ _ (hW₁ _ hx),
      comp_appLE_apply _ _ (x := y.left) (by rw [← Over.comp_left, ← Hom.mul_def, _root_.one_mul])
        _ _ _ _ _ (hW₁ _ hy),
      comp_appLE_apply _ _ hcm _ _ _ _ _ heW] at this
  have hpow : ∀ k : ℕ, j ≫ (z ^ k) = 1 := fun k ↦ by rw [comp_pow, hz, one_pow]
  have ind : ∀ (k : ℕ) (s : Γ(G.left, V)), (z ^ k).left.appLE V W (hW₁ _ (hpow k)) s -
      e.left.appLE V W heW s = k * (z.left.appLE V W (hW₁ _ hz) s - e.left.appLE V W heW s) := by
    intro k s
    induction k with
    | zero =>
      rw [appLE_congr (g := e.left) (by rw [pow_zero]) _ _ _ heW]
      simp
    | succ k ih =>
      rw [appLE_congr (g := (z ^ k * z).left) (by rw [pow_succ]) _ _ _
        (hW₁ _ (by rw [← pow_succ]; exact hpow _)), add _ _ (hpow k) hz (by rw [← pow_succ]; exact hpow _)]
      push_cast
      linear_combination ih
  have hn' : IsUnit (n : Γ(T.left, W)) := by
    simpa using hn.map (T.hom.appLE ⊤ W le_top).hom
  have fin : z.left.appLE V W (hW₁ _ hz) = e.left.appLE V W heW := by
    ext s
    have := ind n s
    rw [appLE_congr (g := e.left) (by rw [hzn]) _ _ _ heW, sub_self] at this
    exact sub_eq_zero.mp (hn'.mul_right_eq_zero.mp this.symm)
  rw [← hW.isoSpec_hom_fromSpec, Category.assoc, Category.assoc,
    ← hV.SpecMap_appLE_fromSpec z.left hW (hW₁ _ hz), fin, hV.SpecMap_appLE_fromSpec e.left hW heW]

lemma mul_eq_zero_of_ker_sq {R R₀ : CommRingCat.{0}} (φ : R ⟶ R₀) (hφ : RingHom.ker φ.hom ^ 2 = ⊥)
    (W : (Spec R).Opens) (hW : IsAffineOpen W) (s t : Γ(Spec R, W))
    (hs : (Spec.map φ).app W s = 0) (ht : (Spec.map φ).app W t = 0) : s * t = 0 := by
  have h : (Spec.map φ).ker ^ 2 = ⊥ := by
    apply Scheme.IdealSheafData.ext_of_isAffine
    suffices RingHom.ker (Spec.map φ).appTop.hom ^ 2 = ⊥ by
      simp only [Scheme.IdealSheafData.ideal_pow, Pi.pow_apply, Scheme.Hom.ker_apply,
        Scheme.IdealSheafData.ideal_bot, Pi.bot_apply]
      exact this
    have key : ∀ s ∈ RingHom.ker (Spec.map φ).appTop.hom,
        (Scheme.ΓSpecIso R).hom s ∈ RingHom.ker φ.hom := fun s hs ↦ by
      rw [RingHom.mem_ker] at hs ⊢
      rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_naturality, CommRingCat.comp_apply, hs,
        map_zero]
    rw [pow_two, eq_bot_iff, Ideal.mul_le]
    intro s hs t ht
    rw [Ideal.mem_bot]
    apply (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv.injective
    rw [map_mul, map_zero, ← Ideal.mem_bot, ← hφ, pow_two]
    exact Ideal.mul_mem_mul (key s hs) (key t ht)
  have h' : RingHom.ker ((Spec.map φ).app W).hom ^ 2 = ⊥ := by
    simpa using congr(($h).ideal ⟨W, hW⟩)
  rw [← Ideal.mem_bot, ← h', pow_two]
  exact Ideal.mul_mem_mul hs ht

end GlobalTheory.MulUnramified

namespace GlobalTheory


open MulUnramified in
theorem formallyUnramified_mulN (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (n : ℕ)
    (hn : IsUnit (n : Γ(S, ⊤))) : FormallyUnramified (mulN G n).left := by
  refine FormallyUnramified.of_hom_ext _ fun R R₀ φ hφ hsq g₁ g₂ hi hg ↦ ?_
  have hS : g₂ ≫ G.hom = g₁ ≫ G.hom := by
    rw [← Over.w (mulN G n), reassoc_of% hg]
  let T : Over S := Over.mk (g₁ ≫ G.hom)
  let T₀ : Over S := Over.mk (Spec.map φ ≫ g₁ ≫ G.hom)
  let j : T₀ ⟶ T := Over.homMk (Spec.map φ) rfl
  let x : T ⟶ G := Over.homMk g₁ rfl
  let y : T ⟶ G := Over.homMk g₂ hS
  have hj : j ≫ x = j ≫ y := Over.OverMorphism.ext hi
  have hxy : x ^ n = y ^ n := by
    rw [← comp_mulN, ← comp_mulN]
    exact Over.OverMorphism.ext hg
  have hsurj : Function.Surjective (Spec.map φ) := by
    intro (p : PrimeSpectrum R)
    change p ∈ Set.range (PrimeSpectrum.comap φ.hom)
    rw [range_comap_of_surjective _ _ hφ, PrimeSpectrum.mem_zeroLocus]
    intro a ha
    refine p.isPrime.mem_of_pow_mem 2 ?_
    have : a ^ 2 ∈ RingHom.ker φ.hom ^ 2 := Ideal.pow_mem_pow ha 2
    rw [hsq, Ideal.mem_bot] at this
    rw [this]
    exact zero_mem _
  have := eq_one_of_pow_eq_one G j hsurj (mul_eq_zero_of_ker_sq φ hsq) n hn (x / y)
    (by rw [GrpObj.comp_div, hj, div_self']) (by rw [div_pow, hxy, div_self'])
  exact congrArg (·.left) (div_eq_one.mp this)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsIntegralAndIsNormalSchemeOfSmoothDvr
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem isDominant_spMap_of_isFractionRing (T K : Type) [CommRing T] [IsDomain T] [Field K]
    [Algebra T K] [IsFractionRing T K] : IsDominant (spMap (algebraMap T K)) := by
  refine ⟨?_⟩
  change DenseRange (PrimeSpectrum.comap (algebraMap T K))
  rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
    (RingHom.injective_iff_ker_eq_bot _).mp (IsFractionRing.injective T K)]
  exact bot_le

theorem isDominant_genericFibre_of_flat (T K : Type) [CommRing T] [IsDomain T] [Field K]
    [Algebra T K] [IsFractionRing T K] {X : Scheme.{0}} (f : X ⟶ Sp T) [Flat f] :
    IsDominant (pullback.fst f (spMap (algebraMap T K))) := by
  have := isDominant_spMap_of_isFractionRing T K
  have := IsSchemeTheoreticallyDominant.of_isDominant (spMap (algebraMap T K))
  infer_instance

theorem connectedSpace_of_flat_of_genericFibre (T K : Type) [CommRing T] [IsDomain T] [Field K]
    [Algebra T K] [IsFractionRing T K] {X : Scheme.{0}} (f : X ⟶ Sp T) [Flat f]
    [ConnectedSpace ↥(pullback f (spMap (algebraMap T K)))] : ConnectedSpace X := by
  have := isDominant_genericFibre_of_flat T K f
  let g := pullback.fst f (spMap (algebraMap T K))
  have h : _root_.IsConnected (closure (Set.range g)) := (isConnected_range g.continuous).closure
  rw [g.denseRange.closure_range] at h
  exact connectedSpace_iff_univ.mpr h

theorem isIntegral_and_isNormalScheme_of_smooth (T K : Type) [CommRing T] [IsDomain T]
    [IsNoetherianRing T] [IsIntegrallyClosed T] [Field K] [Algebra T K] [IsFractionRing T K]
    {X : Scheme.{0}} (f : X ⟶ Sp T) [Smooth f]
    [ConnectedSpace ↥(pullback f (spMap (algebraMap T K)))] :
    IsIntegral X ∧ ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X := by
  have hT : GlobalTheory.IsNormalScheme (Sp T) := inferInstance
  have hX : GlobalTheory.IsNormalScheme X := (isNormalScheme_iff X).mpr
    (forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth f ((isNormalScheme_iff _).mp hT))
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have := connectedSpace_of_flat_of_genericFibre T K f
  exact ⟨IsNormalScheme.isIntegral_of_connectedSpace X, hX.pred X⟩

theorem isIntegral_and_isNormalScheme_of_smooth_dvr :
    ∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K]
      [IsFractionRing T K] (G : Over (Sp T)), Smooth G.hom →
      ConnectedSpace ((Over.pullback (spMap (algebraMap T K))).obj G).left →
      IsIntegral G.left ∧ ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme G.left := by
  intro T K _ _ _ _ _ _ G hG hc
  have : ConnectedSpace ↥(pullback G.hom (spMap (algebraMap T K))) := hc
  exact isIntegral_and_isNormalScheme_of_smooth T K G.hom

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsIsoOfIsOpenImmersionOfGeometricallyConnected
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

namespace OpenSubgroupScheme

variable {K : Type} [Field K] {Ga G : Over (Spec (CommRingCat.of K))}

lemma mem_range_iff_factors (p : Ga ⟶ G) [IsOpenImmersion p.left] (x : 𝟙_ _ ⟶ G) :
    x.left (IsLocalRing.closedPoint K) ∈ Set.range p.left ↔ ∃ a : 𝟙_ _ ⟶ Ga, a ≫ p = x := by
  constructor
  · intro h
    have hr : Set.range x.left ⊆ Set.range p.left := by
      rintro _ ⟨z, rfl⟩
      have : z = IsLocalRing.closedPoint K :=
        Subsingleton.elim (α := Spec (CommRingCat.of K)) _ _
      rw [this]; exact h
    refine ⟨Over.homMk (IsOpenImmersion.lift p.left x.left hr) ?_, ?_⟩
    · rw [← Over.w p, ← Category.assoc, IsOpenImmersion.lift_fac]
      exact Over.w x
    · ext1
      simp
  · rintro ⟨a, rfl⟩
    exact ⟨a.left (IsLocalRing.closedPoint K), rfl⟩

lemma exists_point [IsAlgClosed K] [LocallyOfFiniteType G.hom] (y : G.left) (hy : IsClosed {y}) :
    ∃ x : 𝟙_ _ ⟶ G, x.left (IsLocalRing.closedPoint K) = y :=
  ⟨Over.homMk (pointOfClosedPoint G.hom y hy) (pointOfClosedPoint_comp G.hom y hy),
    pointOfClosedPoint_apply G.hom y hy _⟩

lemma comp_mulRight [GrpObj G] (x g : 𝟙_ _ ⟶ G) : x ≫ (GrpObj.mulRight g).hom = x * g := by
  rw [GrpObj.mulRight_hom, Hom.mul_def, comp_lift_assoc, Category.comp_id, ← Category.assoc,
    Subsingleton.elim (x ≫ toUnit G) (𝟙 _), Category.id_comp]

lemma mulRight_apply [GrpObj G] (x g : 𝟙_ _ ⟶ G) :
    (GrpObj.mulRight g).hom.left (x.left (IsLocalRing.closedPoint K)) =
      (x * g).left (IsLocalRing.closedPoint K) := by
  rw [← comp_mulRight]; rfl

lemma range_eq_univ [IsAlgClosed K] [GrpObj Ga] [GrpObj G] (p : Ga ⟶ G) [IsMonHom p]
    [IsOpenImmersion p.left] [LocallyOfFiniteType G.hom] [ConnectedSpace G.left] :
    Set.range p.left = Set.univ := by
  have := LocallyOfFiniteType.jacobsonSpace G.hom
  set U : Set G.left := Set.range p.left with hU
  have hUo : IsOpen U := p.left.isOpenEmbedding.isOpen_range
  let V : Set G.left := ⋃ g : {g : 𝟙_ _ ⟶ G // ¬ ∃ a : 𝟙_ _ ⟶ Ga, a ≫ p = g},
    (GrpObj.mulRight g.1).hom.left ⁻¹' U
  have hVo : IsOpen V := isOpen_iUnion fun g => hUo.preimage (Scheme.Hom.continuous _)
  have hdisj : U ∩ V = ∅ := by
    by_contra hne
    obtain ⟨y, ⟨hyU, hyV⟩, hyc⟩ := nonempty_inter_closedPoints (Set.nonempty_iff_ne_empty.mpr hne)
      (hUo.inter hVo).isLocallyClosed
    obtain ⟨x, rfl⟩ := exists_point y hyc
    obtain ⟨g, hg⟩ := Set.mem_iUnion.mp hyV
    rw [Set.mem_preimage, mulRight_apply] at hg
    obtain ⟨a, ha⟩ := (mem_range_iff_factors p x).mp hyU
    obtain ⟨b, hb⟩ := (mem_range_iff_factors p _).mp hg
    refine g.2 ⟨a⁻¹ * b, ?_⟩
    rw [MonObj.mul_comp, GrpObj.inv_comp, ha, hb, inv_mul_cancel_left]
  have hone : (1 : 𝟙_ _ ⟶ G).left (IsLocalRing.closedPoint K) ∈ U :=
    (mem_range_iff_factors p _).mpr ⟨1, MonObj.one_comp p⟩
  have hcov : U ∪ V = Set.univ := by
    by_contra hne
    obtain ⟨y, hy, hyc⟩ := nonempty_inter_closedPoints (Set.nonempty_compl.mpr hne)
      (hUo.union hVo).isClosed_compl.isLocallyClosed
    obtain ⟨x, rfl⟩ := exists_point y hyc
    rw [Set.mem_compl_iff, Set.mem_union, not_or] at hy
    refine hy.2 (Set.mem_iUnion.mpr ⟨⟨x⁻¹, ?_⟩, ?_⟩)
    · rintro ⟨a, ha⟩
      refine hy.1 ((mem_range_iff_factors p x).mpr ⟨a⁻¹, ?_⟩)
      rw [GrpObj.inv_comp, ha, inv_inv]
    · rw [Set.mem_preimage, mulRight_apply, mul_inv_cancel]
      exact hone
  have hc : Uᶜ = V := by
    ext y
    constructor
    · intro hy
      exact ((hcov ▸ Set.mem_univ y : y ∈ U ∪ V)).resolve_left hy
    · intro hy hyU
      exact (hdisj ▸ ⟨hyU, hy⟩ : y ∈ (∅ : Set G.left))
  have hcl : IsClopen U := ⟨isOpen_compl_iff.mp (hc ▸ hVo), hUo⟩
  exact hcl.eq_univ ⟨_, hone⟩

end OpenSubgroupScheme

theorem isIso_of_isOpenImmersion_of_geometricallyConnected :
    ∀ (S : Scheme.{0}) (Ga G : Over S) [GrpObj Ga] [GrpObj G] (p : Ga ⟶ G), IsMonHom p →
      IsOpenImmersion p.left → LocallyOfFiniteType G.hom → GeometricallyConnected G.hom → IsIso p := by
  intro S Ga G _ _ p _ _ _ _
  have hsurj : Set.range p.left = Set.univ := by
    refine Set.eq_univ_of_forall fun y => ?_
    let s : S := G.hom y
    let Ω : Type := AlgebraicClosure (S.residueField s)
    let t : Spec (CommRingCat.of Ω) ⟶ S :=
      Spec.map (CommRingCat.ofHom (algebraMap (S.residueField s) Ω)) ≫ S.fromSpecResidueField s
    have ht : G.hom y = t (IsLocalRing.closedPoint Ω) :=
      (Scheme.fromSpecResidueField_apply s _).symm
    obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback y _ ht
    have : IsOpenImmersion ((Over.pullback t).map p).left :=
      MorphismProperty.overPullbackMap _ _ ‹_›
    have : LocallyOfFiniteType ((Over.pullback t).obj G).hom := by
      show LocallyOfFiniteType (pullback.snd G.hom t); infer_instance
    have : ConnectedSpace ((Over.pullback t).obj G).left :=
      GeometricallyConnected.geometrically_connectedSpace _ _ _ (.of_hasPullback G.hom t)
    have h := OpenSubgroupScheme.range_eq_univ ((Over.pullback t).map p)
    obtain ⟨w, hw⟩ : z ∈ Set.range ((Over.pullback t).map p).left := h ▸ Set.mem_univ _
    refine ⟨pullback.fst Ga.hom t w, ?_⟩
    have e : ((Over.pullback t).map p).left ≫ pullback.fst G.hom t = pullback.fst Ga.hom t ≫ p.left :=
      pullback.lift_fst _ _ _
    rw [← hz, ← hw, ← Scheme.Hom.comp_apply, ← e]
    rfl
  have : IsIso p.left := isIso_of_isOpenImmersion_of_opensRange_eq_top p.left (by
    ext1
    exact hsurj)
  have : IsIso ((Over.forget S).map p) := this
  exact isIso_of_reflects_iso p (Over.forget S)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.RingHomFlatCodescendsAlongFaithfullyFlat
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem ringHom_flat_codescendsAlong_faithfullyFlat :
    RingHom.CodescendsAlong.{0} RingHom.Flat RingHom.FaithfullyFlat := by
  refine .mk _ RingHom.Flat.respectsIso fun R S T _ _ _ _ _ h h' ↦ ?_
  rw [RingHom.flat_algebraMap_iff] at h' ⊢
  rw [RingHom.faithfullyFlat_algebraMap_iff] at h
  exact .of_flat_tensorProduct R T S

theorem flat_descendsAlong_fpqc :
    MorphismProperty.DescendsAlong (@Flat : MorphismProperty Scheme.{0})
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact) :=
  HasRingHomProperty.descendsAlong_flat ringHom_flat_codescendsAlong_faithfullyFlat

theorem isPullback_overPullback_map_left {S S' : Scheme.{0}} (f : S' ⟶ S) {X Y : Over S}
    (φ : X ⟶ Y) :
    IsPullback ((Over.pullback f).map φ).left (pullback.fst X.hom f) (pullback.fst Y.hom f)
      φ.left := by
  refine IsPullback.flip (IsPullback.of_bot (v₂₁ := pullback.snd Y.hom f) (v₂₂ := Y.hom) (h₃₁ := f)
    ?_ (pullback.lift_fst _ _ _).symm (IsPullback.of_hasPullback Y.hom f))
  have h₁ : ((Over.pullback f).map φ).left ≫ pullback.snd Y.hom f = pullback.snd X.hom f :=
    pullback.lift_snd _ _ _
  rw [h₁, Over.w φ]
  exact IsPullback.of_hasPullback X.hom f

theorem flat_of_flat_fieldBaseChange (k k' : Type) [Field k] [Field k'] (σ : k →+* k')
    (X Y : Over (Sp k)) (φ : X ⟶ Y)
    (h : Flat ((Over.pullback (spMap σ)).map φ).left) : Flat φ.left := by
  haveI := flat_descendsAlong_fpqc
  have h₁ : Flat (spMap σ) := inferInstance
  have h₂ : Surjective (spMap σ) := inferInstance
  have h₃ : QuasiCompact (spMap σ) := inferInstance
  exact MorphismProperty.of_isPullback_of_descendsAlong (P := @Flat)
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    (isPullback_overPullback_map_left (spMap σ) φ)
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ h

end GlobalTheory
end

