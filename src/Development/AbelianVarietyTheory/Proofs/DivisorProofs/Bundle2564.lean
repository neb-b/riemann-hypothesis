module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1984
public import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0039
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2390
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0003
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0005
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0006
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0007
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0008
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Stokes
public import ReciprocityTheory.AnalyticForms.PotentialTheory.SNCAtlas
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0002
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PLCurveA
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PLLocalStatement
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Pullback
public import ReciprocityTheory.AnalyticForms.PotentialTheory.AtlasIndep
public import ReciprocityTheory.AnalyticForms.PotentialTheory.DegreeInt
public import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffFubiniStudyRatioCompChart0
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimEqSucc
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1246
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothConeSumGeneratorsEqOfCommonInteriorPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

namespace GlobalTheory.TInj

open GlobalTheory.Poinc

theorem cone_gen_mem_of_common {O : Type} [CommRing O] {bar : O → O} {φ : InvFun O} {X : Type} [AddCommGroup X]
    [Module O X] [Module.Finite O X] {r r' : ℕ} {ζ : Fin r → LinearMap.BilinForm ℤ X}
    {ζ' : Fin r' → LinearMap.BilinForm ℤ X} (hζ : IsCone bar φ ζ) (hζ' : IsCone bar φ ζ') (c : Fin r → ℕ)
    (c' : Fin r' → ℕ) (hc : ∀ j, 0 < c j) (he : ∑ j, c j • ζ j = ∑ j, c' j • ζ' j) (j : Fin r) :
    ∃ j', ζ j = ζ' j' := by
  obtain ⟨k, d, hk, hd⟩ := intCone_absorb hζ.mem hζ.nonneg hζ.linear hζ' c c' he j (hc j)
  have hd' : ∑ i, d i • ζ' i = ∑ l, (Pi.single j k : Fin r → ℕ) l • ζ l := by
    rw [← hd, Finset.sum_eq_single j (fun l _ hl => by simp [Pi.single_apply, hl]) (by simp)]
    simp
  have habs : ∀ i, 0 < d i → ∃ (k' : ℕ) (e : Fin r → ℕ), 0 < k' ∧ k' • ζ' i = ∑ l, e l • ζ l :=
    fun i hi => intCone_absorb hζ'.mem hζ'.nonneg hζ'.linear hζ d _ hd' i hi
  obtain ⟨f, hf⟩ := hζ.basis.exists_dual
  obtain ⟨g, hg⟩ := hζ'.basis.exists_dual
  let G : Fin r → balForms bar X := fun l => ⟨ζ l, hζ.mem l⟩
  let G' : Fin r' → balForms bar X := fun i => ⟨ζ' i, hζ'.mem i⟩
  have hfG : ∀ l m, f l (G m) = if l = m then 1 else 0 := hf
  have hgG : ∀ i m, g i (G' m) = if i = m then 1 else 0 := hg
  have hdG : k • G j = ∑ i, d i • G' i := Subtype.ext (by simp [G, G', hd])
  have hpos : ∀ i, 0 < d i → ∀ l, 0 ≤ f l (G' i) := by
    intro i hi l
    obtain ⟨k', e, hk', he'⟩ := habs i hi
    have h0 : k' • G' i = ∑ m, e m • G m := Subtype.ext (by simp [G, G', he'])
    have h1 := congrArg (f l) h0
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_nsmul, map_sum] at h1
    simp only [map_nsmul, hfG, smul_ite, smul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true, nsmul_eq_mul,
      _root_.mul_one] at h1
    have hk'' : (0 : ℤ) < k' := by exact_mod_cast hk'
    by_contra hneg
    push_neg at hneg
    have : (k' : ℤ) * f l (G' i) < 0 := mul_neg_of_pos_of_neg hk'' hneg
    linarith [Int.natCast_nonneg (e l)]
  have hex : ∃ i, 0 < d i := by
    by_contra hno
    push_neg at hno
    have h0 : k • ζ j = 0 := by
      rw [hd]
      exact Finset.sum_eq_zero fun i _ => by rw [Nat.le_zero.1 (hno i), zero_smul]
    refine hζ.linearIndependent.ne_zero j (LinearMap.ext₂ fun x y => ?_)
    have h1 := LinearMap.congr_fun₂ h0 x y
    simp only [LinearMap.smul_apply, LinearMap.zero_apply, nsmul_eq_mul] at h1
    rcases mul_eq_zero.1 h1 with h2 | h2
    · exact absurd h2 (by exact_mod_cast hk.ne')
    · simpa using h2
  obtain ⟨i, hi⟩ := hex
  have hzero : ∀ l, l ≠ j → f l (G' i) = 0 := by
    intro l hl
    have h1 := congrArg (f l) hdG
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_nsmul, map_sum, hfG, if_neg hl, smul_zero] at h1
    simp only [map_nsmul, nsmul_eq_mul] at h1
    have hnn : ∀ i' ∈ Finset.univ, 0 ≤ (d i' : ℤ) * f l (G' i') := fun i' _ => by
      rcases Nat.eq_zero_or_pos (d i') with h | h
      · simp [h]
      · exact mul_nonneg (Int.natCast_nonneg _) (hpos i' h l)
    have h2 := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 h1.symm i (Finset.mem_univ _)
    exact (mul_eq_zero.1 h2).resolve_left (by exact_mod_cast hi.ne')
  obtain ⟨k', e, hk', he'⟩ := habs i hi
  have hE : k' • G' i = ∑ m, e m • G m := Subtype.ext (by simp [G, G', he'])
  have hem : ∀ m, (e m : ℤ) = k' * f m (G' i) := by
    intro m
    have h1 := congrArg (f m) hE
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_nsmul, map_sum] at h1
    simp only [map_nsmul, hfG, smul_ite, smul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true, nsmul_eq_mul,
      _root_.mul_one] at h1
    exact h1.symm
  have hEj : k' • G' i = e j • G j := by
    rw [hE]
    refine Finset.sum_eq_single j (fun m _ hm => ?_) (by simp)
    have h1 := hem m
    rw [hzero m hm, mul_zero] at h1
    rw [show e m = 0 by exact_mod_cast h1, zero_smul]
  have h1 := congrArg (g i) hEj
  simp only [map_nsmul, hgG, if_true, nsmul_eq_mul, _root_.mul_one] at h1
  have h2 := hem j
  have hk'' : (0 : ℤ) < k' := by exact_mod_cast hk'
  have hu : f j (G' i) * g i (G j) = 1 := by
    have h3 : (k' : ℤ) * (f j (G' i) * g i (G j) - 1) = 0 := by
      rw [mul_sub, ← _root_.mul_assoc, ← h2, _root_.mul_one]
      linarith
    exact sub_eq_zero.1 ((mul_eq_zero.1 h3).resolve_left hk''.ne')
  have hf1 : f j (G' i) = 1 := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one hu with h | h
    · exact h
    · have := Int.natCast_nonneg (e j)
      rw [h2, h] at this
      linarith
  have hej : e j = k' := by
    have := h2
    rw [hf1, _root_.mul_one] at this
    exact_mod_cast this
  rw [hej] at hEj
  refine ⟨i, LinearMap.ext₂ fun x y => ?_⟩
  have h3 := LinearMap.congr_fun₂ (congrArg Subtype.val hEj) x y
  simp only [G, G', Submodule.coe_smul, LinearMap.smul_apply, nsmul_eq_mul] at h3
  exact (mul_left_cancel₀ (by exact_mod_cast hk'.ne' : (k' : ℤ) ≠ 0) h3).symm

theorem coneSum_eq : ∀ (φ : InvFun ℤ) (X : Type) [AddCommGroup X] [Module.Finite ℤ X] (m m' : ℕ)
    (δ : Fin m → LinearMap.BilinForm ℤ X) (δ' : Fin m' → LinearMap.BilinForm ℤ X), IsCone id φ δ → IsCone id φ δ' →
    ∀ (c : Fin m → ℕ) (c' : Fin m' → ℕ), (∀ k, 0 < c k) → (∀ k, 0 < c' k) →
    ∑ k, c k • δ k = ∑ k, c' k • δ' k → ∑ k, δ k = ∑ k, δ' k := by
  intro φ X _ _ m m' δ δ' hδ hδ' c c' hc hc' he
  classical
  have h1 : ∀ k, ∃ j, δ k = δ' j := cone_gen_mem_of_common hδ hδ' c c' hc he
  have h2 : ∀ j, ∃ k, δ' j = δ k := cone_gen_mem_of_common hδ' hδ c' c hc' he.symm
  have himg : Finset.univ.image δ = Finset.univ.image δ' := by
    ext x
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨k, rfl⟩
      obtain ⟨j, hj⟩ := h1 k
      exact ⟨j, hj.symm⟩
    · rintro ⟨j, rfl⟩
      obtain ⟨k, hk⟩ := h2 j
      exact ⟨k, hk.symm⟩
  have e1 : ∑ x ∈ Finset.univ.image δ, x = ∑ k, δ k :=
    Finset.sum_image fun a _ b _ h => hδ.injective h
  have e2 : ∑ x ∈ Finset.univ.image δ', x = ∑ k, δ' k :=
    Finset.sum_image fun a _ b _ h => hδ'.injective h
  rw [← e1, ← e2, himg]

end GlobalTheory.TInj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothSncComponentClosureCharZero
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory.SncComp

theorem smooth_of_regular_stalk (K : Type) [Field K] [PerfectField K] (Y : Scheme.{0}) (q : Y ⟶ Sp K)
    [LocallyOfFiniteType q] (d : ℕ)
    (h : ∀ y : Y, IsClosed ({y} : Set Y) →
      IsRegularLocalRing (Y.presheaf.stalk y) ∧ ringKrullDim (Y.presheaf.stalk y) = d) :
    SmoothOfRelativeDimension d q := by
  have : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace q
  choose A _ _ j _ pt hj hq using exists_affine_chart_over q
  let 𝒰 : Y.OpenCover := Scheme.Cover.mkOfCovers Y (fun y => Spec (.of (A y))) j (fun y => ⟨y, pt y, hj y⟩)
  have := HasRingHomProperty.instIsZariskiLocalAtSource (P := @SmoothOfRelativeDimension d)
  refine IsZariskiLocalAtSource.of_openCover (P := @SmoothOfRelativeDimension d) 𝒰 fun (y : Y) => ?_
  change SmoothOfRelativeDimension d (j y ≫ q)
  have hft : LocallyOfFiniteType (spMap (algebraMap K (A y))) := by
    have : LocallyOfFiniteType (j y ≫ q) := inferInstance
    rwa [hq y] at this
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at hft
  have : Algebra.FiniteType K (A y) := RingHom.finiteType_algebraMap.mp hft
  rw [hq y]
  refine RegGenSmooth.smooth_of_regular K (A y) d fun m hm => ?_
  let w : Spec (.of (A y)) := (⟨m, inferInstance⟩ : PrimeSpectrum _)
  have hw : IsClosed ({w} : Set (Spec (.of (A y)))) := (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).2 hm
  have hc : IsClosed ({j y w} : Set Y) := by
    have h1 := (j y).isOpenEmbedding.preimage_closedPoints
    have h2 : w ∈ (j y) ⁻¹' closedPoints Y := by rw [h1]; exact hw
    exact h2
  obtain ⟨h1, h2⟩ := h _ hc
  let e := (asIso ((j y).stalkMap w) ≪≫ Spec.stalkIso (.of _) w).commRingCatIsoToRingEquiv
  exact ⟨IsRegularLocalRing.of_ringEquiv e, (ringKrullDim_eq_of_ringEquiv e).symm.trans h2⟩

theorem smooth_component : ∀ (F : Type) [Field F] [CharZero F] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp F) (e : ℕ), IsProjOver p → SmoothOfRelativeDimension (e + 1) p → ∀ (r : ℕ) (z : Fin r → X), (∀ x : X, FinalTheorems.LSncAt X (fun a => (Closeds.closure {z a})) x) → ∀ a, SmoothOfRelativeDimension e (closι (z a) ≫ p) := by
  intro F _ _ X _ p e _ hsm r z hL a
  have : Smooth p := SmoothOfRelativeDimension.smooth (e + 1) p
  have hdim := GlobalTheory.HSCore.VanishNumberField.topologicalKrullDim_eq_of_smooth p (e + 1) hsm
  refine smooth_of_regular_stalk F _ _ e fun y hy => ?_
  let I := Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {z a})
  have hc : IsClosed ({closι (z a) y} : Set X) := by
    simpa using (closι (z a)).isClosedEmbedding.isClosedMap _ hy
  have hd := (ProperCut.ringKrullDim_stalk_eq p hc).trans hdim
  obtain ⟨hreg, n, t, ε, hR, hI⟩ := hL (closι (z a) y)
  have hmem : closι (z a) y ∈ Closeds.closure {z a} := by
    have := Vanishing.ι_mem_support I y
    have h := Scheme.IdealSheafData.coe_support_vanishingIdeal (Closeds.closure {z a})
    exact h.le this
  have hker : RingHom.ker ((closι (z a)).stalkMap y).hom = Ideal.span {t (ε ⟨a, hmem⟩)} :=
    (Vanishing.ker_stalkMap I y).trans (hI ⟨a, hmem⟩)
  have hm : t (ε ⟨a, hmem⟩) ∈ IsLocalRing.maximalIdeal _ := hR.1 ▸ Ideal.subset_span ⟨_, rfl⟩
  obtain ⟨h1, h2⟩ := isRegularLocalRing_quotient_of_not_mem_sq hm ((regular_params_spec t hR.1 hR.2).1 _)
  let φ := (Ideal.quotEquivOfEq hker.symm).trans
    (RingHom.quotientKerEquivOfSurjective ((closι (z a)).stalkMap_surjective y))
  refine ⟨IsRegularLocalRing.of_ringEquiv φ, ?_⟩
  rw [← ringKrullDim_eq_of_ringEquiv φ]
  rw [hd] at h2
  generalize ringKrullDim (X.presheaf.stalk (closι (z a) y) ⧸ Ideal.span {t (ε ⟨a, hmem⟩)}) = u at h2
  induction u using WithBot.recBotCoe with
  | bot => exact absurd h2 (by rw [WithBot.bot_add]; exact WithBot.bot_ne_coe)
  | coe u =>
    induction u using ENat.recTopCoe with
    | top => exact absurd (WithBot.coe_injective h2) (ENat.top_ne_coe _)
    | coe u =>
      have : u + 1 = e + 1 := by exact_mod_cast h2
      exact_mod_cast Nat.succ_injective this

end GlobalTheory.SncComp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothWeightedLineBundleIsometryCalculus
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory.Mix.IsomCalc

variable {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k} {σ : k →+* ℂ}
variable {L M : MLine p σ}

theorem isom_of_local {J : Type} (W : J → X.Opens) (hW : ∀ x, ∃ j, x ∈ W j) (a : J → M.B.ι)
    (b : J → L.B.ι) (ha : ∀ j, W j ≤ M.B.U (a j)) (hb : ∀ j, W j ≤ L.B.U (b j)) (u : ∀ j, Γ(X, W j)ˣ)
    (hu : ∀ (x : X) j j', x ∈ W j → x ∈ W j' → gm (𝟙 X) x (W j) (u j) =
      gm (𝟙 X) x _ (M.B.g (a j) (a j')) * (gm (𝟙 X) x _ (L.B.g (b j) (b j')))⁻¹ * gm (𝟙 X) x (W j') (u j'))
    (hφ : ∀ j (y : CxPts p σ), y ∈ ptsIn p σ (W j) →
      M.φ.φ (a j) y = L.φ.φ (b j) y + logSq y (W j) (u j)) : L.Isom M := by
  let v (c : M.B.ι × L.B.ι) (j : J) : Γ(X, M.B.U c.1 ⊓ L.B.U c.2 ⊓ W j)ˣ :=
    res (inf_le_inf inf_le_left (ha j)) (M.B.g c.1 (a j)) *
      (res (inf_le_inf inf_le_right (hb j)) (L.B.g c.2 (b j)))⁻¹ * res inf_le_right (u j)
  have hv (c j) (x : X) (hx : x ∈ M.B.U c.1 ⊓ L.B.U c.2 ⊓ W j) : gm (𝟙 X) x _ (v c j) =
      gm (𝟙 X) x _ (M.B.g c.1 (a j)) * (gm (𝟙 X) x _ (L.B.g c.2 (b j)))⁻¹ * gm (𝟙 X) x _ (u j) := by
    simp only [v, map_mul, map_inv, gm_res (𝟙 X) x _ hx]
  have key : ∀ {G : Type} [CommGroup G] (a b c d e : G), a * b * (c * d)⁻¹ * e = a * c⁻¹ * (b * d⁻¹ * e) := by
    intro G _ a b c d e
    simp only [mul_inv]
    ac_rfl
  have hg (c : M.B.ι × L.B.ι) : ∃ s : Γ(X, M.B.U c.1 ⊓ L.B.U c.2)ˣ, ∀ j, res inf_le_left s = v c j := by
    refine glue_unit _ _ _ (fun x hx => ?_) (v c) fun j j' x hx => ?_
    · obtain ⟨j, hj⟩ := hW x
      exact Opens.mem_iSup.2 ⟨j, hx, hj⟩
    · rw [hv c j x hx.1, hv c j' x hx.2, hu x j j' hx.1.2 hx.2.2,
        ← gm_cocycle M.φ.isLB (𝟙 X) x hx.1.1.1 (ha j hx.1.2) (ha j' hx.2.2),
        ← gm_cocycle L.φ.isLB (𝟙 X) x hx.1.1.2 (hb j hx.1.2) (hb j' hx.2.2), key]
  choose s hs using hg
  have hs' (c j) (x : X) (hx : x ∈ M.B.U c.1 ⊓ L.B.U c.2 ⊓ W j) : gm (𝟙 X) x _ (s c) =
      gm (𝟙 X) x _ (M.B.g c.1 (a j)) * (gm (𝟙 X) x _ (L.B.g c.2 (b j)))⁻¹ * gm (𝟙 X) x _ (u j) := by
    rw [← hv c j x hx, ← hs, gm_res (𝟙 X) x _ hx]
  refine ⟨⟨s⟩, (isGen_iff_germ _).2 fun x c c' hc hc' => ?_, fun a₀ b₀ y h₁ h₂ => ?_⟩
  · obtain ⟨j, hj⟩ := hW x
    refine (hs' c j x ⟨hc, hj⟩).trans (Eq.trans ?_ (congrArg₂ (· * ·)
      (gm_div' M.B L.B (𝟙 X) x c c' hc hc') (hs' c' j x ⟨hc', hj⟩)).symm)
    rw [← gm_cocycle M.φ.isLB (𝟙 X) x hc.1 hc'.1 (ha j hj),
      ← gm_cocycle L.φ.isLB (𝟙 X) x hc.2 hc'.2 (hb j hj), key]
  · obtain ⟨j, hj⟩ := hW (under y)
    have hj' : y ∈ ptsIn p σ (W j) := mem_ptsIn.2 hj
    have hy : y ∈ ptsIn p σ (M.B.U a₀ ⊓ L.B.U b₀ ⊓ W j) := by simp [*]
    have e : logSq y _ (s (a₀, b₀)) = logSq y _ (M.B.g a₀ (a j)) + -logSq y _ (L.B.g b₀ (b j)) +
        logSq y _ (u j) := by
      rw [← logSq_res inf_le_left hy, hs (a₀, b₀) j]
      simp only [v, logSq_mul hy, logSq_inv hy, logSq_res _ hy]
    have e₁ : _ = _ - logSq y _ (M.B.g a₀ (a j)) := M.φ.trans a₀ (a j) y h₁ (ptsIn_mono (ha j) hj')
    have e₂ : _ = _ - logSq y _ (L.B.g b₀ (b j)) := L.φ.trans b₀ (b j) y h₂ (ptsIn_mono (hb j) hj')
    have e₃ := hφ j y hj'
    change _ = _ + logSq y _ (s (a₀, b₀))
    linarith

theorem isom_of_chart (a : L.B.ι → M.B.ι) (ha : ∀ j, L.B.U j ≤ M.B.U (a j))
    (hg : ∀ (x : X) j j', x ∈ L.B.U j → x ∈ L.B.U j' →
      gm (𝟙 X) x _ (L.B.g j j') = gm (𝟙 X) x _ (M.B.g (a j) (a j')))
    (hφ : ∀ j (y : CxPts p σ), y ∈ ptsIn p σ (L.B.U j) → M.φ.φ (a j) y = L.φ.φ j y) : L.Isom M :=
  isom_of_local L.B.U (exists_chart L.φ.isLB) a id ha (fun _ => le_rfl) (fun _ => 1)
    (fun x j j' h h' => by rw [map_one, map_one, ← hg x j j' h h', mul_one]; exact (mul_inv_cancel _).symm)
    fun j y h => by rw [logSq_one h, add_zero]; exact hφ j y h

theorem isom_refl (L : MLine p σ) : L.Isom L :=
  isom_of_chart id (fun _ => le_rfl) (fun _ _ _ _ _ => rfl) fun _ _ _ => rfl

theorem isom_pull (h : L.Isom M) (π : Y ⟶ X) (hπ : π ≫ p = q) :
    (L.pull π hπ).Isom (M.pull π hπ) := by
  obtain ⟨w, hw, h⟩ := h
  refine isom_of_local (fun c : M.B.ι × L.B.ι => π ⁻¹ᵁ (M.B.U c.1 ⊓ L.B.U c.2))
    (fun x => ?_) (fun c _ => c.1) (fun c _ => c.2) (fun _ _ h => mem_pull.2 h.1)
    (fun _ _ h => mem_pull.2 h.2) (fun c => pullU π _ (w.s (c.1, c.2))) (fun x c c' hc hc' => ?_)
    fun c y hy => ?_
  · obtain ⟨a, ha⟩ := exists_chart M.φ.isLB (π x)
    obtain ⟨b, hb⟩ := exists_chart L.φ.isLB (π x)
    exact ⟨(a, b), ha, hb⟩
  · refine Eq.trans ?_ (congrArg (· * _) (congrArg₂ (fun a b => a * b⁻¹)
      (gm_pull_g M.B π (𝟙 Y) x (fun _ => c.1) (fun _ => c'.1) (mem_pull.2 hc.1) (mem_pull.2 hc'.1))
      (gm_pull_g L.B π (𝟙 Y) x (fun _ => c.2) (fun _ => c'.2) (mem_pull.2 hc.2) (mem_pull.2 hc'.2)))).symm
    exact (gm_pull (U := M.B.U c.1 ⊓ L.B.U c.2) (𝟙 Y) π x hc (w.s (c.1, c.2))).trans
      ((gm_isGen hw (𝟙 Y ≫ π) x _ _ _ _ hc.1 hc'.1 hc.2 hc'.2).trans (congrArg (_ * ·)
        (gm_pull (U := M.B.U c'.1 ⊓ L.B.U c'.2) (𝟙 Y) π x hc' (w.s (c'.1, c'.2))).symm))
  · have hy' : PtsOver.map π hπ _ y ∈ ptsIn p σ (M.B.U c.1 ⊓ L.B.U c.2) := hy
    refine (M.φ.pull_φ π hπ _ y).trans ((h _ _ _ (mem_ptsIn_inf.1 hy').1 (mem_ptsIn_inf.1 hy').2).trans
      (congrArg₂ (· + ·) (L.φ.pull_φ π hπ (fun _ => c.2) y).symm ?_))
    exact congrArg (fun z => Real.log (‖z‖ ^ 2)) (ev_app π hπ _ _ y).symm

theorem isom_pull_tens (L M : MLine p σ) (π : Y ⟶ X) (hπ : π ≫ p = q) :
    ((L.tens M).pull π hπ).Isom ((L.pull π hπ).tens (M.pull π hπ)) :=
  isom_of_chart (fun j => (fun _ => (j PUnit.unit).1, fun _ => (j PUnit.unit).2))
    (fun _ _ h => ⟨mem_pull.2 (mem_pull.1 h).1, mem_pull.2 (mem_pull.1 h).2⟩)
    (fun x j j' h h' => by
      have e := mem_pull.1 h
      have e' := mem_pull.1 h'
      refine ((gm_pull_g (CechPic.tens L.B M.B) π (𝟙 Y) x j j' h h').trans
        (gm_tens L.B M.B (𝟙 Y ≫ π) x _ _ e e')).trans (Eq.symm ?_)
      exact (gm_tens (L.B.pull π) (M.B.pull π) (𝟙 Y) x (fun _ => (j PUnit.unit).1, fun _ => (j PUnit.unit).2)
        (fun _ => (j' PUnit.unit).1, fun _ => (j' PUnit.unit).2) ⟨mem_pull.2 e.1, mem_pull.2 e.2⟩
        ⟨mem_pull.2 e'.1, mem_pull.2 e'.2⟩).trans (congrArg₂ (· * ·)
          (gm_pull_g L.B π (𝟙 Y) x _ _ (mem_pull.2 e.1) (mem_pull.2 e'.1))
          (gm_pull_g M.B π (𝟙 Y) x _ _ (mem_pull.2 e.2) (mem_pull.2 e'.2))))
    fun j y _ => (congrArg₂ (· + ·) (L.φ.pull_φ π hπ _ y) (M.φ.pull_φ π hπ _ y)).trans
      ((L.tens M).φ.pull_φ π hπ j y).symm

theorem isom_pull_ofFun (u : CxPts p σ → ℝ) (hu : ∀ y, CInfAt u y) (π : Y ⟶ X) (hπ : π ≫ p = q)
    (hu' : ∀ z, CInfAt (fun z => u (ptMap π hπ σ z)) z) :
    ((MLine.ofFun u hu).pull π hπ).Isom (MLine.ofFun (fun z => u (ptMap π hπ σ z)) hu') :=
  isom_of_chart (fun _ => PUnit.unit) (fun _ => le_top)
    (fun x j j' h h' => (gm_pull_g (LB.triv X) π (𝟙 Y) x j j' h h').trans ((map_one _).trans (map_one _).symm))
    fun j y _ => ((MLine.ofFun u hu).φ.pull_φ π hπ j y).symm

theorem isom_addFn (L : MLine p σ) (u : CxPts p σ → ℝ) (hu : ∀ y, CInfAt u y) :
    (L.addFn u hu).Isom (L.tens (MLine.ofFun u hu)) :=
  isom_of_chart (fun c => (c, PUnit.unit)) (fun _ _ h => ⟨h, trivial⟩)
    (fun x c c' h h' => ((gm_tens L.B (LB.triv X) (𝟙 X) x (c, PUnit.unit) (c', PUnit.unit)
      ⟨h, trivial⟩ ⟨h', trivial⟩).trans ((congrArg (_ * ·) (map_one _)).trans (mul_one _))).symm)
    fun _ _ _ => rfl

theorem isom_pull_pull (L : MLine p σ) (π : Y ⟶ X) (hπ : π ≫ p = q) {Z : Scheme.{0}} {r : Z ⟶ Sp k} (i : Z ⟶ Y)
    (hi : i ≫ q = r) (h₀ : (i ≫ π) ≫ p = r) : ((L.pull π hπ).pull i hi).Isom (L.pull (i ≫ π) h₀) :=
  isom_of_chart (fun J => fun _ => J PUnit.unit PUnit.unit)
    (fun _ _ h => mem_pull₂.2 (mem_pull.1 (mem_pull.1 h)))
    (fun x (J J' : PUnit → PUnit → L.B.ι) h h' => by
      have e := mem_pull.1 h
      have e' := mem_pull.1 h'
      refine (gm_pull_g (L.B.pull π) i (𝟙 Z) x J J' h h').trans
        ((gm_pull_g L.B π (𝟙 Z ≫ i) x (J PUnit.unit) (J' PUnit.unit) e e').trans ?_)
      rw [Category.assoc]
      exact (gm_pull_g L.B (i ≫ π) (𝟙 Z) x (fun _ => J PUnit.unit PUnit.unit) (fun _ => J' PUnit.unit PUnit.unit)
        (mem_pull₂.2 (mem_pull.1 e)) (mem_pull₂.2 (mem_pull.1 e'))).symm)
    fun (J : PUnit → PUnit → L.B.ι) y _ => by
      refine (L.φ.pull_φ (i ≫ π) h₀ (fun _ => J PUnit.unit PUnit.unit) y).trans (Eq.trans ?_
        ((Weight.pull_φ (L.pull π hπ).φ i hi J y).trans (L.φ.pull_φ π hπ (J PUnit.unit) _)).symm)
      exact congrArg _ (Subtype.ext (by simp [PtsOver.map_val]))

end GlobalTheory.Mix.IsomCalc


open GlobalTheory.Mix.IsomCalc in
theorem GlobalTheory.Mix.isom_calculus : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (σ : k →+* ℂ) (π : Y ⟶ X) (hπ : π ≫ p = q), (∀ A : MLine p σ, A.Isom A) ∧ (∀ A B : MLine p σ, A.Isom B → (A.pull π hπ).Isom (B.pull π hπ)) ∧ (∀ A B : MLine p σ, ((A.tens B).pull π hπ).Isom ((A.pull π hπ).tens (B.pull π hπ))) ∧ (∀ (u : CxPts p σ → ℝ) (hu : ∀ y, CInfAt u y), ((MLine.ofFun u hu).pull π hπ).Isom (MLine.ofFun (fun z => u (ptMap π hπ σ z)) fun z => (hu _).pull π hπ)) ∧ (∀ (A : MLine p σ) (u : CxPts p σ → ℝ) (hu : ∀ y, CInfAt u y), (A.addFn u hu).Isom (A.tens (MLine.ofFun u hu))) ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp k) (g : Z ⟶ Y) (hg : g ≫ q = r) (h : (g ≫ π) ≫ p = r) (A : MLine p σ), ((A.pull π hπ).pull g hg).Isom (A.pull (g ≫ π) h) :=
  fun _ _ _ _ _ _ _ π hπ => ⟨isom_refl, fun _ _ h => isom_pull h π hπ, fun A B => isom_pull_tens A B π hπ,
    fun u hu => isom_pull_ofFun u hu π hπ _, isom_addFn, fun _ _ g hg h A => isom_pull_pull A π hπ g hg h⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothWeightsDifferBySmoothFunction
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory.Mix

theorem weight_sub_cInf : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) (B : LB X) (φ ψ : Weight p σ B), φ.IsCInf → ψ.IsCInf → ∃ u : CxPts p σ → ℝ, (∀ y, CInfAt u y) ∧ ∀ i, ∀ y ∈ ptsIn p σ (B.U i), ψ.φ i y = φ.φ i y + u y := by
  intro k _ X p σ B φ ψ hφ hψ
  have key : ∀ i y, y ∈ ptsIn p σ (B.U i) →
      ψ.φ i y - φ.φ i y = ψ.φ (pick φ.isLB y) y - φ.φ (pick φ.isLB y) y := by
    intro i y hi
    rw [ψ.trans _ i y (mem_pick φ.isLB y) hi, φ.trans _ i y (mem_pick φ.isLB y) hi]
    ring
  refine ⟨fun y => ψ.φ (pick φ.isLB y) y - φ.φ (pick φ.isLB y) y, fun y => ?_, fun i y hi => ?_⟩
  · have hy := mem_pick φ.isLB y
    have hs : CInfAt (fun z => ψ.φ (pick φ.isLB y) z + -φ.φ (pick φ.isLB y) z) y :=
      (hψ _ y hy).add (hφ _ y hy).neg
    refine hs.congr ?_
    filter_upwards [(isOpen_ptsIn _).mem_nhds hy] with z hz
    rw [← key _ z hz, sub_eq_add_neg]
  · have := key i y hi
    linarith

end GlobalTheory.Mix
end

