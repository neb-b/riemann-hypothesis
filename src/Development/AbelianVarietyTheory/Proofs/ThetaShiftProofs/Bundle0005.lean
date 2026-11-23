module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0025
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MajPos
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.BijectiveRestrictPointsOfEtaleOfHenselian

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.CoeffEqZeroOfHasSumZero
section
namespace GlobalTheory.LaurentFJ

open Complex ReciprocityTheory.ChartRestriction.G.FD

noncomputable section

theorem coeff_eq_zero_of_hasSum_zero (d : ℤ → ℂ)
    (h : ∀ t : ℝ, HasSum (fun k : ℤ => d k * cexp (2 * Real.pi * I * t) ^ k) 0) (j : ℤ) :
    d j = 0 := by
  have hs : Summable fun k => ‖d k‖ := by
    have := (h 0).summable
    simp only [ofReal_zero, mul_zero, Complex.exp_zero, one_zpow, mul_one] at this
    exact summable_norm_iff.mpr this
  have hpow : ∀ (k : ℤ) (t : ℝ), cexp (2 * Real.pi * I * t) ^ k * cexp (2 * Real.pi * I * t) ^ (-j)
      = cexp ((2 * Real.pi * I * ((k - j : ℤ) : ℂ)) * t) := by
    intro k t
    rw [← Complex.exp_int_mul, ← Complex.exp_int_mul, ← Complex.exp_add]
    congr 1; push_cast; ring
  have hI := intervalIntegral.hasSum_integral_of_dominated_convergence (μ := MeasureTheory.volume)
    (a := 0) (b := 1) (f := fun _ : ℝ => (0 : ℂ))
    (F := fun (k : ℤ) (t : ℝ) => d k * cexp ((2 * Real.pi * I * ((k - j : ℤ) : ℂ)) * t))
    (fun k _ => ‖d k‖)
    (fun k => (by fun_prop : Continuous fun t : ℝ =>
      d k * cexp ((2 * Real.pi * I * ((k - j : ℤ) : ℂ)) * t)).aestronglyMeasurable)
    (fun k => MeasureTheory.ae_of_all _ fun t _ => by
      have : (2 * Real.pi * I * ((k - j : ℤ) : ℂ)) * t =
          ((2 * Real.pi * ((k - j : ℤ) : ℝ) * t : ℝ) : ℂ) * I := by push_cast; ring
      rw [norm_mul, this, Complex.norm_exp_ofReal_mul_I, mul_one])
    (MeasureTheory.ae_of_all _ fun t _ => hs) intervalIntegrable_const
    (MeasureTheory.ae_of_all _ fun t _ => by
      have := (h t).mul_right (cexp (2 * Real.pi * I * t) ^ (-j))
      simp only [zero_mul, mul_assoc (d _), hpow] at this
      exact this)
  have hval : ∀ k : ℤ, (∫ t in (0 : ℝ)..1,
      d k * cexp ((2 * Real.pi * I * ((k - j : ℤ) : ℂ)) * t)) = if k = j then d j else 0 := by
    intro k
    split_ifs with hk
    · subst hk; simp
    · have hc : (2 * Real.pi * I * ((k - j : ℤ) : ℂ)) ≠ 0 := by
        refine mul_ne_zero Complex.two_pi_I_ne_zero ?_
        exact_mod_cast sub_ne_zero.mpr hk
      rw [intervalIntegral.integral_const_mul, integral_exp_mul_complex hc]
      have : cexp (2 * Real.pi * I * ((k - j : ℤ) : ℂ)) = 1 := by
        rw [mul_comm]; exact Complex.exp_int_mul_two_pi_mul_I _
      simp only [ofReal_one, mul_one, ofReal_zero, mul_zero, Complex.exp_zero, this]
      simp
  simp only [hval, intervalIntegral.integral_zero] at hI
  exact (hasSum_ite_eq j (d j)).unique hI

theorem hasSum_fiber_of_hasSum_line {ι : Type*} (c : ι → ℂ) (n : ι → ℤ) (a : ℤ → ℂ) (y : ℝ)
    (f : ℝ → ℂ)
    (ha : ∀ t : ℝ, HasSum (fun k : ℤ => a k * cexp (2 * Real.pi * I * (t + y * I)) ^ k) (f t))
    (hc : ∀ t : ℝ, HasSum (fun i => c i * cexp (2 * Real.pi * I * (t + y * I)) ^ n i) (f t))
    (j : ℤ) : HasSum (fun i : {i // n i = j} => c i) (a j) := by
  have hsum : ∀ k : ℤ, Summable fun i : {i // n i = k} => c i := by
    intro k
    have h1 := ((hc 0).summable.subtype fun i => n i = k).mul_right
      (cexp (2 * Real.pi * I * ((0 : ℝ) + y * I)) ^ (-k))
    refine h1.congr fun i => ?_
    have hi : n i = k := i.2
    simp only [Function.comp_apply, hi]
    rw [mul_assoc, ← zpow_add₀ (Complex.exp_ne_zero _)]
    simp
  have hb : ∀ t : ℝ, HasSum (fun k : ℤ => (∑' i : {i // n i = k}, c i) *
      cexp (2 * Real.pi * I * (t + y * I)) ^ k) (f t) := by
    intro t
    have h1 := (Equiv.sigmaFiberEquiv n).hasSum_iff.mpr (hc t)
    refine h1.sigma fun k => ?_
    have := (hsum k).hasSum.mul_right (cexp (2 * Real.pi * I * (t + y * I)) ^ k)
    refine this.congr_fun fun i => ?_
    simp only [Function.comp_apply, Equiv.sigmaFiberEquiv, Equiv.coe_fn_mk, i.2]
  have hz := coeff_eq_zero_of_hasSum_zero
    (fun k => (a k - ∑' i : {i // n i = k}, c i) * cexp (2 * Real.pi * I * (y * I)) ^ k)
    (fun t => by
      have := (ha t).sub (hb t)
      rw [sub_self] at this
      refine this.congr_fun fun k => ?_
      rw [mul_add, Complex.exp_add, mul_zpow]; ring) j
  have hz' : a j = ∑' i : {i // n i = j}, c i :=
    sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right (zpow_ne_zero _ (Complex.exp_ne_zero _)))
  rw [hz']
  exact (hsum j).hasSum

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E] {r : ℕ}

theorem flow_mem_dom_of_im_nonneg (X : Data E r) {ξ : Fin r → E} (hξ : X.IsIso ξ)
    {x : Frame X.Ψ r} (hx : x ∈ X.dom) (s : X.Ψ → ℂ) (hs : ∀ τ, 0 ≤ (s τ).im) :
    X.flow ξ s x ∈ X.dom := by
  have hiv : X.IsIsoV fun τ => Data.emb τ.1 ξ := by
    intro τ
    refine ⟨?_, ?_⟩
    · have key : hermC τ.1 X.Gm (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) = τ.1 (herm X.Gm ξ ξ) := by
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [hermC, herm, Data.emb, map_sum, map_mul, cc,
          NumberField.IsCMField.complexEmbedding_complexConj]
      change hermC τ.1 X.Gm (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) = 0
      rw [key, hξ.2.1, map_zero]
    · intro h0
      apply hξ.2.2
      funext a
      have := congrFun h0 a
      simpa [Data.emb] using this
  refine (flowDomainCriterion_holds r X _ hiv x hx s).1.2 fun τ => ?_
  have ht : 0 < X.ttV (fun τ => Data.emb τ.1 ξ) x τ :=
    one_div_pos.mpr (mul_pos (MajorantFamilyNorms.c_pos X τ) (X.maj_pos hx τ (hiv τ).2))
  have := div_nonneg (hs τ) ht.le
  linarith

theorem hasSum_fj_of_line (X : Data E r) {la : Wt X.Ψ r} {P : Frame X.Ψ r → ℂ}
    (hP : X.IsSec la P) {ξ : Fin r → E} (hξ : X.IsIso ξ) {x : Frame X.Ψ r} (hx : x ∈ X.dom)
    (sb : X.Ψ → ℝ)
    (hint : ∀ ν : X.Ψ → ℝ, X.fj la ξ ν P x ≠ 0 → ∃ k : ℤ, 2 * ∑ τ, ν τ * sb τ = k)
    (κ u₁ : ℂ) (a : ℤ → ℂ) (y : ℝ)
    (hdom : ∀ w : ℂ, w.im = y → X.flow ξ (fun τ => w * sb τ) x ∈ X.dom)
    (ha : ∀ w : ℂ, w.im = y → HasSum (fun n : ℤ => a n * (u₁ * cexp (2 * Real.pi * I * w)) ^ n)
      (κ * P (X.flow ξ (fun τ => w * sb τ) x))) (j : ℤ) :
    HasSum (fun ν : {ν : X.Ψ → ℝ // 2 * ∑ τ, ν τ * sb τ = j} => κ * X.fj la ξ ν P x)
      (a j * u₁ ^ j) := by
  classical
  set n : (X.Ψ → ℝ) → ℤ := fun ν => ⌊2 * ∑ τ, ν τ * sb τ⌋ with hn
  have hnν : ∀ ν, X.fj la ξ ν P x ≠ 0 → 2 * ∑ τ, ν τ * sb τ = n ν := by
    intro ν hν
    obtain ⟨k, hk⟩ := hint ν hν
    simp only [hn, hk, Int.floor_intCast]
  have him : ∀ t : ℝ, ((t : ℂ) + y * I).im = y := fun t => by simp
  have H := hasSum_fiber_of_hasSum_line (fun ν => κ * X.fj la ξ ν P x) n
    (fun k => a k * u₁ ^ k) y (fun t => κ * P (X.flow ξ (fun τ => ((t : ℂ) + y * I) * sb τ) x))
    (fun t => by
      convert ha _ (him t) using 2 with k
      rw [mul_zpow, mul_assoc])
    (fun t => by
      have := (m3bExp_holds r X la P hP ξ hξ x hx _ (hdom _ (him t))).mul_left κ
      refine this.congr_fun fun ν => ?_
      rw [mul_assoc]
      by_cases hν : X.fj la ξ ν P x = 0
      · simp [hν]
      · congr 2
        rw [← Complex.exp_int_mul]
        congr 1
        have h2 : ((n ν : ℤ) : ℂ) = 2 * ∑ τ, (ν τ : ℂ) * sb τ := by
          have := congrArg (fun z : ℝ => (z : ℂ)) (hnν ν hν)
          push_cast at this
          exact this.symm
        have h3 : ∑ τ, (ν τ : ℂ) * (((t : ℂ) + y * I) * sb τ) =
            ((t : ℂ) + y * I) * ∑ τ, (ν τ : ℂ) * sb τ := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun τ _ => by ring
        rw [h2, h3]; ring) j
  have e1 := (hasSum_subtype_iff_indicator (s := {ν | n ν = j})
    (f := fun ν => κ * X.fj la ξ ν P x)).mp H
  refine (hasSum_subtype_iff_indicator (s := {ν : X.Ψ → ℝ | 2 * ∑ τ, ν τ * sb τ = j})
    (f := fun ν => κ * X.fj la ξ ν P x)).mpr ?_
  convert e1 using 1
  funext ν
  by_cases hν : X.fj la ξ ν P x = 0
  · simp [Set.indicator_apply, hν]
  · have : (2 * ∑ τ, ν τ * sb τ = j) ↔ n ν = j := by
      rw [hnν ν hν]; exact Int.cast_inj
    simp only [Set.indicator_apply, Set.mem_ofPred_eq, this]

theorem hasSum_fj (X : Data E r) {la : Wt X.Ψ r} {P : Frame X.Ψ r → ℂ}
    (hP : X.IsSec la P) {ξ : Fin r → E} (hξ : X.IsIso ξ) {x : Frame X.Ψ r} (hx : x ∈ X.dom)
    (sb : X.Ψ → ℝ) (hsb : ∀ τ, 0 ≤ sb τ)
    (hint : ∀ ν : X.Ψ → ℝ, X.fj la ξ ν P x ≠ 0 → ∃ k : ℤ, 2 * ∑ τ, ν τ * sb τ = k)
    (κ u₁ : ℂ) (a : ℤ → ℂ) (T : ℝ)
    (ha : ∀ w : ℂ, T < w.im → HasSum (fun n : ℤ => a n * (u₁ * cexp (2 * Real.pi * I * w)) ^ n)
      (κ * P (X.flow ξ (fun τ => w * sb τ) x))) (j : ℤ) :
    HasSum (fun ν : {ν : X.Ψ → ℝ // 2 * ∑ τ, ν τ * sb τ = j} => κ * X.fj la ξ ν P x)
      (a j * u₁ ^ j) := by
  refine hasSum_fj_of_line X hP hξ hx sb hint κ u₁ a (max T 0 + 1) (fun w hw => ?_)
    (fun w hw => ha w (by rw [hw]; linarith [le_max_left T 0])) j
  refine flow_mem_dom_of_im_nonneg X hξ hx _ fun τ => ?_
  simp only [mul_im, ofReal_re, ofReal_im, mul_zero, zero_add, hw]
  exact mul_nonneg (by linarith [le_max_right T 0]) (hsb τ)

theorem coeff_mul_zpow_eq_mul_fj (X : Data E r) {la : Wt X.Ψ r} {P : Frame X.Ψ r → ℂ}
    (hP : X.IsSec la P) {ξ : Fin r → E} (hξ : X.IsIso ξ) {x : Frame X.Ψ r} (hx : x ∈ X.dom)
    (sb : X.Ψ → ℝ) (hsb : ∀ τ, 0 ≤ sb τ) (ν₀ : X.Ψ → ℝ) (j : ℤ)
    (hj : 2 * ∑ τ, ν₀ τ * sb τ = j)
    (huniq : ∀ ν : X.Ψ → ℝ, X.fj la ξ ν P x ≠ 0 → 2 * ∑ τ, ν τ * sb τ = j → ν = ν₀)
    (hint : ∀ ν : X.Ψ → ℝ, X.fj la ξ ν P x ≠ 0 → ∃ k : ℤ, 2 * ∑ τ, ν τ * sb τ = k)
    (κ u₁ : ℂ) (a : ℤ → ℂ) (T : ℝ)
    (ha : ∀ w : ℂ, T < w.im → HasSum (fun n : ℤ => a n * (u₁ * cexp (2 * Real.pi * I * w)) ^ n)
      (κ * P (X.flow ξ (fun τ => w * sb τ) x))) :
    a j * u₁ ^ j = κ * X.fj la ξ ν₀ P x := by
  refine (hasSum_fj X hP hξ hx sb hsb hint κ u₁ a T ha j).unique ?_
  refine hasSum_single (f := fun ν : {ν : X.Ψ → ℝ // 2 * ∑ τ, ν τ * sb τ = j} =>
    κ * X.fj la ξ ν P x) ⟨ν₀, hj⟩ fun ν hν => ?_
  by_cases h0 : X.fj la ξ ν P x = 0
  · simp [h0]
  · exact absurd (Subtype.ext (huniq ν h0 ν.2)) hν

end

end GlobalTheory.LaurentFJ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.EqOfDominantGeometricPointsOfUnramified
section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out

attribute [local instance] Over.cartesianMonoidalCategory

universe u

namespace GlobalTheory

theorem exists_point_over_dominant_geometric_point {U S : Scheme.{u}} (g : U ⟶ S)
    [UniversallyOpen g] [LocallyOfFiniteType g] [Nonempty U] {F : Type u} [Field F]
    [IsAlgClosed F] (t : Spec (.of F) ⟶ S) [IsDominant t] :
    ∃ j : Spec (.of F) ⟶ U, j ≫ g = t := by
  obtain ⟨z, u, hu⟩ := t.denseRange.exists_mem_open g.isOpenMap.isOpen_range
    (Set.range_nonempty _)
  obtain ⟨w, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := g) (g := t) u z hu
  have : JacobsonSpace ↥(pullback g t) := LocallyOfFiniteType.jacobsonSpace (pullback.snd g t)
  obtain ⟨c, -, hc⟩ := nonempty_inter_closedPoints (Z := (Set.univ : Set ↥(pullback g t)))
    ⟨w, trivial⟩ isOpen_univ.isLocallyClosed
  replace hc : IsClosed {c} := hc
  refine ⟨pointOfClosedPoint (pullback.snd g t) c hc ≫ pullback.fst g t, ?_⟩
  rw [Category.assoc, pullback.condition, pointOfClosedPoint_comp_assoc]

theorem eq_of_dominant_geometric_points_of_unramified {X S T : Scheme.{u}} (f : X ⟶ S)
    [FormallyUnramified f] [LocallyOfFiniteType f] [IsSeparated f] (g : T ⟶ S)
    [UniversallyOpen g] [LocallyOfFiniteType g] {a b : T ⟶ X} (ha : a ≫ f = g) (hb : b ≫ f = g)
    {F : Type u} [Field F] [IsAlgClosed F] (t : Spec (.of F) ⟶ S) [IsDominant t]
    (h : ∀ j : Spec (.of F) ⟶ T, j ≫ g = t → j ≫ a = j ≫ b) : a = b := by
  have hab : a ≫ f = b ≫ f := ha.trans hb.symm
  have := isClosedImmersion_equalizer_ι_of_isSeparated f hab
  refine eq_of_range_equalizer_ι_eq_univ f hab ?_
  by_contra hne
  let U : T.Opens := ⟨(Set.range (equalizer.ι a b))ᶜ,
    (equalizer.ι a b).isClosedEmbedding.isClosed_range.isOpen_compl⟩
  obtain ⟨y, hy⟩ := Set.nonempty_compl.mpr hne
  have : Nonempty U.toScheme := ⟨⟨y, hy⟩⟩
  obtain ⟨j, hj⟩ := exists_point_over_dominant_geometric_point (U.ι ≫ g) t
  have h1 := range_subset_range_equalizer_ι (j ≫ U.ι) (h _ (by simpa using hj))
  obtain ⟨p⟩ : Nonempty (Spec (CommRingCat.of F)) := inferInstance
  have h2 : (j ≫ U.ι) p ∈ U := by
    rw [Scheme.Hom.comp_apply]
    exact (j p).2
  exact h2 (h1 ⟨_, rfl⟩)

theorem fix_torsion_of_fix_geometric_of_etale {S : Scheme.{0}} (A : Over S) [GrpObj A] (M : ℕ)
    [Etale (mulA A M).left] [IsSeparated (mulA A M).left]
    {F : Type} [Field F] [IsAlgClosed F] (t : Spec (.of F) ⟶ S) [IsDominant t]
    (s : A ⟶ A) [IsMonHom s]
    (hs : ∀ x : Over.mk t ⟶ A, x ^ M = 1 → x ≫ s = x)
    (T : Over S) (x : T ⟶ A) (hx : x ^ M = 1) : x ≫ s = x := by
  have hmul : ∀ {Z : Over S} (y : Z ⟶ A), y ≫ mulA A M = y ^ M := fun y => by
    rw [mulA, MonObj.comp_pow, Category.comp_id]
  have hone : ∀ {Z : Over S}, (1 : Z ⟶ A).left = Z.hom ≫ η[A].left := fun {Z} => by
    rw [Hom.one_def, Over.comp_left]; rfl
  let K : Over S := Over.mk (pullback.snd (mulA A M).left η[A].left)
  have hη : η[A].left ≫ A.hom = 𝟙 S := Over.w η[A]
  let i : K ⟶ A := Over.homMk (pullback.fst (mulA A M).left η[A].left) (by
    change pullback.fst (mulA A M).left η[A].left ≫ A.hom = pullback.snd (mulA A M).left η[A].left
    rw [← Over.w (mulA A M), pullback.condition_assoc]
    erw [hη]
    exact Category.comp_id _)
  have hi : i ^ M = 1 := by
    rw [← hmul]
    apply Over.OverMorphism.ext
    rw [hone]
    exact pullback.condition
  have hlift : ∀ {Z : Over S} (y : Z ⟶ A), y ^ M = 1 → ∃ l : Z ⟶ K, l ≫ i = y := by
    intro Z y hy
    have e : y.left ≫ (mulA A M).left = Z.hom ≫ η[A].left := by
      rw [← Over.comp_left, hmul, hy, hone]
    exact ⟨Over.homMk (pullback.lift _ _ e) (pullback.lift_snd _ _ _),
      Over.OverMorphism.ext (pullback.lift_fst _ _ _)⟩
  have hmono : ∀ {Z : Over S} (l l' : Z ⟶ K), l ≫ i = l' ≫ i → l = l' := by
    intro Z l l' e
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · exact congr(($e).left)
    · exact (Over.w l).trans (Over.w l').symm
  obtain ⟨σ, hσ⟩ := hlift (i ≫ s) (by rw [← MonObj.pow_comp, hi, MonObj.one_comp])
  have hEt : Etale K.hom := inferInstanceAs (Etale (pullback.snd (mulA A M).left η[A].left))
  have hSep : IsSeparated K.hom :=
    inferInstanceAs (IsSeparated (pullback.snd (mulA A M).left η[A].left))
  have key : σ = 𝟙 K := by
    apply Over.OverMorphism.ext
    refine eq_of_dominant_geometric_points_of_unramified K.hom K.hom (Over.w σ) (Over.w (𝟙 K)) t ?_
    intro j hj
    let j' : Over.mk t ⟶ K := Over.homMk j hj
    have : j' ≫ σ = j' ≫ 𝟙 K := by
      apply hmono
      rw [Category.assoc, hσ, Category.comp_id, ← Category.assoc]
      exact hs _ (by rw [← MonObj.comp_pow, hi, MonObj.comp_one])
    exact congr(($this).left)
  obtain ⟨l, rfl⟩ := hlift x hx
  rw [Category.assoc, ← hσ, key, Category.id_comp]

theorem fix_torsion_of_fix_geometric_of_isDominant (hmul : MulNSt) {S : Scheme.{0}}
    [IsLocallyNoetherian S] (P : PolAV S) (M : ℕ) (hM : 1 ≤ M) (hMu : IsUnit (M : Γ(S, ⊤)))
    {F : Type} [Field F] [IsAlgClosed F] (t : Spec (.of F) ⟶ S) [IsDominant t]
    (s : P.A ⟶ P.A) (hsm : IsMonHom s)
    (hs : ∀ x : Over.mk t ⟶ P.A, x ^ M = 1 → x ≫ s = x)
    (T : Over S) (x : T ⟶ P.A) (hx : x ^ M = 1) : x ≫ s = x := by
  obtain ⟨hfin, -, -, het, -⟩ := hmul S P M hM
  have := het hMu
  exact fix_torsion_of_fix_geometric_of_etale P.A M t s hs T x hx

end GlobalTheory
end

