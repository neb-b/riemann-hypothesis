module

public import Mathlib
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0023
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0025
public import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.ComplexMinusRealLineMeasureCoordinates
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0001
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0047
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0046

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsFun
section
private theorem UpperTheory.Reformulated.B.Gr28.exists_fun
    {G W : Type} [Group G] [AddCommGroup W] [_root_.Module ℂ W]
    (H K : Subgroup G) (σ : Representation ℂ (↥H) W) (w : W)
    (hw : ∀ h : H, (h : G) ∈ K → σ h w = w) :
    ∃ f : G → W, f 1 = w ∧ (∀ (h : H) (g : G), f (h * g) = σ h (f g)) ∧
      ∀ k ∈ K, ∀ g, f (g * k) = f g := by
  classical
  let f : G → W := fun g => if hg : ∃ h : H, (h : G)⁻¹ * g ∈ K then σ hg.choose w else 0
  have pos : ∀ (g : G) (h : H), (h : G)⁻¹ * g ∈ K → f g = σ h w := by
    intro g h hh
    have hg : ∃ h : H, (h : G)⁻¹ * g ∈ K := ⟨h, hh⟩
    have h1 := hg.choose_spec
    have h2 : ((h⁻¹ * hg.choose : H) : G) ∈ K := by
      have := K.mul_mem hh (K.inv_mem h1)
      simpa [mul_assoc] using this
    have h3 := hw _ h2
    have h4 : f g = σ hg.choose w := dif_pos hg
    rw [h4]
    conv_rhs => rw [← h3]
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]
  have neg : ∀ g : G, (¬ ∃ h : H, (h : G)⁻¹ * g ∈ K) → f g = 0 := fun g hg => dif_neg hg
  refine ⟨f, ?_, ?_, ?_⟩
  · rw [pos 1 1 (by simp)]
    simp
  · intro h g
    by_cases hg : ∃ h : H, (h : G)⁻¹ * g ∈ K
    · obtain ⟨a, ha⟩ := hg
      rw [pos g a ha, pos (h * g) (h * a) (by simpa [mul_assoc] using ha), map_mul,
        Module.End.mul_apply]
    · rw [neg g hg, map_zero]
      refine neg _ ?_
      rintro ⟨a, ha⟩
      exact hg ⟨h⁻¹ * a, by simpa [mul_assoc] using ha⟩
  · intro k hk g
    by_cases hg : ∃ h : H, (h : G)⁻¹ * g ∈ K
    · obtain ⟨a, ha⟩ := hg
      rw [pos g a ha, pos (g * k) a (by rw [← mul_assoc]; exact K.mul_mem ha hk)]
    · rw [neg g hg]
      refine neg _ ?_
      rintro ⟨a, ha⟩
      refine hg ⟨a, ?_⟩
      have := K.mul_mem ha (K.inv_mem hk)
      simpa [mul_assoc] using this

theorem UpperTheory.Reformulated.B.Gr28.indVec :
    ∀ {G W : Type} [inst : Group G] [inst_1 : TopologicalSpace G] [inst_2 : IsTopologicalGroup G] [inst_3 : AddCommGroup W]
      [inst_4 : _root_.Module ℂ W] (H K : Subgroup G) (σ : Representation ℂ (↥H) W),
      IsOpen (↑K : Set G) →
        ∀ (w : W),
          (∀ (h : ↥H), (↑h : G) ∈ K → ((σ : ↥H → W →ₗ[ℂ] W) h : W → W) w = w) →
            ∃ (f : ↥(GlobalTheory.PRep.smoothPart (GlobalTheory.PRep.ind H σ))),
              (↑(↑f : ↥(GlobalTheory.PRep.indSpace H σ)) : G → W) (1 : G) = w ∧ f ∈ UpperTheory.Reformulated.B.SubgroupFixedSubmodule.fixd (GlobalTheory.PRep.smInd H σ) K := by
  intro G W _ _ _ _ _ H K σ hK w hw
  obtain ⟨f, h1, h2, h3⟩ := UpperTheory.Reformulated.B.Gr28.exists_fun H K σ w hw
  let F : GlobalTheory.PRep.indSpace H σ := ⟨f, h2⟩
  have hF : ∀ k ∈ K, GlobalTheory.PRep.ind H σ k F = F := by
    intro k hk
    apply Subtype.ext
    funext g
    exact h3 k hk g
  have hs : F ∈ GlobalTheory.PRep.smoothPart (GlobalTheory.PRep.ind H σ) := by
    let T : Subgroup G :=
      { carrier := {g | GlobalTheory.PRep.ind H σ g F = F}
        mul_mem' := by
          intro x y hx hy
          simp only [Set.mem_setOf_eq, map_mul, Module.End.mul_apply] at *
          rw [hy, hx]
        one_mem' := by simp
        inv_mem' := by
          intro x hx
          simp only [Set.mem_setOf_eq] at *
          conv_lhs => rw [← hx]
          rw [← Module.End.mul_apply, ← map_mul]
          simp }
    exact Subgroup.isOpen_mono (H₁ := K) (H₂ := T) hF hK
  refine ⟨⟨F, hs⟩, h1, ?_⟩
  intro k hk
  exact Subtype.ext (hF k hk)
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FiniteOfApprox
section
open IsLocalRing Polynomial

namespace UpperTheory.Reformulated.B.Ra2

private lemma split_low {O : Type} [CommRing O] (ϖ : O) (n : ℕ) :
    ∀ Q : O[X], (∀ i < n, ϖ ∣ Q.coeff i) →
      ∃ A B : O[X], Q = C ϖ * A + X ^ n * B ∧ B.coeff 0 = Q.coeff n := by
  induction n with
  | zero => intro Q _; exact ⟨0, Q, by simp, rfl⟩
  | succ n ih =>
    intro Q hQ
    obtain ⟨c, hc⟩ := hQ 0 (Nat.succ_pos n)
    obtain ⟨A, B, hAB, hB⟩ := ih Q.divX (fun i hi => by
      rw [coeff_divX]; exact hQ _ (Nat.succ_lt_succ hi))
    refine ⟨A * X + C c, B, ?_, by rw [hB, coeff_divX]⟩
    conv_lhs => rw [← divX_mul_X_add Q, hAB, hc]
    simp only [C_mul]
    ring

private lemma pow_mem_of_alg {O R : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [CommRing R] [IsDomain R] [IsLocalRing R] [Algebra O R] [IsLocalHom (algebraMap O R)]
    (hinj : Function.Injective (algebraMap O R)) {ϖ : O} (hϖ : Irreducible ϖ)
    {x : R} (hx : x ∈ maximalIdeal R) {P : O[X]} (hP : P ≠ 0) (hPx : aeval x P = 0) :
    ∃ n, x ^ n ∈ Ideal.span {algebraMap O R ϖ} := by
  classical
  have hp0 : algebraMap O R ϖ ≠ 0 := fun h =>
    hϖ.ne_zero (hinj (by rw [h, map_zero]))
  have hfin : FiniteMultiplicity (C ϖ) P :=
    FiniteMultiplicity.of_not_isUnit (fun h => hϖ.not_isUnit (Polynomial.isUnit_C.mp h)) hP
  obtain ⟨Q, hPQ, hQ⟩ := hfin.exists_eq_pow_mul_and_not_dvd
  have hQx : aeval x Q = 0 := by
    rw [hPQ, map_mul, map_pow, aeval_C] at hPx
    exact (mul_eq_zero.mp hPx).resolve_left (pow_ne_zero _ hp0)
  have hex : ∃ i, ¬ ϖ ∣ Q.coeff i := by
    by_contra hcon
    push_neg at hcon
    exact hQ ((Polynomial.C_dvd_iff_dvd_coeff _ _).mpr hcon)
  have hn : ¬ ϖ ∣ Q.coeff (Nat.find hex) := Nat.find_spec hex
  have hlow : ∀ i < Nat.find hex, ϖ ∣ Q.coeff i := fun i hi =>
    not_not.mp (Nat.find_min hex hi)
  obtain ⟨A, B, hAB, hB⟩ := split_low ϖ _ Q hlow
  have hu : IsUnit (B.coeff 0) := by
    by_contra hcon
    have h1 : B.coeff 0 ∈ maximalIdeal O := hcon
    rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton, hB] at h1
    exact hn h1
  have hBu : IsUnit (aeval x B) := by
    by_contra hcon
    have h1 : aeval x B ∈ maximalIdeal R := hcon
    have h2 : aeval x B = aeval x B.divX * x + algebraMap O R (B.coeff 0) := by
      conv_lhs => rw [← divX_mul_X_add B]
      simp
    have h3 : algebraMap O R (B.coeff 0) ∈ maximalIdeal R := by
      have := Ideal.sub_mem _ h1 (Ideal.mul_mem_left _ (aeval x B.divX) hx)
      rwa [h2, add_sub_cancel_left] at this
    exact h3 (hu.map _)
  refine ⟨Nat.find hex, ?_⟩
  rw [← Ideal.mul_unit_mem_iff_mem _ hBu]
  have h0 : algebraMap O R ϖ * aeval x A + x ^ Nat.find hex * aeval x B = 0 := by
    have := hQx
    rw [hAB] at this
    simpa using this
  rw [eq_neg_of_add_eq_zero_right h0]
  exact neg_mem (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))

private lemma approx_ideal {O R : Type} [CommRing O] [IsLocalRing O] [CommRing R] [Algebra O R]
    [UpperTheory.V.Alg.IsCO O R] (I : Ideal R) :
    ∃ M : Submodule O R, M.FG ∧ ∀ z ∈ I, ∃ w ∈ M, z - w ∈ maximalIdeal R * I := by
  obtain ⟨s, hs⟩ : I.FG := IsNoetherian.noetherian I
  subst hs
  refine ⟨Submodule.span O s, Submodule.fg_span s.finite_toSet, fun z hz => ?_⟩
  induction hz using Submodule.span_induction with
  | mem y hy => exact ⟨y, Submodule.subset_span hy, by simp⟩
  | zero => exact ⟨0, zero_mem _, by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨u, hu, hu'⟩ := ha
    obtain ⟨v, hv, hv'⟩ := hb
    refine ⟨u + v, add_mem hu hv, ?_⟩
    have := add_mem hu' hv'
    convert this using 1
    ring
  | smul r a ha' ha =>
    obtain ⟨u, hu, hu'⟩ := ha
    obtain ⟨c, hc⟩ := UpperTheory.V.Alg.IsCO.res_surj (O := O) r
    refine ⟨c • u, Submodule.smul_mem _ _ hu, ?_⟩
    have h1 : (r - algebraMap O R c) * a ∈ maximalIdeal R * Ideal.span (s : Set R) :=
      Ideal.mul_mem_mul hc ha'
    have h2 := Ideal.mul_mem_left _ (algebraMap O R c) hu'
    convert add_mem h1 h2 using 1
    rw [smul_eq_mul, Algebra.smul_def]
    ring

private lemma approx_pow {O R : Type} [CommRing O] [IsLocalRing O] [CommRing R] [Algebra O R]
    [UpperTheory.V.Alg.IsCO O R] (N : ℕ) :
    ∃ M : Submodule O R, M.FG ∧ ∀ z : R, ∃ w ∈ M, z - w ∈ maximalIdeal R ^ N := by
  induction N with
  | zero => exact ⟨⊥, Submodule.fg_bot, fun z => ⟨0, zero_mem _, by simp⟩⟩
  | succ N ih =>
    obtain ⟨M, hM, h⟩ := ih
    obtain ⟨M', hM', h'⟩ := approx_ideal (O := O) (maximalIdeal R ^ N)
    refine ⟨M ⊔ M', hM.sup hM', fun z => ?_⟩
    obtain ⟨w, hw, hzw⟩ := h z
    obtain ⟨w', hw', hzw'⟩ := h' _ hzw
    refine ⟨w + w', add_mem (Submodule.mem_sup_left hw) (Submodule.mem_sup_right hw'), ?_⟩
    rw [pow_succ', ← sub_sub]
    exact hzw'

private lemma finite_of_approx {O R : Type} [CommRing O] [IsLocalRing O]
    [IsAdicComplete (maximalIdeal O) O] [CommRing R] [IsLocalRing R] [Algebra O R]
    [IsLocalHom (algebraMap O R)] [IsHausdorff (maximalIdeal R) R]
    {ϖ : O} (hϖ : maximalIdeal O = Ideal.span {ϖ}) {M : Submodule O R} (hM : M.FG)
    (h : ∀ z : R, ∃ w ∈ M, z - w ∈ Ideal.span {algebraMap O R ϖ}) : Module.Finite O R := by
  obtain ⟨s, g, hg⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hM
  have hϖI : ϖ ∈ maximalIdeal O := hϖ ▸ Ideal.mem_span_singleton_self ϖ
  let G : (Fin s → O) →ₗ[O] R := Fintype.linearCombination O g
  have hstep : ∀ y : R, ∃ (c : Fin s → O) (y' : R), y = G c + algebraMap O R ϖ * y' := by
    intro y
    obtain ⟨w, hw, hyw⟩ := h y
    rw [← hg, ← Fintype.range_linearCombination] at hw
    obtain ⟨c, rfl⟩ := hw
    obtain ⟨y', hy'⟩ := Ideal.mem_span_singleton'.mp hyw
    exact ⟨c, y', by rw [mul_comm, hy']; ring⟩
  choose φ ψ hφ using hstep
  have hmap : ∀ (n : ℕ) (a : O), a ∈ maximalIdeal O ^ n →
      algebraMap O R a ∈ maximalIdeal R ^ n := by
    intro n a ha
    have hle : maximalIdeal O ≤ (maximalIdeal R).comap (algebraMap O R) := fun b hb =>
      fun hu => hb (IsLocalHom.map_nonunit b hu)
    exact Ideal.le_comap_pow _ n (Ideal.pow_right_mono hle n ha)
  refine Module.Finite.of_surjective G fun z => ?_
  let y : ℕ → R := fun k => ψ^[k] z
  let S : ℕ → Fin s → O := fun n j => ∑ k ∈ Finset.range n, ϖ ^ k * φ (y k) j
  have hSsucc : ∀ n, S (n + 1) = S n + ϖ ^ n • φ (y n) := by
    intro n
    funext j
    simp [S, Finset.sum_range_succ]
  have hS : ∀ n, z = G (S n) + algebraMap O R ϖ ^ n * y n := by
    intro n
    induction n with
    | zero =>
      have h0 : S 0 = 0 := by
        funext j
        simp [S]
      simp [h0, y]
    | succ n ih =>
      have hy : y (n + 1) = ψ (y n) := Function.iterate_succ_apply' ψ n z
      rw [hSsucc, map_add (f := _), map_smul, hy, Algebra.smul_def, map_pow]
      conv_lhs => rw [ih, hφ (y n)]
      ring
  have hcauchy : ∀ j, ∀ {m n : ℕ}, m ≤ n →
      S m j ≡ S n j [SMOD (maximalIdeal O ^ m • ⊤ : Submodule O O)] := by
    intro j m n hmn
    induction n, hmn using Nat.le_induction with
    | base => exact SModEq.refl _
    | succ n hmn ih =>
      refine ih.trans ?_
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, hSsucc]
      have : S n j - (S n + ϖ ^ n • φ (y n)) j = -(ϖ ^ n * φ (y n) j) := by
        simp
      rw [this]
      exact neg_mem (Ideal.mul_mem_right _ _
        (Ideal.pow_le_pow_right hmn (Ideal.pow_mem_pow hϖI n)))
  have hL : ∀ j, ∃ L : O, ∀ n, S n j ≡ L [SMOD (maximalIdeal O ^ n • ⊤ : Submodule O O)] :=
    fun j => IsPrecomplete.prec' _ (hcauchy j)
  choose L hL using hL
  refine ⟨L, ?_⟩
  refine (IsHausdorff.eq_iff_smodEq (I := maximalIdeal R)).mpr fun n => ?_
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
  have hd : G L - z = G (L - S n) - algebraMap O R ϖ ^ n * y n := by
    conv_lhs => rw [hS n]
    rw [map_sub]
    ring
  rw [hd]
  refine sub_mem ?_ (Ideal.mul_mem_right _ _ ?_)
  · have hG : G (L - S n) = ∑ j, (L - S n) j • g j := Fintype.linearCombination_apply O g _
    rw [hG]
    refine Ideal.sum_mem _ fun j _ => ?_
    rw [Algebra.smul_def]
    refine Ideal.mul_mem_right _ _ (hmap n _ ?_)
    have h1 := (hL j n).symm
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at h1
    exact h1
  · rw [← map_pow]
    exact hmap n _ (Ideal.pow_mem_pow hϖI n)

end UpperTheory.Reformulated.B.Ra2

open UpperTheory.Reformulated.B.Ra2 in
theorem UpperTheory.Reformulated.B.Ra2.finite_of_alg :
    ∀ {O R : Type} [inst : CommRing O] [inst_1 : IsDomain O] [inst_2 : IsDiscreteValuationRing O]
      [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [inst_4 : CommRing R] [IsDomain R] [inst_6 : Algebra O R]
      [UpperTheory.V.Alg.IsCO O R],
      Function.Injective (⇑(Algebra.algebraMap O R) : O → R) →
        (∀ (a : R), ∃ (P : Polynomial O), P ≠ (0 : Polynomial O) ∧ (Polynomial.aeval a : Polynomial O → R) P = (0 : R)) →
          Module.Finite O R := by
  intro O R _ _ _ _ _ _ _ _ hinj halg
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hrad : maximalIdeal R ≤ (Ideal.span {algebraMap O R ϖ}).radical := fun x hx => by
    obtain ⟨P, hP, hPx⟩ := halg x
    exact pow_mem_of_alg hinj hϖ hx hP hPx
  obtain ⟨N, hN⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad (IsNoetherian.noetherian _)
  obtain ⟨M, hM, h⟩ := approx_pow (O := O) (R := R) N
  exact finite_of_approx hϖ.maximalIdeal_eq hM fun z => by
    obtain ⟨w, hw, hzw⟩ := h z
    exact ⟨w, hw, hN hzw⟩
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.GLRealOpen
section
theorem UpperTheory.Reformulated.B.GLRealOpen.glR_open :
    ∀ {K : Type} [inst : CommRing K] [inst_1 : TopologicalSpace K] [IsTopologicalRing K] (R : Subring K),
      IsOpen (↑R : Set K) → ∀ (n : ℕ), IsOpen (↑(UpperTheory.Reformulated.B.GeneralLinearGroupOverSubring.glR R n) : Set (GL (Fin n) K)) := by
  intro K _ _ _ R hR n
  have hM : IsOpen {M : Matrix (Fin n) (Fin n) K | ∀ i j, M i j ∈ R} := by
    have e : {M : Matrix (Fin n) (Fin n) K | ∀ i j, M i j ∈ R}
        = ⋂ i, ⋂ j, (fun M : Matrix (Fin n) (Fin n) K => M i j) ⁻¹' (R : Set K) := by
      ext M
      simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]
    rw [e]
    refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
    exact hR.preimage (continuous_id.matrix_elem i j)
  have h1 : Continuous fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K) :=
    Units.continuous_val
  have h2 : Continuous fun g : GL (Fin n) K => ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
    Units.continuous_coe_inv
  exact (hM.preimage h1).inter (hM.preimage h2)
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsMoreBis
section
theorem UpperTheory.Reformulated.B.Qf46.cover :
    ∀ {G Y : Type} [inst : Group G] [Countable G] [inst_2 : MeasurableSpace Y] [inst_3 : MulAction G Y]
      (μ : MeasureTheory.Measure Y),
      UpperTheory.Esk.Pres G μ →
        ∀ (b : Y → ℝ),
          UpperTheory.Esk.IsCut G b →
            ∀ (S : Set Y),
              MeasurableSet S →
                (∀ (y : Y), ∃ (g : G), g • y ∈ S) → ∫⁻ (y : Y), ENNReal.ofReal (b y) ∂μ ≤ (μ : Set Y → ENNReal) S := by
  intro G Y _ _ _ _ μ hP b hb S hS hc
  have hB : Measurable fun y => ENNReal.ofReal (b y) := hb.meas.ennreal_ofReal
  have hF : ∀ g : G, Measurable (S.indicator fun y => ENNReal.ofReal (b (g⁻¹ • y))) :=
    fun g => (hB.comp (hP g⁻¹).measurable).indicator hS
  have hone : ∀ y, ∑' g : G, ENNReal.ofReal (b (g⁻¹ • y)) = 1 := by
    intro y
    have h : ∑' g : G, ENNReal.ofReal (b (g⁻¹ • y)) = ∑' g : G, ENNReal.ofReal (b (g • y)) :=
      (Equiv.inv G).tsum_eq (fun g : G => ENNReal.ofReal (b (g • y)))
    rw [h, ← ENNReal.ofReal_tsum_of_nonneg (fun g => hb.nonneg _) (hb.sum y).summable, (hb.sum y).tsum_eq,
      ENNReal.ofReal_one]
  calc ∫⁻ y, ENNReal.ofReal (b y) ∂μ
      ≤ ∫⁻ y, ∑' g : G, S.indicator (fun y => ENNReal.ofReal (b (g⁻¹ • y))) (g • y) ∂μ := by
        refine MeasureTheory.lintegral_mono fun y => ?_
        obtain ⟨g, hg⟩ := hc y
        refine le_trans ?_ (ENNReal.le_tsum g)
        rw [Set.indicator_of_mem hg, inv_smul_smul]
    _ = ∑' g : G, ∫⁻ y, S.indicator (fun y => ENNReal.ofReal (b (g⁻¹ • y))) (g • y) ∂μ :=
        MeasureTheory.lintegral_tsum fun g => ((hF g).comp (hP g).measurable).aemeasurable
    _ = ∑' g : G, ∫⁻ y, S.indicator (fun y => ENNReal.ofReal (b (g⁻¹ • y))) y ∂μ :=
        tsum_congr fun g => (hP g).lintegral_comp (hF g)
    _ = ∫⁻ y, ∑' g : G, S.indicator (fun y => ENNReal.ofReal (b (g⁻¹ • y))) y ∂μ :=
        (MeasureTheory.lintegral_tsum fun g => (hF g).aemeasurable).symm
    _ = ∫⁻ y, S.indicator 1 y ∂μ := by
        refine MeasureTheory.lintegral_congr fun y => ?_
        by_cases hy : y ∈ S
        · simp only [Set.indicator_of_mem hy, hone, Pi.one_apply]
        · simp only [Set.indicator_of_notMem hy, tsum_zero]
    _ = μ S := MeasureTheory.lintegral_indicator_one hS
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsTerFurther
section
theorem UpperTheory.Reformulated.B.Ga5b.exists_nat_smul_mem :
    ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E]
    [inst_2 : NumberField.IsCMField E] {N : ℕ} (X : ReciprocityTheory.ChartRestriction.G.FD.Data E N) (v : Fin N → E),
    ∃ (n : ℕ),
      (0 : ℕ) < n ∧
        (↑n : E) • v ∈
          X.Λ := by
  intro E _ _ _ N X v
  refine Submodule.span_induction (fun x hx => ⟨1, one_pos, by simpa using hx⟩) ⟨1, one_pos, by simp⟩
    ?_ ?_ (X.Λ_span ▸ Submodule.mem_top : v ∈ Submodule.span E (X.Λ : Set (Fin N → E)))
  · rintro x y - - ⟨a, ha, hx⟩ ⟨b, hb, hy⟩
    refine ⟨a * b, mul_pos ha hb, ?_⟩
    convert X.Λ.add_mem (nsmul_mem hx b) (nsmul_mem hy a) using 1
    ext i; simp; ring
  · rintro c x - ⟨a, ha, hx⟩
    obtain ⟨m, s, hm, hs⟩ := ((IsFractionRing.isAlgebraic_iff ℤ ℚ E).2
      (.of_finite ℚ c)).exists_nsmul_eq (NumberField.RingOfIntegers E)
    refine ⟨m * a, mul_pos (Nat.pos_of_ne_zero hm) ha, ?_⟩
    convert X.Λ.smul_mem s hx using 1
    rw [← algebraMap_smul E s, ← hs]; ext i; simp; ring
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LocalSituation
section
theorem UpperTheory.Reformulated.B.LocalSituation.exists_smul_mem :
    ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E] [inst_2 : NumberField.IsCMField E] {r : ℕ}
      (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (w : Fin r → E),
      ∃ (c : NumberField.RingOfIntegers E), c ≠ (0 : NumberField.RingOfIntegers E) ∧ c • w ∈ X.Λ := by
  intro E _ _ _ r X w
  have hw : w ∈ Submodule.span E (X.Λ : Set (Fin r → E)) := by
    rw [X.Λ_span]; exact Submodule.mem_top
  induction hw using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by rwa [one_smul]⟩
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact X.Λ.zero_mem⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨b, hb, hby⟩ := hy
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine X.Λ.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact X.Λ.smul_mem b hax
    · rw [mul_smul]; exact X.Λ.smul_mem a hby
  | smul t x _ hx =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := NumberField.RingOfIntegers E) t
    have hq0 : q ≠ 0 := nonZeroDivisors.ne_zero hq
    have hq1 : algebraMap (NumberField.RingOfIntegers E) E q ≠ 0 := by
      simpa using hq0
    refine ⟨a * q, mul_ne_zero ha hq0, ?_⟩
    have key : (a * q) • ((algebraMap (NumberField.RingOfIntegers E) E p /
        algebraMap (NumberField.RingOfIntegers E) E q) • x) = p • (a • x) := by
      ext i
      simp only [Pi.smul_apply]
      simp only [Algebra.smul_def, map_mul, Algebra.algebraMap_self, RingHom.id_apply]
      field_simp
    rw [key]
    exact X.Λ.smul_mem p hax
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MonicNormLtOne
section
theorem UpperTheory.Reformulated.B.MonicNormLtOne.mc_norm_lt :
    ∀ {l : ℕ} [inst : Fact (Nat.Prime l)] {R : Type}
    [inst_1 : CommRing R] [inst_2 : IsLocalRing R] [inst_3 : Algebra ℤ_[l] R] (y : R →ₐ[ℤ_[l]] PadicAlgCl l),
    ∀ a ∈ IsLocalRing.maximalIdeal R, ‖(y : R → PadicAlgCl l) a‖ < (1 : ℝ) := by
  intro l _ R _ _ _ y a ha
  exact UpperTheory.Reformulated.B.NormLtOne.norm_lt_one (O := ℤ_[l]) y a ha
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MulLinearAe
section
theorem UpperTheory.Reformulated.B.MulLinearAe.mulL_ae.{u_1} :
    ∀ {X : Type u_1} [inst : MeasurableSpace X] {ν : MeasureTheory.Measure X} (c : X → ℝ) (hc : Measurable c)
      (hb : ∀ (x : X), |c x| ≤ (1 : ℝ)) (f : ↥(MeasureTheory.Lp ℂ (2 : ENNReal) ν)),
      (↑(↑((UpperTheory.Reformulated.B.MultiplicationNormBound.mulL c hc hb : ↥(MeasureTheory.Lp ℂ (2 : ENNReal) ν) → ↥(MeasureTheory.Lp ℂ (2 : ENNReal) ν))
                        f) :
              X →ₘ[ν] ℂ) :
          X → ℂ) =ᵐ[ν]
        fun (x : X) ↦ (↑(c x) : ℂ) * (↑(↑f : X →ₘ[ν] ℂ) : X → ℂ) x := by
  intro X _ ν c hc hb f
  have h : MeasureTheory.MemLp (fun x : X => (c x : ℂ) * f x) 2 ν :=
    (MeasureTheory.Lp.memLp f).of_le
      ((Complex.measurable_ofReal.comp hc).aestronglyMeasurable.mul
        (MeasureTheory.Lp.aestronglyMeasurable f))
      (Filter.Eventually.of_forall fun x => by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_of_le_one_left (norm_nonneg _) (hb x))
  exact h.coeFn_toLp
end

