module

public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.SmoothSeminormAndSobolevBounds
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CompactHaarRightInvariantInst
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0112
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicitySpaceEqZeroOfLowestKTypes
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle0003

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.EigenOrthogonalForm
section
noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum MeasureTheory
open scoped InnerProductSpace ComplexConjugate

namespace PositivityTheory.CW

namespace BilinearFormCasimir

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Mx n → (H →L[ℂ] H)}

def tr (k : KG ε) (v : kfin ε σ) : kfin ε σ :=
  ⟨σ (toMK k⁻¹) v, isKFin_translate (mem_kfin.1 v.2) (toMK_mem_K _)⟩

theorem tr_add (k : KG ε) (v v' : kfin ε σ) : tr k (v + v') = tr k v + tr k v' :=
  Subtype.ext (map_add (σ (toMK k⁻¹)) (v : H) v')

theorem tr_smul (k : KG ε) (c : ℂ) (v : kfin ε σ) : tr k (c • v) = c • tr k v :=
  Subtype.ext (map_smul (σ (toMK k⁻¹)) c (v : H))

theorem continuous_tr (hU : IsURepOn (UJset ε) σ) (l : kfin ε σ →ₗ[ℂ] ℂ) (v : kfin ε σ) :
    Continuous fun k : KG ε => l (tr k v) := by
  obtain ⟨S, hSf, hvS, hSK⟩ := mem_kfin.1 v.2
  haveI := hSf
  have hSk : ∀ x ∈ S, x ∈ kfin ε σ := fun x hx => mem_kfin.2 ⟨S, hSf, hx, hSK⟩
  let ι : S →ₗ[ℂ] kfin ε σ :=
    { toFun := fun x => ⟨x, hSk x x.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hc : Continuous (l ∘ₗ ι) := LinearMap.continuous_of_finiteDimensional _
  have hmem : ∀ k : KG ε, σ (toMK k⁻¹) v ∈ S := fun k => hSK _ (toMK_mem_K _) _ hvS
  have h1 : Continuous fun k : KG ε => σ (toMK k⁻¹) (v : H) :=
    (hU.2.2 v).comp_continuous ((continuous_toMK ε).comp continuous_inv) fun k => K_le_UJ (toMK_mem_K _)
  have h2 : Continuous fun k : KG ε => (⟨σ (toMK k⁻¹) v, hmem k⟩ : S) := h1.subtype_mk _
  exact (hc.comp h2).congr fun k => rfl

def fm (l : kfin ε σ →ₗ[ℂ] ℂ) (v y : kfin ε σ) : ℂ := ∫ k, conj (l (tr k v)) * l (tr k y) ∂(muK ε)

theorem integrable_fm (hU : IsURepOn (UJset ε) σ) (l : kfin ε σ →ₗ[ℂ] ℂ) (v y : kfin ε σ) :
    Integrable (fun k : KG ε => conj (l (tr k v)) * l (tr k y)) (muK ε) := by
  haveI : CompactSpace (KG ε) := instCompactKG n ε
  have hc : Continuous fun k : KG ε => conj (l (tr k v)) * l (tr k y) :=
    ((continuous_tr hU l v).star).mul (continuous_tr hU l y)
  exact hc.integrable_of_hasCompactSupport (isClosed_tsupport _).isCompact

def bf (hU : IsURepOn (UJset ε) σ) (l : kfin ε σ →ₗ[ℂ] ℂ) : kfin ε σ →ₗ⋆[ℂ] kfin ε σ →ₗ[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (fm l)
    (fun v v' y => by
      unfold fm
      rw [← integral_add (integrable_fm hU l v y) (integrable_fm hU l v' y)]
      refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
      simp only [tr_add, map_add (f := _), add_mul])
    (fun c v y => by
      unfold fm
      rw [smul_eq_mul, ← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
      simp only [tr_smul, map_smul, smul_eq_mul, map_mul]
      ring)
    (fun v y y' => by
      unfold fm
      rw [← integral_add (integrable_fm hU l v y) (integrable_fm hU l v y')]
      refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
      simp only [tr_add, map_add (f := _), mul_add])
    (fun c v y => by
      unfold fm
      rw [RingHom.id_apply, smul_eq_mul, ← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
      simp only [tr_smul, map_smul, smul_eq_mul]
      ring)

theorem bf_apply (hU : IsURepOn (UJset ε) σ) (l : kfin ε σ →ₗ[ℂ] ℂ) (v y : kfin ε σ) :
    bf hU l v y = fm l v y := rfl

end BilinearFormCasimir

open BilinearFormCasimir in
theorem e2b : E2b := by
  intro n ε H _ _ _ σ hU hI Q hQ v₀ hv₀
  have hv0 : v₀ ≠ 0 := fun h => hv₀ (by rw [h, map_zero])

  let f0 : (ℂ ∙ v₀) →ₗ[ℂ] ℂ := (LinearPMap.mkSpanSingleton v₀ ((Q v₀ : ℝ) : ℂ) hv0).toFun
  have hf0 : ∀ x : (ℂ ∙ v₀), ‖f0 x‖ ≤ Q x := by
    rintro ⟨x, hx⟩
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hx
    have e : f0 ⟨c • v₀, hx⟩ = c • ((Q v₀ : ℝ) : ℂ) :=
      LinearPMap.mkSpanSingleton'_apply v₀ ((Q v₀ : ℝ) : ℂ) _ c hx
    rw [e, smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (apply_nonneg Q v₀)]
    exact (map_smul_eq_mul Q c v₀).symm.le
  obtain ⟨l, hl, hlQ⟩ := Module.Dual.exists_extension_of_le_seminorm (ℂ ∙ v₀) f0 hf0
  have hlv : l v₀ = ((Q v₀ : ℝ) : ℂ) := by
    have h1 : v₀ ∈ (ℂ ∙ v₀) := Submodule.mem_span_singleton_self v₀
    have h1' : (1 : ℂ) • v₀ ∈ (ℂ ∙ v₀) := by rw [one_smul]; exact h1
    rw [hl ⟨v₀, h1⟩]
    have e : f0 ⟨(1 : ℂ) • v₀, h1'⟩ = (1 : ℂ) • ((Q v₀ : ℝ) : ℂ) :=
      LinearPMap.mkSpanSingleton'_apply v₀ ((Q v₀ : ℝ) : ℂ) _ 1 h1'
    have e' : (⟨v₀, h1⟩ : (ℂ ∙ v₀)) = ⟨(1 : ℂ) • v₀, h1'⟩ := Subtype.ext (one_smul ℂ v₀).symm
    rw [e', e, one_smul]
  have hQtr : ∀ (k : KG ε) (v : kfin ε σ), Q (tr k v) = Q v := fun k v => hQ _ (toMK_mem_K _) v _ rfl
  refine ⟨bf hU l, fun k hk v y v' y' hv' hy' => ?_, fun v y => ?_, ?_⟩
  ·
    obtain ⟨k0, rfl⟩ : ∃ k0 : KG ε, toMK k0 = k := by rw [← range_toMK ε] at hk; exact hk
    have htr : ∀ (k : KG ε) (w w' : kfin ε σ), (w' : H) = σ (toMK k0) w → tr k w' = tr (k0⁻¹ * k) w := by
      intro k w w' hw
      apply Subtype.ext
      show σ (toMK k⁻¹) (w' : H) = σ (toMK (k0⁻¹ * k)⁻¹) w
      rw [hw, ← sigma_mul hU (K_le_UJ (toMK_mem_K _)) (K_le_UJ (toMK_mem_K _))]
      congr 2
    rw [bf_apply, bf_apply, fm, fm]
    simp only [htr _ _ _ hv', htr _ _ _ hy']
    exact integral_mul_left_eq_self (fun k => conj (l (tr k v)) * l (tr k y)) k0⁻¹
  · rw [bf_apply, fm]
    have h := norm_integral_le_of_norm_le_const (μ := muK ε) (f := fun k => conj (l (tr k v)) * l (tr k y))
      (C := Q v * Q y) (Filter.Eventually.of_forall fun k => by
        rw [norm_mul, RCLike.norm_conj, ← hQtr k v, ← hQtr k y]
        exact mul_le_mul (hlQ _) (hlQ _) (norm_nonneg _) (apply_nonneg _ _))
    simpa [measure_univ] using h
  · rw [bf_apply, fm]
    haveI : CompactSpace (KG ε) := instCompactKG n ε
    have e : ∀ k : KG ε, conj (l (tr k v₀)) * l (tr k v₀) = ((‖l (tr k v₀)‖ ^ 2 : ℝ) : ℂ) := fun k => by
      rw [mul_comm, Complex.mul_conj']
      push_cast
      ring
    simp only [e]
    rw [integral_complex_ofReal]
    have hpos : 0 < ∫ k, ‖l (tr k v₀)‖ ^ 2 ∂(muK ε) := by
      refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 1)
        ((continuous_tr hU l v₀).norm.pow 2) (isClosed_tsupport _).isCompact (fun k => by positivity) ?_
      have h1 : tr (1 : KG ε) v₀ = v₀ := Subtype.ext (by
        show σ (toMK (1 : KG ε)⁻¹) (v₀ : H) = v₀
        rw [inv_one]
        exact sigma_one hU _)
      rw [h1, hlv, Complex.norm_real, Real.norm_of_nonneg (apply_nonneg Q v₀)]
      exact pow_ne_zero 2 hv₀
    exact_mod_cast hpos.ne'

end PositivityTheory.CW

end
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.ExistsFunctional
section
noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum

namespace PositivityTheory.CW

namespace KInvarianceAlt

theorem kinv {n : ℕ} {ε : Fin n → Bool} {k : Mx n} (hk : k ∈ Kset ε) : ∃ k' ∈ Kset ε, k' * k = 1 := by
  obtain ⟨hu, hJ⟩ := hk
  have hu' : kᴴ * k = 1 := by
    have := Matrix.mem_unitaryGroup_iff'.1 hu; rwa [Matrix.star_eq_conjTranspose] at this
  have hJh : (Jm ε)ᴴ = Jm ε := by
    ext i j; simp only [Jm, diagonal_conjTranspose, diagonal_apply]; split_ifs <;> simp_all
  have hJ' : kᴴ * Jm ε = Jm ε * kᴴ := by
    have h := congrArg Matrix.conjTranspose hJ
    simp only [Matrix.conjTranspose_mul, hJh] at h
    exact h.symm
  have hs' : kᴴ ∈ Matrix.unitaryGroup (Fin n) ℂ := by
    have := Unitary.star_mem hu; rwa [Matrix.star_eq_conjTranspose] at this
  exact ⟨kᴴ, ⟨hs', hJ'⟩, hu'⟩

end KInvarianceAlt

theorem e1a : SmoothSeminormGrowth := by
  intro n ε H _ _ _ σ hU hI E _ _ _ _ _ _ p π dπ hπ i
  obtain ⟨q, N, hq, hg⟩ := hπ.growth i
  haveI : Nonempty (UJset ε) := ⟨⟨1, one_mem_UJ ε⟩⟩
  set W : Mx n → ℝ := fun g => (1 + hs g) ^ N with hWdef
  have hW : ∀ g, 0 < W g := fun g => pow_pos (by linarith [hs_nonneg g]) _
  have hWm : ∀ a b : Mx n, W (a * b) ≤ W a * W b := fun a b => by
    simp only [hWdef]
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by linarith [hs_nonneg (a * b)]) (one_add_hs_mul_le a b) N
  have hmul : ∀ a ∈ UJset ε, ∀ b ∈ UJset ε, ∀ x, π (a * b) x = π a (π b x) := fun a ha b hb x => by
    rw [hπ.map_mul a ha b hb]; rfl
  let f : UJset ε → Seminorm ℂ E := fun g => (Real.toNNReal (W g.1)⁻¹) • (p i).comp (π g.1 : E →ₗ[ℂ] E)
  have hf : ∀ g x, f g x = p i (π g.1 x) / W g.1 := fun g x => by
    show ((Real.toNNReal (W g.1)⁻¹ : NNReal) : ℝ) * p i (π g.1 x) = _
    rw [Real.coe_toNNReal _ (inv_nonneg.2 (hW _).le), div_eq_inv_mul]
  have hfq : ∀ g x, f g x ≤ q x := fun g x => by
    rw [hf, div_le_iff₀ (hW _), mul_comm]
    exact hg g.1 g.2 x
  have hbdd : BddAbove (Set.range f) := ⟨q, by
    rintro _ ⟨g, rfl⟩
    exact Pi.le_def.2 fun x => hfq g x⟩
  have hfb : ∀ x, BddAbove (Set.range fun g => f g x) := fun x => ⟨q x, by
    rintro _ ⟨g, rfl⟩
    exact hfq g x⟩
  set Q : Seminorm ℂ E := ⨆ g, f g with hQdef
  have hQ : ∀ x, Q x = ⨆ g, f g x := fun x => Seminorm.iSup_apply hbdd
  have hle : ∀ g x, f g x ≤ Q x := fun g x => by rw [hQ]; exact le_ciSup (hfb x) g
  have hQq : Q ≤ q := Pi.le_def.2 fun x => by rw [hQ]; exact ciSup_le fun g => hfq g x
  have h1 : ∀ g ∈ UJset ε, ∀ x, p i (π g x) ≤ W g * Q x := fun g hg x => by
    have := hle ⟨g, hg⟩ x
    rw [hf, div_le_iff₀ (hW _)] at this
    linarith
  have hKk : ∀ k ∈ Kset ε, ∀ x, Q (π k x) ≤ Q x := fun k hk x => by
    rw [hQ (π k x)]
    refine ciSup_le fun g => ?_
    have hgk : g.1 * k ∈ UJset ε := mul_mem_UJ g.2 (K_le_UJ hk)
    have := hle ⟨g.1 * k, hgk⟩ x
    rw [hf] at this ⊢
    have e : W (g.1 * k) = W g.1 := by
      simp only [hWdef, ((Formalism.REAL.hermitian_small_ball n ε).2 g.1 k hk).1]
    rw [← hmul g.1 g.2 k (K_le_UJ hk), ← e]
    exact this
  refine ⟨Q, N, Seminorm.continuous_of_le hq hQq, h1, fun h hh x => ?_, fun k hk x => ?_⟩
  · rw [hQ (π h x)]
    refine ciSup_le fun g => ?_
    rw [hf, hmul g.1 g.2 h hh x |>.symm, div_le_iff₀ (hW _)]
    calc p i (π (g.1 * h) x) ≤ W (g.1 * h) * Q x := h1 _ (mul_mem_UJ g.2 hh) x
      _ ≤ (W g.1 * W h) * Q x := mul_le_mul_of_nonneg_right (hWm _ _) (apply_nonneg _ _)
      _ = W h * Q x * W g.1 := by ring
  · refine le_antisymm (hKk k hk x) ?_
    obtain ⟨k', hk', e⟩ := KInvarianceAlt.kinv hk
    have := hKk k' hk' (π k x)
    rwa [← hmul k' (K_le_UJ hk') k (K_le_UJ hk), e, hπ.map_one] at this

end PositivityTheory.CW

end
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.ExistsNormingFunctional
section
noncomputable section

open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum

namespace PositivityTheory.CW

namespace ZeroOnDense

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Mx n → (H →L[ℂ] H)} {E : Type} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [T2Space E]
  {p : ℕ → Seminorm ℂ E}

theorem zero_on (hp : WithSeminorms p) (hD : Dens ε σ) (Φ : H → E)
    (hsub : ∀ x y, Sm ε σ x → Sm ε σ y → Φ (x - y) = Φ x - Φ y)
    (hb : ∀ i, ∃ (S : List (List (Mx n))) (C : ℝ), Words (lieSet ε) S ∧
      ∀ u, Sm ε σ u → p i (Φ u) ≤ C * sobNorm σ S u)
    (h0 : ∀ v, IsKFin ε σ v → Φ v = 0) : ∀ w, Sm ε σ w → Φ w = 0 := by
  intro w hw
  by_contra hne
  obtain ⟨i, hi⟩ := hp.separating_of_T1 _ hne
  obtain ⟨S, C, hS, hC⟩ := hb i
  have key : ∀ δ : ℝ, 0 < δ → p i (Φ w) ≤ |C| * δ := by
    intro δ hδ
    obtain ⟨v, hv, hd⟩ := hD.2.2 w hw S hS δ hδ
    have hvs : Sm ε σ v := hD.1 v hv
    have hwv : Sm ε σ (w - v) := sm_iff.2 ((smooth (Jm ε) σ).sub_mem (sm_iff.1 hw) (sm_iff.1 hvs))
    have e : Φ w = Φ (w - v) := by rw [hsub w v hw hvs, h0 v hv, sub_zero]
    rw [e]
    calc p i (Φ (w - v)) ≤ C * sobNorm σ S (w - v) := hC _ hwv
      _ ≤ |C| * sobNorm σ S (w - v) := mul_le_mul_of_nonneg_right (le_abs_self C) (sobNorm_nonneg _ _ _)
      _ ≤ |C| * δ := mul_le_mul_of_nonneg_left hd.le (abs_nonneg C)
  have hpos : 0 < p i (Φ w) := lt_of_le_of_ne (apply_nonneg _ _) (Ne.symm hi)
  set x := p i (Φ w) with hx
  have h1 := key (x / (2 * (|C| + 1))) (by positivity)
  have h2 : |C| * (x / (2 * (|C| + 1))) < x := by
    rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith [abs_nonneg C]
  linarith

end ZeroOnDense

theorem d0 : D0 := by
  intro n ε H _ _ _ σ hU hI E _ _ _ _ _ _ p π dπ hπ hD T hT h0
  exact ZeroOnDense.zero_on hπ.withSeminorms hD T (fun x y _ _ => map_sub T x y) hT h0

end PositivityTheory.CW

end
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.ExponentialKSet
section
open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum GlobalTheory.LowTypeDetermined

namespace PositivityTheory.CW

namespace ExistsFunctional

theorem exists_functional {E : Type} [AddCommGroup E] [Module ℂ E] (q : Seminorm ℂ E) {x₀ : E} (hx : q x₀ ≠ 0) :
    ∃ φ : Module.Dual ℂ E, φ x₀ ≠ 0 ∧ ∀ x, ‖φ x‖ ≤ q x := by
  have h0 : x₀ ≠ 0 := by
    rintro rfl
    exact hx (map_zero q)
  let e := LinearEquiv.toSpanNonzeroSingleton ℂ E x₀ h0
  let f : Module.Dual ℂ (Submodule.span ℂ {x₀}) := (q x₀ : ℂ) • (e.symm : _ →ₗ[ℂ] ℂ)
  have hfe : ∀ t : ℂ, f (e t) = t * q x₀ := by
    intro t
    simp [f, mul_comm]
  obtain ⟨g, hg, hgp⟩ := Module.Dual.exists_extension_of_le_seminorm (Submodule.span ℂ {x₀}) f
    (p := q) (by
      intro y
      obtain ⟨t, rfl⟩ := e.surjective y
      rw [hfe, norm_mul, Complex.norm_real, Real.norm_of_nonneg (apply_nonneg q x₀)]
      rw [LinearEquiv.toSpanNonzeroSingleton_apply]
      simp [map_smul_eq_mul])
  refine ⟨g, ?_, hgp⟩
  have h1 := hg (e 1)
  rw [hfe, one_mul] at h1
  have : ((e 1 : Submodule.span ℂ {x₀}) : E) = x₀ := by
    rw [LinearEquiv.toSpanNonzeroSingleton_one]
  rw [this] at h1
  rw [h1]
  exact_mod_cast hx

end ExistsFunctional

theorem e1b : faceMap_comp_succAbove_castSucc := by
  unfold faceMap_comp_succAbove_castSucc AllTgt
  intro n ε H _ _ _ σ hU hI E _ _ _ _ _ _ p π dπ hrep T hT i w₀ hw₀ hp u hu hu0
  by_contra hall
  push_neg at hall
  obtain ⟨φ, hφ0, hφ⟩ := ExistsFunctional.exists_functional (p i) hp
  let ℓ : H →ₗ[ℂ] ℂ := φ ∘ₗ T
  have hlie : ((GlobalTheory.LowTypeDetermined.lie (Jm ε) : Set (Mx n))) = lieSet ε := rfl
  have hsm : ∀ w, Sm ε σ w →
      w ∈ GlobalTheory.LowTypeDetermined.smooth (Jm ε) (fun g => σ (1 * g * (1 : Mx n)⁻¹)) := by
    intro w hw
    change SmoothVec ((GlobalTheory.LowTypeDetermined.lie (Jm ε) : Set (Mx n)))
      (fun g => σ (1 * g * (1 : Mx n)⁻¹)) w
    simp only [inv_one, mul_one, one_mul]
    rw [hlie]
    exact hw
  have key := GlobalTheory.LowTypeDetermined.eq_zero_of_translates (G := Jm ε) (P := 1) hU hI isUnit_one
    (by simp) (ℓ := ℓ) ?_ (hsm u hu) hu0 ?_ (hsm w₀ hw₀)
  · exact hφ0 key
  · obtain ⟨S, C, hS, hb⟩ := hT.2 i
    refine ⟨S, C, ?_, ?_⟩
    · rw [hlie]
      exact hS
    · simp only [inv_one, mul_one, one_mul]
      rw [hlie]
      intro w hw
      exact (hφ (T w)).trans (hb w hw)
  · intro g hg
    show φ (T (σ g u)) = 0
    rw [hT.1 g hg u hu]
    exact norm_le_zero_iff.mp ((hφ _).trans (hall g hg).le)

end PositivityTheory.CW
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.HilbertSchmidtSqEq
section
noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open ReciprocityTheory.ChartRestriction.DS (actM casimirK)

namespace PositivityTheory.CW.MatrixActionLinear

variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]

theorem actM_add (A : Fin n → Fin n → Module.End ℂ M) (X Y : Mx n) : actM A (X + Y) = actM A X + actM A Y := by
  unfold actM
  simp only [Matrix.add_apply, add_smul, Finset.sum_add_distrib]

theorem actM_smul (A : Fin n → Fin n → Module.End ℂ M) (c : ℂ) (X : Mx n) : actM A (c • X) = c • actM A X := by
  unfold actM
  simp only [Matrix.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]

theorem actM_single (A : Fin n → Fin n → Module.End ℂ M) (a b : Fin n) : actM A (Matrix.single a b 1) = A a b := by
  classical
  unfold actM
  rw [Finset.sum_eq_single a]
  · rw [Finset.sum_eq_single b]
    · simp
    · intro d _ hd
      simp [Ne.symm hd]
    · simp
  · intro c _ hc
    refine Finset.sum_eq_zero fun d _ => ?_
    simp [Ne.symm hc]
  · simp

end PositivityTheory.CW.MatrixActionLinear

namespace PositivityTheory.CW

open MatrixActionLinear in
theorem e3b : faceMap_castSucc_comp_eq_succ := by
  classical
  intro n ε H _ _ _ σ hU hI E _ _ _ _ _ _ p π dπ hπ A hA T hT m
  haveI : IsTopologicalAddGroup E := hπ.withSeminorms.topologicalAddGroup
  haveI : ContinuousSMul ℂ E := hπ.withSeminorms.continuousSMul

  let P : Module.End ℂ (kfin ε σ) → Prop := fun u => ∃ D : E →L[ℂ] E, ∀ v : kfin ε σ, T ((u v : kfin ε σ) : H) = D (T v)
  have hone : P 1 := ⟨1, fun v => rfl⟩
  have hadd : ∀ u₁ u₂, P u₁ → P u₂ → P (u₁ + u₂) := by
    rintro u₁ u₂ ⟨D₁, h₁⟩ ⟨D₂, h₂⟩
    refine ⟨D₁ + D₂, fun v => ?_⟩
    simp only [LinearMap.add_apply, Submodule.coe_add, map_add (f := _), h₁, h₂, _root_.add_apply]
  have hmul : ∀ u₁ u₂, P u₁ → P u₂ → P (u₁ * u₂) := by
    rintro u₁ u₂ ⟨D₁, h₁⟩ ⟨D₂, h₂⟩
    refine ⟨D₁.comp D₂, fun v => ?_⟩
    rw [Module.End.mul_apply, h₁, h₂]
    rfl
  have hzero : P 0 := ⟨0, fun v => by simp⟩
  have hsum : ∀ (s : Finset (Fin n)) (f : Fin n → Module.End ℂ (kfin ε σ)), (∀ i ∈ s, P (f i)) → P (∑ i ∈ s, f i) := by
    intro s f hf
    induction s using Finset.induction_on with
    | empty => simpa using hzero
    | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact hadd _ _ (hf a (Finset.mem_insert_self a s)) (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))
  have hgen : ∀ a b, P (A a b) := by
    intro a b
    obtain ⟨h1, h2, h3, -⟩ := complex_parts_mem_lie_algebra_holds n ε (Matrix.single a b 1)
    set X₁ := cpart1 ε (Matrix.single a b 1)
    set X₂ := cpart2 ε (Matrix.single a b 1)
    have hX₁ : X₁ ∈ lieSet ε := h1
    have hX₂ : X₂ ∈ lieSet ε := h2
    have eA : A a b = actM A X₁ + Complex.I • actM A X₂ := by
      rw [← actM_single A a b, h3, actM_add, actM_smul]
    refine ⟨dπ X₁ + Complex.I • dπ X₂, fun v => ?_⟩
    have hv : IsKFin ε σ (v : H) := v.2
    rw [eA, LinearMap.add_apply, LinearMap.smul_apply, Submodule.coe_add, Submodule.coe_smul, hA X₁ hX₁ v,
      hA X₂ hX₂ v, map_add, map_smul, hT X₁ hX₁ v hv, hT X₂ hX₂ v hv]
    rfl
  have hcas : P (casimirK ε A) := by
    unfold casimirK
    exact hsum _ _ fun a _ => hsum _ _ fun b _ => hmul _ _ (hgen a b) (hgen b a)
  have hpow : ∀ k : ℕ, P ((1 + casimirK ε A) ^ k) := by
    intro k
    induction k with
    | zero => simpa using hone
    | succ k ih => rw [pow_succ]; exact hmul _ _ ih (hadd _ _ hone hcas)
  exact hpow m

end PositivityTheory.CW

end
end

