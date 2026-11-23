module

public import Development.WeilBound.ThetaLifts.LeviDeterminants.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenNsmulAdelicCompletionOfVectorSet
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0298
public import Development.AutomorphicSpectrum.Proofs.MembershipProofs.Bundle0007

@[expose] public section

-- bundled from Development.WeilBound.ThetaLifts.LeviDeterminants.GrowFin
section
noncomputable section

namespace PositivityTheory.ThKF0.Grow.Fi

open scoped Matrix NNReal ENNReal Classical Pointwise
open NumberField IsDedekindDomain Filter Topology GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

def Int' (a : Af F) : Prop := ∀ v, a v ∈ v.adicCompletionIntegers F

theorem Int'.nsmul {a : Af F} (h : Int' a) (k : ℕ) : Int' (k • a) := fun v => by
  have : (k • a) v = k • a v := map_nsmul (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) k a
  rw [this]
  exact nsmul_mem (h v) k

theorem exists_pi (U : Set (κ → Af F)) (hU : U ∈ 𝓝 (0 : κ → Af F)) :
    ∃ N : ℕ, 0 < N ∧ ∀ M, N ∣ M → ∀ a : κ → Af F, (∀ i, Int' (a i)) → M • a ∈ U := by
  rw [nhds_pi, Filter.mem_pi] at hU
  obtain ⟨I, -, t, ht, hI⟩ := hU
  choose N hN h using fun i => GlobalTheory.AdLat.OpenLat.exists_nsmul_adele F (t i) (ht i)
  refine ⟨∏ i, N i, Finset.prod_pos fun i _ => hN i, fun M hM a ha => hI fun i _ => ?_⟩
  obtain ⟨k, rfl⟩ := (Finset.dvd_prod_of_mem N (Finset.mem_univ i)).trans hM
  rw [Pi.smul_apply, mul_smul]
  exact h i _ ((ha i).nsmul k)

theorem eventually_fix (c : Af F → ℂ) (hc : IsLocallyConstant c) (h0 : c 0 = 1) (e : Af F) {g : (κ → Af F) → ℂ}
    (hg : g ∈ SB (κ → Af F)) : ∀ᶠ w in 𝓝 (0 : (κ → Af F) × (κ → Af F)), ∀ x,
      c (x ⬝ᵥ w.2 + e * (w.1 ⬝ᵥ w.2)) * g (x + w.1) = g x := by
  let C : Set (κ → Af F) := Set.pi Set.univ fun _ => {a | Int' a}
  have hC : IsCompact C := isCompact_univ_pi fun _ => GlobalTheory.AdeleCocompact.isCompact_integral F
  have hO : IsOpen C := isOpen_set_pi Set.finite_univ fun _ _ => GlobalTheory.AdLat.OpenLat.isOpen_integral F
  have hz : (0 : κ → Af F) ∈ C := fun i _ v => zero_mem _
  have hK : IsCompact ((fun p : (κ → Af F) × (κ → Af F) => p.1 - p.2) '' (tsupport g ×ˢ C)) :=
    (hg.2.isCompact.prod hC).image (by fun_prop)
  have h1 : ∀ᶠ w in 𝓝 (0 : (κ → Af F) × (κ → Af F)),
      ∀ x ∈ (fun p : (κ → Af F) × (κ → Af F) => p.1 - p.2) '' (tsupport g ×ˢ C),
      c (x ⬝ᵥ w.2 + e * (w.1 ⬝ᵥ w.2)) * g (x + w.1) = g x := by
    refine hK.eventually_forall_of_forall_eventually fun x _ => ?_
    have l1 : IsLocallyConstant fun z : ((κ → Af F) × (κ → Af F)) × (κ → Af F) =>
        c (z.2 ⬝ᵥ z.1.2 + e * (z.1.1 ⬝ᵥ z.1.2)) * g (z.2 + z.1.1) :=
      (hc.comp_continuous (by unfold dotProduct; fun_prop)).mul (hg.1.comp_continuous (by fun_prop))
    have l2 : IsLocallyConstant fun z : ((κ → Af F) × (κ → Af F)) × (κ → Af F) => g z.2 :=
      hg.1.comp_continuous continuous_snd
    filter_upwards [l1.eventually_eq (0, x), l2.eventually_eq (0, x)] with z e1 e2
    rw [e1, e2]
    simp [h0]
  filter_upwards [h1, (hO.preimage continuous_fst).mem_nhds (show (0 : (κ → Af F) × (κ → Af F)) ∈ _ from hz)]
    with w hw hw' x
  by_cases hx : x ∈ (fun p : (κ → Af F) × (κ → Af F) => p.1 - p.2) '' (tsupport g ×ˢ C)
  · exact hw x hx
  · have a1 : g (x + w.1) = 0 := by
      by_contra hne
      exact hx ⟨(x + w.1, w.1), ⟨subset_tsupport _ hne, hw'⟩, by simp⟩
    have a2 : g x = 0 := by
      by_contra hne
      exact hx ⟨(x, 0), ⟨subset_tsupport _ hne, hz⟩, by simp⟩
    rw [a1, a2, mul_zero]

theorem intF_nat {a : AF F} (h : IntF a) (k : ℕ) : IntF ((k : AF F) * a) := by
  refine ⟨?_, fun v => ?_⟩
  · change (k : AF F).1 * a.1 = 0
    rw [h.1, mul_zero]
  · rw [map_mul, map_natCast]
    exact mul_mem (natCast_mem _ k) (h.2 v)

theorem integralPoint_natCast_smul {w : Pt F κ} (h : IntP w) (k : ℕ) : IntP ((k : AF F) • w) :=
  ⟨fun i => intF_nat (h.1 i) k, fun i => intF_nat (h.2 i) k⟩

theorem dot_fst (x y : κ → AF F) (hy : ∀ i, (y i).1 = 0) : (x ⬝ᵥ y).1 = 0 :=
  (map_sum (RingHom.fst (Ainf F) (Af F)) _ Finset.univ).trans (Finset.sum_eq_zero fun i _ => by
    change (x i).1 * (y i).1 = 0
    rw [hy i, mul_zero])

theorem dot_snd (x y : κ → AF F) : (x ⬝ᵥ y).2 = (fun i => (x i).2) ⬝ᵥ fun i => (y i).2 :=
  map_sum (RingHom.snd (Ainf F) (Af F)) _ Finset.univ

theorem fix_pure {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (f : SInf F κ) {g : (κ → Af F) → ℂ} (hg : g ∈ SB (κ → Af F)) :
    ∃ m : ℕ, 1 ≤ m ∧ ∀ w : Pt F κ, IntP w → schr ψ ((m : AF F) • w) (pureA F f g) = pureA F f g := by
  let ψf : AddChar (Af F) ℂ := ψ.compAddMonoidHom (AddMonoidHom.inr (Ainf F) (Af F))
  have hl : IsLocallyConstant ψf := GlobalTheory.CompanionTheory.AdelicHeis.isLocallyConstant_fin ψf
    (hψ.1.comp (continuous_const.prodMk continuous_id)) fun x => GlobalTheory.CompanionTheory.AdelicHeis.norm_eq_one ψ hψ.1 hψ.2.1 _
  obtain ⟨U, hU, U', hU', h⟩ := mem_nhds_prod_iff.1 (eventually_fix ψf hl ψf.map_zero_eq_one (⅟(2 : AF F)).2 hg)
  obtain ⟨N, hN, h1⟩ := exists_pi U hU
  obtain ⟨N', hN', h2⟩ := exists_pi U' hU'
  refine ⟨N * N', Nat.mul_pos hN hN', fun w hw => funext fun x => ?_⟩
  have hw' := integralPoint_natCast_smul hw (N * N')
  have e1 : (fun i => ((((N * N' : ℕ) : AF F) • w).1 i).2) = (N * N') • fun i => (w.1 i).2 := by
    funext i
    rw [Pi.smul_apply, nsmul_eq_mul]; rfl
  have e2 : (fun i => ((((N * N' : ℕ) : AF F) • w).2 i).2) = (N * N') • fun i => (w.2 i).2 := by
    funext i
    rw [Pi.smul_apply, nsmul_eq_mul]; rfl
  have key := h (Set.mk_mem_prod (h1 _ (dvd_mul_right N N') (fun i => (w.1 i).2) fun i => (hw.1 i).2)
    (h2 _ (dvd_mul_left N' N) (fun i => (w.2 i).2) fun i => (hw.2 i).2)) fun i => (x i).2
  rw [← e1, ← e2] at key
  generalize ((N * N' : ℕ) : AF F) • w = u at hw' key
  have p : ψ (x ⬝ᵥ u.2 + ⅟(2 : AF F) * (u.1 ⬝ᵥ u.2)) = ψf (((fun i => (x i).2) ⬝ᵥ fun i => (u.2 i).2) +
      (⅟(2 : AF F)).2 * ((fun i => (u.1 i).2) ⬝ᵥ fun i => (u.2 i).2)) := by
    rw [← dot_snd, ← dot_snd]
    refine congrArg ψ (Prod.ext ?_ rfl)
    change (x ⬝ᵥ u.2).1 + (⅟(2 : AF F)).1 * (u.1 ⬝ᵥ u.2).1 = 0
    rw [dot_fst _ _ fun i => (hw'.2 i).1, dot_fst _ _ fun i => (hw'.2 i).1, mul_zero, add_zero]
  have q : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F ((x + u.1) i).1) =
      fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1 := by
    funext i
    change InfiniteAdeleRing.ringEquiv_mixedSpace F ((x i).1 + (u.1 i).1) = _
    rw [(hw'.1 i).1, add_zero]
  simp only [schr, pureA]
  rw [p, q, mul_left_comm]
  exact congrArg _ key

theorem fix {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) :
    ∃ m : ℕ, 1 ≤ m ∧ ∀ w : Pt F κ, IntP w → schr ψ ((m : AF F) • w) Φ = Φ := by
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    exact fix_pure hψ f hg
  | zero => exact ⟨1, le_rfl, fun w _ => funext fun x => by simp [schr]⟩
  | add a b _ _ ha hb =>
    obtain ⟨m, hm, h⟩ := ha
    obtain ⟨m', hm', h'⟩ := hb
    refine ⟨m * m', Nat.mul_pos hm hm', fun w hw => funext fun x => ?_⟩
    have e1 := congrFun (h _ (integralPoint_natCast_smul hw m')) x
    have e2 := congrFun (h' _ (integralPoint_natCast_smul hw m)) x
    rw [smul_smul] at e1 e2
    rw [mul_comm] at e2
    rw [Nat.cast_mul, Pi.add_apply, ← e1, ← e2]
    simp only [schr, Pi.add_apply, mul_add]
  | smul c a _ ha =>
    obtain ⟨m, hm, h⟩ := ha
    refine ⟨m, hm, fun w hw => funext fun x => ?_⟩
    rw [Pi.smul_apply, ← congrFun (h w hw) x]
    simp only [schr, Pi.smul_apply, smul_eq_mul]
    ring

end PositivityTheory.ThKF0.Grow.Fi

namespace PositivityTheory.ThKF0.Grow

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

theorem finInv : FinInv := by
  intro F _ _ κ _ ψ hψ Φ hΦ
  obtain ⟨m, hm, h⟩ := Fi.fix hψ hΦ
  refine ⟨m, hm, fun T s d c hT hs w hw => ?_⟩
  rw [← hT.impl _ Φ hΦ, map_smul, Nat.cast_mul, mul_smul, h _ (hs.fin w hw)]

end PositivityTheory.ThKF0.Grow
end
end

-- bundled from Development.WeilBound.ThetaLifts.LeviDeterminants.GrowLine
section
noncomputable section

namespace PositivityTheory.ThKF0.Grow

open scoped Matrix NNReal ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

section Line

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

def lineFn (f : SchwartzMap V ℂ) (A : V) (L : V →L[ℝ] ℝ) (c : ℝ) (p : V) (t : ℝ) : ℂ :=
  Complex.exp (-(2 * Real.pi * Complex.I) * ((t * L p + t ^ 2 * c : ℝ) : ℂ)) * f (p + t • A)

def lineD (f : SchwartzMap V ℂ) (A : V) (L : V →L[ℝ] ℝ) (c : ℝ) (p : V) (t : ℝ) : ℂ :=
  Complex.exp (-(2 * Real.pi * Complex.I) * ((t * L p + t ^ 2 * c : ℝ) : ℂ)) *
    (-(2 * Real.pi * Complex.I) * ((L p + 2 * t * c : ℝ) : ℂ) * f (p + t • A) + fderiv ℝ f (p + t • A) A)

theorem hasDerivAt_lineFn (f : SchwartzMap V ℂ) (A : V) (L : V →L[ℝ] ℝ) (c : ℝ) (p : V) (t : ℝ) :
    HasDerivAt (lineFn f A L c p) (lineD f A L c p t) t := by
  have h1 : HasDerivAt (fun s : ℝ => s * L p + s ^ 2 * c) (L p + 2 * t * c) t := by
    have a1 : HasDerivAt (fun s : ℝ => s * L p) (L p) t := by simpa using (hasDerivAt_id t).mul_const (L p)
    have a2 : HasDerivAt (fun s : ℝ => s ^ 2 * c) (2 * t * c) t := by
      simpa using ((hasDerivAt_id t).pow 2).mul_const c
    exact a1.fun_add a2
  have h2 := ((h1.ofReal_comp).const_mul (-(2 * Real.pi * Complex.I))).cexp
  have h3 : HasDerivAt (fun s : ℝ => p + s • A) A t := by
    simpa using ((hasDerivAt_id t).smul_const A).const_add p
  have h4 : HasDerivAt (fun s : ℝ => f (p + s • A)) (fderiv ℝ f (p + t • A) A) t :=
    (f.hasFDerivAt (p + t • A)).comp_hasDerivAt t h3
  refine (h2.fun_mul h4).congr_deriv ?_
  simp only [lineD]
  push_cast
  ring

theorem lineD_bound (f : SchwartzMap V ℂ) (A A₀ : V) (L : V →L[ℝ] ℝ) (c : ℝ) (k : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (m : V) (t : ℝ), |t| ≤ 1 → ‖lineD f A L c (m + A₀) t‖ ≤ K * ((1 + ‖m‖) ^ k)⁻¹ := by
  set C₀ : ℝ := 2 ^ (k + 1) * (Finset.Iic (k + 1, 1)).sup (schwartzSeminormFamily ℂ V ℂ) f
  have hC0 : 0 ≤ C₀ := by positivity
  have b0 : ∀ q, (1 + ‖q‖) ^ (k + 1) * ‖f q‖ ≤ C₀ := fun q => by
    have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (k + 1, 1)) (k := k + 1) (n := 0) le_rfl (by simp) f q
    rwa [norm_iteratedFDeriv_zero] at h
  have b1 : ∀ q, (1 + ‖q‖) ^ k * ‖fderiv ℝ f q‖ ≤ C₀ := fun q => by
    have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (k + 1, 1)) (k := k + 1) (n := 1) le_rfl le_rfl f q
    rw [norm_iteratedFDeriv_one] at h
    refine le_trans ?_ h
    have hS : (1 : ℝ) ≤ 1 + ‖q‖ := by linarith [norm_nonneg q]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hS (Nat.le_succ k)) (norm_nonneg _)
  set R : ℝ := ‖A₀‖ + ‖A‖ with hR
  have hR0 : 0 ≤ R := by positivity
  set B : ℝ := ‖L‖ * (1 + ‖A‖ + ‖A‖ ) + 2 * |c| with hB
  have hB0 : 0 ≤ B := by positivity
  refine ⟨(2 * Real.pi * B * C₀ + ‖A‖ * C₀) * (1 + R) ^ k, by positivity, fun m t ht => ?_⟩
  set p := m + A₀ with hp
  set q := p + t • A with hq
  have htA : ‖t • A‖ ≤ ‖A‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg _) ht
  have hpq : ‖p‖ ≤ ‖q‖ + ‖A‖ := by
    have : p = q - t • A := by simp [hq]
    rw [this]
    exact (norm_sub_le _ _).trans (by gcongr)
  have hmq : ‖m‖ ≤ ‖q‖ + R := by
    have : m = q - t • A - A₀ := by simp [hq, hp]
    rw [this]
    refine (norm_sub_le _ _).trans ?_
    have := norm_sub_le q (t • A)
    rw [hR]
    linarith
  set S : ℝ := 1 + ‖q‖ with hS
  have hS1 : 1 ≤ S := by rw [hS]; linarith [norm_nonneg q]
  have hS0 : 0 < S := by linarith
  have hSk : 0 < S ^ k := by positivity
  have hf : S * ‖f q‖ ≤ C₀ * (S ^ k)⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ hSk]
    have := b0 q
    calc S * ‖f q‖ * S ^ k = S ^ (k + 1) * ‖f q‖ := by ring
      _ ≤ C₀ := this
  have hdf : ‖fderiv ℝ f q‖ ≤ C₀ * (S ^ k)⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ hSk, mul_comm]
    exact b1 q
  have hLp : |L p + 2 * t * c| ≤ S * B := by
    have h1 : |L p| ≤ ‖L‖ * (‖q‖ + ‖A‖) :=
      (L.le_opNorm p).trans (mul_le_mul_of_nonneg_left hpq (norm_nonneg _))
    have h2 : |2 * t * c| ≤ 2 * |c| := by
      rw [abs_mul, abs_mul, abs_two]
      have := abs_nonneg c
      nlinarith
    have h3 : ‖q‖ + ‖A‖ ≤ S * (1 + ‖A‖ + ‖A‖) := by
      have hA := norm_nonneg A
      have hq0 := norm_nonneg q
      nlinarith
    calc |L p + 2 * t * c| ≤ |L p| + |2 * t * c| := abs_add_le _ _
      _ ≤ ‖L‖ * (S * (1 + ‖A‖ + ‖A‖)) + S * (2 * |c|) := by
          have := mul_le_mul_of_nonneg_left h3 (norm_nonneg L)
          have h4 : 2 * |c| ≤ S * (2 * |c|) := le_mul_of_one_le_left (by positivity) hS1
          linarith
      _ = S * B := by rw [hB]; ring
  have hnorm : ‖lineD f A L c p t‖ ≤ (2 * Real.pi * B * C₀ + ‖A‖ * C₀) * (S ^ k)⁻¹ := by
    have hexp : ‖Complex.exp (-(2 * Real.pi * Complex.I) * ((t * L p + t ^ 2 * c : ℝ) : ℂ))‖ = 1 := by
      have : -(2 * Real.pi * Complex.I) * ((t * L p + t ^ 2 * c : ℝ) : ℂ) =
          ((-(2 * Real.pi) * (t * L p + t ^ 2 * c) : ℝ) : ℂ) * Complex.I := by
        push_cast
        ring
      rw [this, Complex.norm_exp_ofReal_mul_I]
    have hc : ‖-(2 * Real.pi * Complex.I)‖ = 2 * Real.pi := by
      simp [abs_of_pos Real.pi_pos]
    rw [lineD, norm_mul, hexp, one_mul]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, hc, Complex.norm_real, Real.norm_eq_abs]
    have h1 : 2 * Real.pi * |L p + 2 * t * c| * ‖f q‖ ≤ 2 * Real.pi * B * (C₀ * (S ^ k)⁻¹) := by
      calc 2 * Real.pi * |L p + 2 * t * c| * ‖f q‖ ≤ 2 * Real.pi * (S * B) * ‖f q‖ := by gcongr
        _ = 2 * Real.pi * B * (S * ‖f q‖) := by ring
        _ ≤ _ := by gcongr
    have h2 : ‖(fderiv ℝ f q) A‖ ≤ ‖A‖ * (C₀ * (S ^ k)⁻¹) := by
      refine ((fderiv ℝ f q).le_opNorm A).trans ?_
      rw [mul_comm]
      gcongr
    calc _ ≤ 2 * Real.pi * B * (C₀ * (S ^ k)⁻¹) + ‖A‖ * (C₀ * (S ^ k)⁻¹) := add_le_add h1 h2
      _ = _ := by ring
  refine hnorm.trans ?_
  have hT : 1 + ‖m‖ ≤ S * (1 + R) := by
    rw [hS]
    nlinarith [norm_nonneg q]
  have hT0 : 0 < 1 + ‖m‖ := by linarith [norm_nonneg m]
  have hinv : (S ^ k)⁻¹ ≤ (1 + R) ^ k * ((1 + ‖m‖) ^ k)⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), inv_mul_le_iff₀ hSk, ← mul_pow]
    exact pow_le_pow_left₀ hT0.le hT k
  calc _ ≤ (2 * Real.pi * B * C₀ + ‖A‖ * C₀) * ((1 + R) ^ k * ((1 + ‖m‖) ^ k)⁻¹) := by gcongr
    _ = _ := by ring

end Line

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem evI_add (a b : AF F) : evI F (a + b) = evI F a + evI F b :=
  map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F) a.1 b.1

theorem evI_mul (a b : AF F) : evI F (a * b) = evI F a * evI F b :=
  map_mul (InfiniteAdeleRing.ringEquiv_mixedSpace F) a.1 b.1

theorem evI_zero : evI F 0 = 0 := map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)

theorem evI_sum {ι : Type} (s : Finset ι) (g : ι → AF F) : evI F (∑ i ∈ s, g i) = ∑ i ∈ s, evI F (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using evI_zero
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, evI_add, ih]

theorem evI_realAd (t : ℝ) : evI F (realAd F t) = algebraMap ℝ (mixedEmbedding.mixedSpace F) t := by
  change (InfiniteAdeleRing.ringEquiv_mixedSpace F) ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm _) = _
  exact (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply _

def linForm (B : κ → mixedEmbedding.mixedSpace F) : (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    (∑ i, (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)) ∘ₗ (LinearMap.mulRight ℝ (B i)) ∘ₗ
      (LinearMap.proj i : (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] mixedEmbedding.mixedSpace F))

theorem linForm_apply (B y : κ → mixedEmbedding.mixedSpace F) :
    linForm B y = Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, y i * B i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [linForm, map_sum, LinearMap.sum_apply]

theorem phase_line (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) (a b x : κ → AF F) (hb : At (evI F) b) (t : ℝ) :
    ψ (x ⬝ᵥ (realAd F t • b) + ⅟(2 : AF F) * ((realAd F t • a) ⬝ᵥ (realAd F t • b))) =
      Complex.exp (-(2 * Real.pi * Complex.I) * ((t * linForm (fun i => evI F (b i)) (fun i => evI F (x i)) +
        t ^ 2 * Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F ⅟(2 : AF F) * ∑ i, evI F (a i) * evI F (b i)) : ℝ) : ℂ)) := by
  have hz : At (evI F) (x ⬝ᵥ (realAd F t • b) + ⅟(2 : AF F) * ((realAd F t • a) ⬝ᵥ (realAd F t • b))) := by
    intro s hs
    have hsb : ∀ i, s * b i = 0 := fun i => by simpa using congrFun (hb s hs) i
    have e1 : ∀ i, s * (x i * (realAd F t * b i)) = x i * realAd F t * (s * b i) := fun i => by ring
    have e2 : ∀ i, s * (⅟(2 : AF F) * (realAd F t * a i * (realAd F t * b i))) =
        ⅟(2 : AF F) * (realAd F t * a i * realAd F t) * (s * b i) := fun i => by ring
    simp only [dotProduct, Pi.smul_apply, smul_eq_mul, mul_add, Finset.mul_sum, e1, e2, hsb, mul_zero, Finset.sum_const_zero,
      add_zero]
  rw [hψ.2.2 _ hz]
  congr 3
  have ev : evI F (x ⬝ᵥ (realAd F t • b) + ⅟(2 : AF F) * ((realAd F t • a) ⬝ᵥ (realAd F t • b))) =
      t • (∑ i, evI F (x i) * evI F (b i)) + (t ^ 2) • (evI F ⅟(2 : AF F) * ∑ i, evI F (a i) * evI F (b i)) := by
    simp only [dotProduct, Pi.smul_apply, smul_eq_mul, evI_add, evI_mul, evI_sum, evI_realAd, Algebra.smul_def, map_pow,
      Finset.mul_sum]
    congr 1
    · exact Finset.sum_congr rfl fun i _ => by ring
    · exact Finset.sum_congr rfl fun i _ => by ring
  rw [ev, map_add (f := _), map_smul, map_smul, linForm_apply]
  simp [smul_eq_mul]


omit [Fintype κ] in
theorem snd_eq_zero {z : κ → AF F} (hz : At (evI F) z) (i : κ) : (z i).2 = 0 := by
  let w : AF F := LinearMap.inr F (Ainf F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) 1
  have e0 : evI F w = 0 := map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)
  have h : w * z i = 0 := congrFun (hz w e0) i
  have h2 : (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) * (z i).2 = 0 := congrArg Prod.snd h
  simpa using h2


open scoped Classical in
theorem schr_line (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) (a b : κ → AF F) (ha : At (evI F) a) (hb : At (evI F) b)
    (f : SInf F κ) (g : (κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) → ℂ) (x : κ → AF F) (t : ℝ) :
    schr ψ (realAd F t • a, realAd F t • b) (pureA F f g) x =
      lineFn f (fun i => evI F (a i)) (linForm fun i => evI F (b i))
        (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F ⅟(2 : AF F) * ∑ i, evI F (a i) * evI F (b i)))
        (fun i => evI F (x i)) t * g (fun i => (x i).2) := by
  have hat : At (evI F) (realAd F t • a) := fun s hs => by
    rw [smul_comm, ha s hs, smul_zero]
  have e : (fun i => evI F ((x + realAd F t • a) i)) = (fun i => evI F (x i)) + t • fun i => evI F (a i) := by
    funext i
    simp [evI_add, evI_mul, evI_realAd, Algebra.smul_def]
  have e2 : (fun i => ((x + realAd F t • a) i).2) = fun i => (x i).2 := by
    funext i
    have h := snd_eq_zero hat i
    show (x i).2 + ((realAd F t • a) i).2 = (x i).2
    rw [h, add_zero]
  show ψ _ * (f (fun i => evI F ((x + realAd F t • a) i)) * g (fun i => ((x + realAd F t • a) i).2)) = _
  rw [phase_line ψ hψ a b x hb t, e, e2, lineFn]
  exact (mul_assoc _ _ _).symm

end PositivityTheory.ThKF0.Grow
end
end

-- bundled from Development.WeilBound.ThetaLifts.LeviDeterminants.GrowTr
section
noncomputable section

namespace PositivityTheory.ThKF0.Grow

open scoped Matrix Classical
open NumberField

theorem exists_trace_ne {F : Type} [Field F] [NumberField F] (x : mixedEmbedding.mixedSpace F) (hx : x ≠ 0) :
    ∃ y, Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (x * y) ≠ 0 := by
  obtain ⟨y, hy⟩ : ∃ y : mixedEmbedding.mixedSpace F, x * y * x = x :=
    ⟨(fun w => (x.1 w)⁻¹, fun w => (x.2 w)⁻¹), Prod.ext (funext fun w => mul_inv_mul_cancel (x.1 w))
      (funext fun w => mul_inv_mul_cancel (x.2 w))⟩
  refine ⟨y, fun h => hx ?_⟩
  have hi : IsIdempotentElem (LinearMap.mulLeft ℝ (x * y)) := by
    refine LinearMap.ext fun z => ?_
    change x * y * (x * y * z) = x * y * z
    rw [← mul_assoc, ← mul_assoc, hy]
  have ht := (LinearMap.IsIdempotentElem.isProj_range _ hi).trace
  have h0 : LinearMap.trace ℝ _ (LinearMap.mulLeft ℝ (x * y)) = 0 := h
  rw [h0] at ht
  have hr : LinearMap.range (LinearMap.mulLeft ℝ (x * y)) = ⊥ :=
    Submodule.finrank_eq_zero.1 (by exact_mod_cast ht.symm)
  have : x * y * x = 0 := LinearMap.congr_fun (LinearMap.range_eq_bot.1 hr) x
  rwa [hy] at this

theorem trBd : TrBd := by
  intro F _ _ κ _
  let B : V F κ →ₗ[ℝ] V F κ →ₗ[ℝ] ℝ := LinearMap.mk₂ ℝ
    (fun x b => Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (x ⬝ᵥ b))
    (fun x x' b => by rw [add_dotProduct, map_add (f := _)]) (fun c x b => by rw [smul_dotProduct, map_smul])
    (fun x b b' => by rw [dotProduct_add, map_add (f := _)]) (fun c x b => by rw [dotProduct_smul, map_smul])
  let A : V F κ →ₗ[ℝ] V F κ →L[ℝ] ℝ := (LinearMap.toContinuousLinearMap : (V F κ →ₗ[ℝ] ℝ) ≃ₗ[ℝ] _).toLinearMap ∘ₗ B
  have hA : LinearMap.ker A = ⊥ := by
    refine LinearMap.ker_eq_bot'.2 fun x hx => funext fun i => ?_
    by_contra hi
    obtain ⟨y, hy⟩ := exists_trace_ne (x i) hi
    have : Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (x ⬝ᵥ Pi.single i y) = 0 :=
      congrArg (fun T : V F κ →L[ℝ] ℝ => T (Pi.single i y)) hx
    rw [dotProduct_single] at this
    exact hy this
  obtain ⟨K, -, hK⟩ := A.exists_antilipschitzWith hA
  refine ⟨2 * K, by positivity, fun x => ?_⟩
  have h1 : ‖x‖ ≤ K * ‖A x‖ := ZeroHomClass.bound_of_antilipschitz A hK x
  by_cases h0 : ‖A x‖ = 0
  · refine ⟨0, by simp, ?_⟩
    rw [h0, mul_zero] at h1
    exact h1.trans (by positivity)
  · have hp : 0 < ‖A x‖ := (norm_nonneg _).lt_of_ne' h0
    obtain ⟨b, hb, hb'⟩ := (A x).exists_lt_apply_of_lt_opNorm (r := ‖A x‖ / 2) (by linarith)
    refine ⟨b, hb.le, h1.trans ?_⟩
    have h2 : ‖A x‖ / 2 < |Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (x ⬝ᵥ b)| := hb'
    have h3 : (0 : ℝ) ≤ K := K.2
    nlinarith

end PositivityTheory.ThKF0.Grow
end
end

