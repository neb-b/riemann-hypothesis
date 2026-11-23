module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.GermIntegrals.StepSt

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.PointAveraging.MinkowskiBalls.GermUnique
section
open MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL ValuativeRel PositivityTheory.Tls2.Ming3
open scoped Topology Pointwise

set_option linter.unusedSectionVars false

noncomputable section

namespace PositivityTheory.Rg.Ming.UniqX

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem valSet_eq (a : k) (c : kˣ) :
    {y : k | valuation k (y - a) ≤ valuation k (c : k)} = (fun y => -a + y) ⁻¹' (c • (𝒪[k] : Set k)) := by
  ext y
  have hc : 0 < valuation k (c : k) := by
    rw [zero_lt_iff]; simp
  simp only [Set.mem_setOf_eq, Set.mem_preimage]
  rw [Set.mem_smul_set_iff_inv_smul_mem, SetLike.mem_coe, Valuation.mem_integer_iff, Units.smul_def,
    Units.val_inv_eq_inv_val, smul_eq_mul, map_mul, map_inv₀, neg_add_eq_sub, inv_mul_le_one₀ hc]

theorem isOpen_valSet (a : k) (c : kˣ) : IsOpen {y : k | valuation k (y - a) ≤ valuation k (c : k)} := by
  rw [valSet_eq]
  exact (Valuation.isOpen_integer.smul c).preimage (continuous_const.add continuous_id)

theorem vol_valSet [MeasurableSpace k] [BorelSpace k] (ν : Measure k) (hν : IsUnitVol ν) (a : k) (c : kˣ) :
    ν {y : k | valuation k (y - a) ≤ valuation k (c : k)} = ENNReal.ofReal (nabs k c) := by
  obtain ⟨hH, h1⟩ := hν
  haveI := hH
  haveI : SecondCountableTopology k := by exact secondCountable k
  rw [valSet_eq, measure_preimage_add, ← distribHaarChar_mul, h1, mul_one, nabs, ENNReal.ofReal_coe_nnreal]

variable {n r : ℕ}

theorem ballM_eq_pi (c : kˣ) (x₀ : Matrix (Fin n) (Fin r) k) :
    (ballM c x₀ : Set (Matrix (Fin n) (Fin r) k)) =
      (Set.univ.pi fun i => Set.univ.pi fun l => {y : k | valuation k (y - x₀ i l) ≤ valuation k (c : k)} :
        Set (Fin n → Fin r → k)) := by
  ext x
  simp only [ballM, Set.mem_setOf_eq]
  constructor
  · intro h i _ l _
    exact h i l
  · intro h i l
    exact h i (Set.mem_univ _) l (Set.mem_univ _)

theorem measurableSet_ballM [MeasurableSpace k] [BorelSpace k] (c : kˣ) (x₀ : Matrix (Fin n) (Fin r) k) :
    MeasurableSet (ballM c x₀) := by
  rw [ballM_eq_pi]
  exact MeasurableSet.univ_pi fun i => MeasurableSet.univ_pi fun l => (isOpen_valSet _ c).measurableSet

theorem volM_ballM [MeasurableSpace k] [BorelSpace k] (ν : Measure k) (hν : IsUnitVol ν) (c : kˣ)
    (x₀ : Matrix (Fin n) (Fin r) k) :
    volM ν (Fin n) (Fin r) (ballM c x₀) = ∏ _i : Fin n, ∏ _l : Fin r, ENNReal.ofReal (nabs k c) := by
  obtain ⟨hH, h1⟩ := hν
  haveI := hH
  haveI : SecondCountableTopology k := by exact secondCountable k
  rw [volM, ballM_eq_pi]
  erw [Measure.pi_pi]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Measure.pi_pi]
  exact Finset.prod_congr rfl fun l _ => vol_valSet ν ⟨hH, h1⟩ (x₀ i l) c

theorem volM_ballM_ne_zero [MeasurableSpace k] [BorelSpace k] (ν : Measure k) (hν : IsUnitVol ν) (c : kˣ)
    (x₀ : Matrix (Fin n) (Fin r) k) : (volM ν (Fin n) (Fin r) (ballM c x₀)).toReal ≠ 0 := by
  have hpos : 0 < nabs k c := by
    unfold nabs
    have h : distribHaarChar k c * distribHaarChar k c⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel, map_one]
    have hne : distribHaarChar k c ≠ 0 := left_ne_zero_of_mul_eq_one h
    exact_mod_cast pos_iff_ne_zero.2 hne
  rw [volM_ballM ν hν, ENNReal.toReal_prod]
  refine Finset.prod_ne_zero_iff.2 fun i _ => ?_
  rw [ENNReal.toReal_prod]
  refine Finset.prod_ne_zero_iff.2 fun l _ => ?_
  rw [ENNReal.toReal_ofReal hpos.le]
  exact hpos.ne'

theorem integral_ind [MeasurableSpace k] [BorelSpace k] (ν : Measure k) (c : kˣ) (x₀ : Matrix (Fin n) (Fin r) k) :
    ∫ x, (ballM c x₀).indicator (fun _ => (1 : ℂ)) x ∂volM ν (Fin n) (Fin r) =
      ((volM ν (Fin n) (Fin r) (ballM c x₀)).toReal : ℂ) := by
  rw [integral_indicator_const _ (measurableSet_ballM c x₀)]
  simp [Measure.real]

theorem ballM_mono {c c' : kˣ} (hle : valuation k (c : k) ≤ valuation k (c' : k))
    {x₀ : Matrix (Fin n) (Fin r) k} : ballM c x₀ ⊆ ballM c' x₀ :=
  fun _ hx i l => (hx i l).trans hle

theorem exists_le_both (c₁ c₂ : kˣ) :
    ∃ c : kˣ, valuation k (c : k) ≤ valuation k (c₁ : k) ∧ valuation k (c : k) ≤ valuation k (c₂ : k) := by
  rcases le_total (valuation k (c₁ : k)) (valuation k (c₂ : k)) with h | h
  · exact ⟨c₁, le_rfl, h⟩
  · exact ⟨c₂, h, le_rfl⟩

variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem germ_zero [MeasurableSpace k] (ν : Measure k) (B : SB (Matrix (Fin n) (Fin r) k) →ₗ[ℂ] W →ₗ[ℂ] V)
    (x₀ : Matrix (Fin n) (Fin r) k) : IsGerm ν B x₀ 0 0 :=
  ⟨1, fun Φ _ => by simp⟩

theorem germ_comb [MeasurableSpace k] (ν : Measure k) (B : SB (Matrix (Fin n) (Fin r) k) →ₗ[ℂ] W →ₗ[ℂ] V)
    (x₀ : Matrix (Fin n) (Fin r) k) (a : ℂ) {w₁ w₂ : W} {v₁ v₂ : V}
    (h₁ : IsGerm ν B x₀ w₁ v₁) (h₂ : IsGerm ν B x₀ w₂ v₂) : IsGerm ν B x₀ (a • w₁ + w₂) (a • v₁ + v₂) := by
  obtain ⟨c₁, e₁⟩ := h₁
  obtain ⟨c₂, e₂⟩ := h₂
  obtain ⟨c, hc₁, hc₂⟩ := exists_le_both c₁ c₂
  refine ⟨c, fun Φ hΦ => ?_⟩
  rw [map_add (f := _), map_smul, e₁ Φ (fun x hx => ballM_mono hc₁ (hΦ x hx)),
    e₂ Φ (fun x hx => ballM_mono hc₂ (hΦ x hx)), smul_add, smul_comm a]

theorem germ_unique (hb : BallSt) [MeasurableSpace k] [BorelSpace k] (ν : Measure k) (hν : IsUnitVol ν)
    (B : SB (Matrix (Fin n) (Fin r) k) →ₗ[ℂ] W →ₗ[ℂ] V) (x₀ : Matrix (Fin n) (Fin r) k) {w : W} {v₁ v₂ : V}
    (h₁ : IsGerm ν B x₀ w v₁) (h₂ : IsGerm ν B x₀ w v₂) : v₁ = v₂ := by
  obtain ⟨c₁, hc₁⟩ := h₁
  obtain ⟨c₂, hc₂⟩ := h₂
  obtain ⟨c, hle₁, hle₂⟩ := exists_le_both c₁ c₂
  let Φ : SB (Matrix (Fin n) (Fin r) k) :=
    ⟨(ballM c x₀).indicator fun _ => (1 : ℂ), ((hb k n r).1 c x₀).2.2.1⟩
  have hsupp : ∀ x, (Φ : Matrix (Fin n) (Fin r) k → ℂ) x ≠ 0 → x ∈ ballM c x₀ := by
    intro x hx
    by_contra h
    exact hx (by simp [Φ, Set.indicator, h])
  have e₁ := hc₁ Φ fun x hx => ballM_mono hle₁ (hsupp x hx)
  have e₂ := hc₂ Φ fun x hx => ballM_mono hle₂ (hsupp x hx)
  have hI : (∫ x, (Φ : Matrix (Fin n) (Fin r) k → ℂ) x ∂volM ν (Fin n) (Fin r)) ≠ 0 := by
    change (∫ x, (ballM c x₀).indicator (fun _ => (1 : ℂ)) x ∂volM ν (Fin n) (Fin r)) ≠ 0
    rw [integral_ind]
    exact Complex.ofReal_ne_zero.2 (volM_ballM_ne_zero ν hν c x₀)
  exact smul_right_injective V hI (e₁.symm.trans e₂)

end PositivityTheory.Rg.Ming.UniqX

namespace PositivityTheory.Rg.Ming

open PositivityTheory.Rg.Ming.UniqX in
theorem uniq : BallSt → UniqSt := by
  intro hb
  unfold UniqSt
  intro k _ _ _ _ _ _ ν hν n r V _ _ W _ _ B x₀ hex
  choose f hf using hex
  have hadd : ∀ w₁ w₂ : W, f (w₁ + w₂) = f w₁ + f w₂ := by
    intro w₁ w₂
    have h := germ_comb ν B x₀ 1 (hf w₁) (hf w₂)
    rw [one_smul, one_smul] at h
    exact germ_unique hb ν hν B x₀ (hf (w₁ + w₂)) h
  have hsmul : ∀ (a : ℂ) (w : W), f (a • w) = a • f w := by
    intro a w
    have h := germ_comb ν B x₀ a (hf w) (germ_zero ν B x₀)
    rw [add_zero, add_zero] at h
    exact germ_unique hb ν hν B x₀ (hf (a • w)) h
  refine ⟨{ toFun := f, map_add' := hadd, map_smul' := hsmul }, fun w v => ?_⟩
  constructor
  · intro h
    exact germ_unique hb ν hν B x₀ h (hf w)
  · rintro rfl
    exact hf w

end PositivityTheory.Rg.Ming

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.PointAveraging.MinkowskiBalls.IsCompactSupportSB
section
open MeasureTheory GlobalTheory.SplitWeil ValuativeRel PositivityTheory.Tls2.Ming3

namespace PositivityTheory.Rg.Ming

set_option linter.unusedSectionVars false

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n r : ℕ}

theorem ballM_mono_loc {c c' : kˣ} (h : valuation k (c : k) ≤ valuation k (c' : k))
    (x : Matrix (Fin n) (Fin r) k) : ballM c x ⊆ ballM c' x :=
  fun _ hy i l => (hy i l).trans h

theorem mem_ballM_self_loc (c : kˣ) (x : Matrix (Fin n) (Fin r) k) : x ∈ ballM c x := by
  intro i l
  simp

theorem isCompact_support_SB (Φ : SB (Matrix (Fin n) (Fin r) k)) :
    IsCompact (Function.support Φ.1) := by
  obtain ⟨hlc, hcs⟩ : IsLocallyConstant Φ.1 ∧ HasCompactSupport Φ.1 := Φ.2
  refine IsCompact.of_isClosed_subset hcs ?_ (subset_tsupport _)
  have h := (hlc.isClopen_fiber 0).isOpen
  rw [← isOpen_compl_iff]
  convert h using 1
  ext x
  simp [Function.mem_support]

theorem loc (hB : BallSt) : LocSt := by
  intro k _ _ _ _ n r P Φ hΦ
  obtain ⟨hball, hsmall, hdec⟩ := hB k n r
  have hpick : ∀ x : {x // (Φ : Matrix (Fin n) (Fin r) k → ℂ) x ≠ 0}, ∃ c : kˣ,
      ∀ Ψ : SB (Matrix (Fin n) (Fin r) k),
        (∀ y, (Ψ : Matrix (Fin n) (Fin r) k → ℂ) y ≠ 0 →
          y ∈ ballM c x.1 ∧ (Φ : Matrix (Fin n) (Fin r) k → ℂ) y ≠ 0) → Ψ ∈ P := by
    intro x
    obtain ⟨U, hU, hxU, hP⟩ := hΦ x.1 x.2
    obtain ⟨c, -, hc⟩ := hsmall x.1 U (hU.mem_nhds hxU)
    exact ⟨c, fun Ψ hΨ => hP Ψ fun y hy => ⟨hc (hΨ y hy).1, (hΨ y hy).2⟩⟩
  choose cs hcs using hpick
  obtain ⟨t, ht⟩ := (isCompact_support_SB Φ).elim_finite_subcover
    (fun x => ballM (cs x) x.1) (fun x => (hball (cs x) x.1).1)
    (fun x hx => Set.mem_iUnion.2 ⟨⟨x, hx⟩, mem_ballM_self_loc _ _⟩)
  obtain ⟨c₀, hc₀⟩ := hdec Φ
  have hmin : ∀ s : Finset {x // (Φ : Matrix (Fin n) (Fin r) k → ℂ) x ≠ 0}, ∃ c : kˣ,
      valuation k (c : k) ≤ valuation k (c₀ : k) ∧
        ∀ i ∈ s, valuation k (c : k) ≤ valuation k (cs i : k) := by
    intro s
    classical
    refine Finset.induction_on s ⟨c₀, le_rfl, by simp⟩ ?_
    intro a s _ ih
    obtain ⟨c, hc1, hc2⟩ := ih
    rcases le_total (valuation k (c : k)) (valuation k (cs a : k)) with h | h
    · refine ⟨c, hc1, ?_⟩
      intro i hi
      rcases Finset.mem_insert.1 hi with rfl | hi
      · exact h
      · exact hc2 i hi
    · refine ⟨cs a, h.trans hc1, ?_⟩
      intro i hi
      rcases Finset.mem_insert.1 hi with rfl | hi
      · exact le_rfl
      · exact h.trans (hc2 i hi)
  obtain ⟨c, hcc₀, hcci⟩ := hmin t
  obtain ⟨S, hS, hsum⟩ := hc₀ c hcc₀
  have hind : ∀ x, ((ballM c x).indicator fun _ => (1 : ℂ)) ∈ SB (Matrix (Fin n) (Fin r) k) :=
    fun x => (hball c x).2.2.1
  have hterm : ∀ x ∈ S, (Φ : Matrix (Fin n) (Fin r) k → ℂ) x •
      (⟨_, hind x⟩ : SB (Matrix (Fin n) (Fin r) k)) ∈ P := by
    intro x hx
    have hx0 : (Φ : Matrix (Fin n) (Fin r) k → ℂ) x ≠ 0 := (hS x hx x (mem_ballM_self_loc c x)).2
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.1 (ht (show x ∈ Function.support (Φ : Matrix (Fin n) (Fin r) k → ℂ) from hx0))
    have hsub : ballM c x ⊆ ballM (cs i) i.1 := by
      rw [← (hball (cs i) i.1).2.2.2.1 x hxi]
      exact ballM_mono_loc (hcci i hi) x
    apply P.smul_mem
    apply hcs i
    intro y hy
    have hy' : y ∈ ballM c x := by
      by_contra hn
      exact hy (by simp [Set.indicator, hn])
    exact ⟨hsub hy', by rw [(hS x hx y hy').1]; exact hx0⟩
  have hΦeq : Φ = ∑ x ∈ S, (Φ : Matrix (Fin n) (Fin r) k → ℂ) x •
      (⟨_, hind x⟩ : SB (Matrix (Fin n) (Fin r) k)) := by
    apply Subtype.ext
    refine hsum.trans ?_
    simp [Submodule.coe_sum, Submodule.coe_smul]
  rw [hΦeq]
  exact P.sum_mem hterm

end PositivityTheory.Rg.Ming
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.PointAveraging.MinkowskiBalls.MemBallMSelf
section
open MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL ValuativeRel PositivityTheory.Tls2.Ming3

namespace PositivityTheory.Rg.Ming.StepX

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n r : ℕ}

theorem isUnit_det_val {m : ℕ} (h : GL (Fin m) k) : IsUnit h.val.det := by
  exact (Matrix.isUnit_iff_isUnit_det h.val).mp h.isUnit

theorem rank_conj (h : GL (Fin n) k) (g : GL (Fin r) k) (x : Matrix (Fin n) (Fin r) k) :
    (h.val * x * g.val).rank = x.rank := by
  rw [Matrix.rank_mul_eq_left_of_isUnit_det _ _ (isUnit_det_val g),
    Matrix.rank_mul_eq_right_of_isUnit_det _ _ (isUnit_det_val h)]

theorem conj_cancel (h : GL (Fin n) k) (g : GL (Fin r) k) (x : Matrix (Fin n) (Fin r) k) :
    (h⁻¹ : GL (Fin n) k).val * (h.val * x * g.val) * (g⁻¹ : GL (Fin r) k).val = x := by
  simp [← Matrix.mul_assoc]

theorem conj_cancel' (h : GL (Fin n) k) (g : GL (Fin r) k) (x : Matrix (Fin n) (Fin r) k) :
    h.val * ((h⁻¹ : GL (Fin n) k).val * x * (g⁻¹ : GL (Fin r) k).val) * g.val = x := by
  simp [← Matrix.mul_assoc]

theorem mem_ballM_self (c : kˣ) (x : Matrix (Fin n) (Fin r) k) : x ∈ ballM c x := by
  intro i l
  simp

theorem tr_mem (h : GL (Fin n) k) (g : GL (Fin r) k) (Ψ : SB (Matrix (Fin n) (Fin r) k)) :
    (fun y => Ψ.1 (h.val * y * g.val)) ∈ SB (Matrix (Fin n) (Fin r) k) := by
  let e : Matrix (Fin n) (Fin r) k ≃ₜ Matrix (Fin n) (Fin r) k :=
    { toFun := fun y => h.val * y * g.val
      invFun := fun y => (h⁻¹ : GL (Fin n) k).val * y * (g⁻¹ : GL (Fin r) k).val
      left_inv := fun y => conj_cancel h g y
      right_inv := fun y => conj_cancel' h g y
      continuous_toFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
      continuous_invFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const }
  obtain ⟨h1, h2⟩ := Ψ.2
  exact ⟨h1.comp_continuous e.continuous, h2.comp_homeomorph e⟩

variable {μ : kˣ →* ℂˣ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  {σ : Representation ℂ (GL (Fin r) k) V} {π : Representation ℂ (GL (Fin n) k) W}
  {B : SB (Matrix (Fin n) (Fin r) k) →ₗ[ℂ] W →ₗ[ℂ] V}

theorem kill (hE : Equi μ σ π B) (h : GL (Fin n) k) (g : GL (Fin r) k)
    (Φ Ψ : SB (Matrix (Fin n) (Fin r) k)) (hΨ : ∀ y, Ψ.1 y = Φ.1 (h.val * y * g.val))
    (hΦ : B Φ = 0) : B Ψ = 0 := by
  apply LinearMap.ext
  intro F
  rw [LinearMap.zero_apply]
  let Φ' : SB (Matrix (Fin n) (Fin r) k) := ⟨om μ g⁻¹ h Ψ.1, om_mem_SB μ g⁻¹ h Ψ.2⟩
  have hΦ' : Φ' = om μ g⁻¹ h (fun _ => (1 : ℂ)) 0 • Φ := by
    apply Subtype.ext
    funext y
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
    show om μ g⁻¹ h Ψ.1 y = om μ g⁻¹ h (fun _ => (1 : ℂ)) 0 * Φ.1 y
    simp only [om]
    rw [hΨ, conj_cancel', mul_one]
  have h1 := hE g⁻¹ h Ψ Φ' rfl F
  rw [hΦ', map_smul, hΦ, smul_zero, LinearMap.zero_apply] at h1
  have h3 := congrArg (σ g) h1
  rw [map_zero, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at h3
  exact h3.symm

theorem key (hball : BallSt) (hnf : NfSt) (hcore : CoreSt) {j : ℕ} (hj : j < r) (hjn : 2 * j < n)
    (hμ : IsUnitaryChar μ) (hσ : IsUnitarisable σ) (hE : Equi μ σ π B) (hV : VanRk B (j + 1))
    (c : kˣ) (hc : valuation k (c : k) < 1) (Ψ : SB (Matrix (Fin n) (Fin r) k))
    (hsupp : ∀ y, Ψ.1 y ≠ 0 → y ∈ ballM c (idem k r n j))
    (hvan : ∀ y : Matrix (Fin n) (Fin r) k, y.rank < j → Ψ.1 y = 0) : B Ψ = 0 := by
  obtain ⟨hB1, -, hB3⟩ := hball k n r
  obtain ⟨c₀, hc₀⟩ := hB3 Ψ
  obtain ⟨c', hc'1, hc'0⟩ : ∃ c' : kˣ, valuation k (c' : k) < 1 ∧ valuation k (c' : k) ≤ valuation k (c₀ : k) := by
    by_cases h0 : valuation k (c₀ : k) < 1
    · exact ⟨c₀, h0, le_rfl⟩
    · exact ⟨c, hc, le_of_lt (lt_of_lt_of_le hc (not_lt.mp h0))⟩
  obtain ⟨S, hS, hsum⟩ := hc₀ c' hc'0
  have hind : ∀ x₀ : Matrix (Fin n) (Fin r) k,
      ((ballM c' x₀).indicator fun _ => (1 : ℂ)) ∈ SB (Matrix (Fin n) (Fin r) k) :=
    fun x₀ => (hB1 c' x₀).2.2.1
  have hpiece : ∀ x ∈ S, B ⟨_, hind x⟩ = 0 := by
    intro x hx
    by_cases hr : ∃ y ∈ ballM c' x, y.rank = j
    · obtain ⟨y, hy, hyr⟩ := hr
      have hball_eq : ballM c' y = ballM c' x := (hB1 c' x).2.2.2.1 y hy
      have hyS : y ∈ ballM c (idem k r n j) := by
        apply hsupp
        rw [(hS x hx y hy).1]
        exact (hS x hx y hy).2
      obtain ⟨h, hh, g, hg, hye⟩ := (hnf k n r j y hyr).2 c hc hyS
      have hcore' : B ⟨_, hind (idem k r n j)⟩ = 0 :=
        hcore k n r μ V W σ π B j hj hjn hμ hσ hE hV c' hc'1 _ rfl
      refine kill hE h⁻¹ g⁻¹ ⟨_, hind (idem k r n j)⟩ ⟨_, hind x⟩ (fun z => ?_) hcore'
      show (ballM c' x).indicator (fun _ => (1 : ℂ)) z = (ballM c' (idem k r n j)).indicator (fun _ => (1 : ℂ))
        ((h⁻¹ : GL (Fin n) k).val * z * (g⁻¹ : GL (Fin r) k).val)
      have hiff : (h⁻¹ : GL (Fin n) k).val * z * (g⁻¹ : GL (Fin r) k).val ∈ ballM c' (idem k r n j) ↔
          z ∈ ballM c' x := by
        have h4 := (hB1 c' y).2.2.2.2 h⁻¹ (inv_mem hh) g⁻¹ (inv_mem hg) z
        rw [hball_eq, hye, conj_cancel] at h4
        exact h4
      by_cases hz : z ∈ ballM c' x
      · rw [Set.indicator_of_mem hz, Set.indicator_of_mem (hiff.mpr hz)]
      · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem (fun h' => hz (hiff.mp h'))]
    · push_neg at hr
      apply hV
      intro z hz
      show (ballM c' x).indicator (fun _ => (1 : ℂ)) z = 0
      apply Set.indicator_of_notMem
      intro hzx
      have hne : Ψ.1 z ≠ 0 := by
        rw [(hS x hx z hzx).1]
        exact (hS x hx z hzx).2
      have h1 : j ≤ z.rank := by
        by_contra hl
        exact hne (hvan z (lt_of_not_ge hl))
      have h2 := hr z hzx
      omega
  have hΨeq : Ψ = ∑ x ∈ S, Ψ.1 x • (⟨_, hind x⟩ : SB (Matrix (Fin n) (Fin r) k)) := by
    apply Subtype.ext
    rw [Submodule.coe_sum]
    simp only [Submodule.coe_smul]
    exact hsum
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hΨeq, map_sum]
  apply Finset.sum_eq_zero
  intro x hx
  rw [map_smul, hpiece x hx, smul_zero]

end PositivityTheory.Rg.Ming.StepX

namespace PositivityTheory.Rg.Ming

open PositivityTheory.Rg.Ming.StepX

theorem step : BallSt → LocSt → NfSt → RkSt → CoreSt → StepSt := by
  intro hBall hLoc hNf hRk hCore
  intro k _ _ _ _ n r μ V _ _ W _ _ σ π B j hj hjn hμ hσ hE hV
  intro Φ hΦ
  have hPker : Φ ∈ LinearMap.ker B := by
    apply hLoc k n r (LinearMap.ker B) Φ
    intro x hx
    obtain ⟨m, hm⟩ : ∃ m, x.rank = m := ⟨_, rfl⟩
    have hjm : j ≤ m := by
      rw [← hm]
      by_contra hlt
      exact hx (hΦ x (lt_of_not_ge hlt))
    have hmn : m ≤ n := by
      rw [← hm]
      simpa using Matrix.rank_le_height x
    have hmr : m ≤ r := by
      rw [← hm]
      simpa using Matrix.rank_le_width x
    obtain ⟨⟨h, g, hxe⟩, -⟩ := hNf k n r m x hm
    obtain ⟨c, hc, -⟩ := (hBall k n r).2.1 (0 : Matrix (Fin n) (Fin r) k) Set.univ Filter.univ_mem
    refine ⟨{y | (h⁻¹ : GL (Fin n) k).val * y * (g⁻¹ : GL (Fin r) k).val ∈ ballM c (idem k r n m)}, ?_, ?_, ?_⟩
    · exact ((hBall k n r).1 c _).1.preimage
        ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const)
    · have e1 : (h⁻¹ : GL (Fin n) k).val * x * (g⁻¹ : GL (Fin r) k).val = idem k r n m := by
        rw [hxe]
        exact conj_cancel h g _
      simp only [Set.mem_setOf_eq]
      rw [e1]
      exact mem_ballM_self c _
    · intro Ψ hΨ
      rw [LinearMap.mem_ker]
      rcases eq_or_lt_of_le hjm with hjm' | hjm'
      · subst hjm'
        let Ψ' : SB (Matrix (Fin n) (Fin r) k) := ⟨fun y => Ψ.1 (h.val * y * g.val), tr_mem h g Ψ⟩
        have hsupp : ∀ y, Ψ'.1 y ≠ 0 → y ∈ ballM c (idem k r n j) := by
          intro y hy
          have hmem := (hΨ _ hy).1
          simp only [Set.mem_setOf_eq] at hmem
          rw [conj_cancel] at hmem
          exact hmem
        have hvan : ∀ y : Matrix (Fin n) (Fin r) k, y.rank < j → Ψ'.1 y = 0 := by
          intro y hy
          by_contra hne
          have h2 := (hΨ _ hne).2
          apply h2
          apply hΦ
          rw [rank_conj]
          exact hy
        have hB' : B Ψ' = 0 := key hBall hNf hCore hj hjn hμ hσ hE hV c hc Ψ' hsupp hvan
        refine kill hE h⁻¹ g⁻¹ Ψ' Ψ (fun y => ?_) hB'
        show Ψ.1 y = Ψ.1 (h.val * ((h⁻¹ : GL (Fin n) k).val * y * (g⁻¹ : GL (Fin r) k).val) * g.val)
        rw [conj_cancel']
      · apply hV Ψ
        intro y hy
        by_contra hne
        have hmem := (hΨ y hne).1
        simp only [Set.mem_setOf_eq] at hmem
        have h5 := hRk k n r m hmn hmr c hc _ hmem
        rw [rank_conj] at h5
        omega
  exact LinearMap.mem_ker.mp hPker

end PositivityTheory.Rg.Ming
end

