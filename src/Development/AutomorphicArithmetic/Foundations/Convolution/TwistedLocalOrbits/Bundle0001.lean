module

public import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.HoweSpace
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.Bundle0001
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.InvTransposeGLInvTransposeGL

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.BallSub
section
open ValuativeRel UpperTheory.ConvolutionTheory.Loc

section

variable {E : Type} [Field E] [ValuativeRel E] {n : ℕ}

private theorem bd_mul {a b : ValueGroupWithZero E} {M N : Matrix (Fin n) (Fin n) E} (h : ∀ i j, valuation E (M i j) ≤ a)
    (h' : ∀ i j, valuation E (N i j) ≤ b) (i j : Fin n) : valuation E ((M * N) i j) ≤ a * b := by
  rw [Matrix.mul_apply]
  refine Valuation.map_sum_le _ fun k _ => ?_
  rw [map_mul]
  exact mul_le_mul' (h i k) (h' k j)

private theorem bd_one (i j : Fin n) : valuation E ((1 : Matrix (Fin n) (Fin n) E) i j) ≤ 1 := by
  rw [Matrix.one_apply]
  split_ifs <;> simp

private theorem bd_inv {r : ValueGroupWithZero E} (hr : r < 1) {A H : Matrix (Fin n) (Fin n) E} (hA : ∀ i j, valuation E (A i j) ≤ r)
    (hH : H = 1 - H * A) (i j : Fin n) : valuation E (H i j) ≤ 1 := by
  obtain ⟨p, -, hp⟩ := Finset.exists_max_image Finset.univ (fun p : Fin n × Fin n => valuation E (H p.1 p.2)) ⟨(i, j), Finset.mem_univ _⟩
  refine (hp (i, j) (Finset.mem_univ _)).trans ?_
  by_contra hc
  push Not at hc
  have h1 := bd_mul (fun a b => hp (a, b) (Finset.mem_univ _)) hA p.1 p.2
  have h2 : valuation E ((H * A) p.1 p.2) < valuation E (H p.1 p.2) :=
    h1.trans_lt (mul_lt_of_lt_one_right (zero_lt_one.trans hc) hr)
  have h3 : valuation E ((1 - H * A) p.1 p.2) < valuation E (H p.1 p.2) :=
    Valuation.map_sub_lt _ ((bd_one _ _).trans_lt hc) h2
  rw [← hH] at h3
  exact lt_irrefl _ h3

end

theorem UpperTheory.ConvolutionTheory.Loc.ballSub :
    ∀ (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] (n : ℕ) (r : ValueGroupWithZero E), 0 < r → r < 1 →
      ∃ K : Subgroup (GL (Fin n) E), (K : Set (GL (Fin n) E)) = ball n r ∧ IsOpen (K : Set (GL (Fin n) E)) ∧ IsCompact (K : Set (GL (Fin n) E)) := by
  intro E _ _ _ _ n r h0 h1
  have mb : ∀ {g : GL (Fin n) E}, g ∈ ball n r → ∀ i j, valuation E (((g : Matrix (Fin n) (Fin n) E) - 1) i j) ≤ r := fun hg i j => hg i j
  have hinv : ∀ g ∈ ball (E := E) n r, g⁻¹ ∈ ball n r := by
    intro g hg i j
    have e : ((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) = 1 - (g⁻¹ : GL (Fin n) E) * ((g : Matrix (Fin n) (Fin n) E) - 1) := by
      rw [mul_sub, Units.inv_mul]; simp
    have h := bd_mul (bd_inv h1 (mb hg) e) (mb hg) i j
    rw [one_mul] at h
    rw [e, Matrix.sub_apply, sub_sub_cancel_left, Valuation.map_neg]
    exact h
  let K : Subgroup (GL (Fin n) E) :=
    { carrier := ball n r
      one_mem' := fun i j => by simp
      inv_mem' := fun {g} hg => hinv g hg
      mul_mem' := fun {a b} ha hb i j => by
        have e : ((a * b : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) - 1 =
            ((a : Matrix (Fin n) (Fin n) E) - 1) * ((b : Matrix (Fin n) (Fin n) E) - 1) + ((a : Matrix (Fin n) (Fin n) E) - 1) +
              ((b : Matrix (Fin n) (Fin n) E) - 1) := by
          rw [Units.val_mul]; noncomm_ring
        rw [← Matrix.sub_apply, e]
        refine Valuation.map_add_le _ (Valuation.map_add_le _ ?_ (ha i j)) (hb i j)
        exact (bd_mul (mb ha) (mb hb) i j).trans
          (mul_le_of_le_one_right' h1.le) }
  have hent : ∀ i j, Continuous fun g : GL (Fin n) E => (g : Matrix (Fin n) (Fin n) E) i j - (1 : Matrix (Fin n) (Fin n) E) i j :=
    fun i j => (Units.continuous_val.matrix_elem i j).sub continuous_const
  refine ⟨K, rfl, K.isOpen_of_mem_nhds (g := 1) ?_, ?_⟩
  · have hb : {x : E | valuation E x < r} ∈ nhds (0 : E) :=
      (IsValuativeTopology.mem_nhds_zero_iff _).2 ⟨Units.mk0 r h0.ne', subset_rfl⟩
    have : ∀ᶠ g : GL (Fin n) E in nhds 1, ∀ i j,
        valuation E ((g : Matrix (Fin n) (Fin n) E) i j - (1 : Matrix (Fin n) (Fin n) E) i j) < r := by
      refine Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => ?_
      exact (hent i j).continuousAt.preimage_mem_nhds (t := {x : E | valuation E x < r}) (by simpa using hb)
    exact this.mono fun g hg i j => (hg i j).le
  · have hc : IsCompact {M : Matrix (Fin n) (Fin n) E | ∀ i j, valuation E (M i j) ≤ r} :=
      isCompact_pi_infinite (s := fun _ : Fin n => {x : Fin n → E | ∀ j, x j ∈ {y | valuation E y ≤ r}})
        fun _ => isCompact_pi_infinite fun _ => IsNonarchimedeanLocalField.isCompact_closedBall E r
    have hc' := hc.image (f := fun M => M + 1) (by fun_prop)
    have h := (UpperTheory.V.Z.Tf.Orb.gLTop E n).2.2.2.2 _ _ hc' hc'
    convert h using 1
    ext g
    constructor
    · intro hg
      exact ⟨⟨_, mb hg, sub_add_cancel _ _⟩, ⟨_, mb (hinv g hg), sub_add_cancel _ _⟩⟩
    · rintro ⟨⟨M, hM, e⟩, -⟩ i j
      rw [← e]
      simpa using hM i j
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.HoweAvg
section
open GlobalTheory.PRep MeasureTheory

namespace UpperTheory.ConvolutionTheory.Loc

variable {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]

private theorem cont_coeff {ρ : Representation ℂ G V} (hρ : IsSmooth ρ) (l : V →ₗ[ℂ] ℂ) (w : V) :
    Continuous fun g : G => l (ρ g w) := by
  have h : IsLocallyConstant fun g : G => ρ g w := by
    rw [IsLocallyConstant.iff_exists_open]
    intro x
    refine ⟨(fun g => x⁻¹ * g) ⁻¹' {g | ρ g w = w}, (hρ w).preimage (continuous_const.mul continuous_id), by simp, ?_⟩
    intro y hy
    have hy' : ρ (x⁻¹ * y) w = w := hy
    calc ρ y w = ρ x (ρ (x⁻¹ * y) w) := by
          rw [← mul_apply_eq_comp, ← map_mul, mul_inv_cancel_left]
      _ = ρ x w := by rw [hy']
  exact (h.comp l).continuous

open Classical in
private theorem avg {ρ : Representation ℂ G V} (hρ : IsSmooth ρ) (C : Subgroup G) (hC : IsCompact (C : Set G))
    (θ : G → ℂ) (hθ : Continuous θ) (hmul : ∀ a ∈ C, ∀ b ∈ C, θ (a * b) = θ a * θ b) (l : V →ₗ[ℂ] ℂ) (v : V)
    (S : Set G) (hS : IsOpen S) (h1 : 1 ∈ S) (hv : ∀ c ∈ C, θ c * l (ρ c⁻¹ v) = if c ∈ S then 1 else 0) :
    ∃ l' : V →ₗ[ℂ] ℂ, (∀ c ∈ C, ∀ w, l' (ρ c w) = θ c * l' w) ∧ l' v = 1 := by
  haveI : CompactSpace C := isCompact_iff_compactSpace.1 hC
  letI : MeasurableSpace C := borel C
  haveI : BorelSpace C := ⟨rfl⟩
  let μ : Measure C := Measure.haar
  have hc : ∀ w, Continuous fun c : C => θ c * l (ρ (c : G)⁻¹ w) := fun w =>
    (hθ.comp continuous_subtype_val).mul ((cont_coeff hρ l w).comp continuous_subtype_val.inv)
  have hi : ∀ w, Integrable (fun c : C => θ c * l (ρ (c : G)⁻¹ w)) μ := fun w =>
    (hc w).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  let L : V →ₗ[ℂ] ℂ :=
    { toFun := fun w => ∫ c : C, θ c * l (ρ (c : G)⁻¹ w) ∂μ
      map_add' := fun a b => by
        rw [← integral_add (hi a) (hi b)]
        simp only [map_add (f := _), mul_add]
      map_smul' := fun t a => by
        simp only [map_smul, smul_eq_mul, RingHom.id_apply]
        rw [← integral_const_mul]
        congr 1
        funext c
        ring }
  have hL : ∀ c ∈ C, ∀ w, L (ρ c w) = θ c * L w := by
    intro c hc w
    change ∫ x : C, θ x * l (ρ (x : G)⁻¹ (ρ c w)) ∂μ = θ c * ∫ x : C, θ x * l (ρ (x : G)⁻¹ w) ∂μ
    rw [← integral_const_mul, ← integral_mul_left_eq_self _ (⟨c, hc⟩ : C)]
    congr 1
    funext x
    simp only [Subgroup.coe_mul, Subtype.coe_mk]
    rw [hmul c hc x x.2, ← mul_apply_eq_comp, ← map_mul, mul_inv_rev, inv_mul_cancel_right, mul_assoc]
  have hT : IsOpen ((Subtype.val : C → G) ⁻¹' S) := hS.preimage continuous_subtype_val
  have hLv : L v = (μ.real ((Subtype.val : C → G) ⁻¹' S) : ℂ) := by
    change ∫ x : C, θ x * l (ρ (x : G)⁻¹ v) ∂μ = _
    have : (fun x : C => θ x * l (ρ (x : G)⁻¹ v)) = ((Subtype.val : C → G) ⁻¹' S).indicator fun _ => (1 : ℂ) := by
      funext x
      rw [hv x x.2, Set.indicator_apply]
      rfl
    rw [this, integral_indicator_const _ hT.measurableSet]
    simp
  have hne : L v ≠ 0 := by
    rw [hLv, Complex.ofReal_ne_zero, measureReal_ne_zero_iff (measure_ne_top _ _)]
    exact hT.measure_ne_zero μ ⟨1, h1⟩
  refine ⟨(L v)⁻¹ • L, fun c hc w => ?_, ?_⟩
  · simp only [LinearMap.smul_apply, hL c hc, smul_eq_mul]
    ring
  · simp [hne]

theorem eq_zero_of_no_intertwining {ρ : Representation ℂ G V} (hρ : IsSmooth ρ) (K N : Subgroup G)
    (hK : IsCompact (K : Set G)) (hK' : IsOpen (K : Set G))
    (hN : ∀ F : Finset G, (∀ u ∈ F, u ∈ N) → ∃ C : Subgroup G, IsCompact (C : Set G) ∧ C ≤ N ∧ ∀ u ∈ F, u ∈ C)
    (χ : G → ℂ) (hχ : Continuous χ) (hmul : ∀ a ∈ N, ∀ b ∈ N, χ (a * b) = χ a * χ b)
    (hint : ∀ u ∈ N, u ∉ K → ∃ k ∈ K, u * k * u⁻¹ ∈ K ∧ χ (u * k * u⁻¹) ≠ χ k)
    (v : V) (hv : ∀ k ∈ K, ρ k v = χ k • v)
    (hker : v ∈ Submodule.span ℂ {w | ∃ u ∈ N, ∃ x, w = ρ u x - χ u • x}) : v = 0 := by
  classical
  by_contra h0
  obtain ⟨l₀, hl₀⟩ := Module.Projective.exists_dual_eq_one ℂ h0
  have hK1 : ∀ k ∈ K, χ k = l₀ (ρ k v) := fun k hk => by rw [hv k hk, map_smul, hl₀, smul_eq_mul, mul_one]
  have hKmul : ∀ a ∈ K, ∀ b ∈ K, χ (a * b) = χ a * χ b := fun a ha b hb => by
    rw [hK1 _ (K.mul_mem ha hb), map_mul, mul_apply_eq_comp, hv b hb, map_smul, map_smul, ← hK1 a ha, smul_eq_mul,
      mul_comm]
  have hinv : ∀ a ∈ K, χ a * χ a⁻¹ = 1 := fun a ha => by
    rw [← hKmul a ha _ (K.inv_mem ha), mul_inv_cancel, hK1 1 K.one_mem, map_one, one_apply_eq_self, hl₀]
  obtain ⟨l₁, hl₁, hl₁v⟩ := avg hρ K hK χ hχ hKmul l₀ v Set.univ isOpen_univ trivial (fun c hc => by
    rw [← hK1 _ (K.inv_mem hc), hinv c hc]; simp)
  have hF : ∃ F : Finset G, (∀ u ∈ F, u ∈ N) ∧
      ∀ l' : V →ₗ[ℂ] ℂ, (∀ c ∈ F, ∀ w, l' (ρ c w) = χ c * l' w) → l' v = 0 := by
    clear hl₁v hv hK1 hl₀ h0
    induction hker using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨u, hu, x, rfl⟩ := hw
      exact ⟨{u}, by simpa using hu, fun l' h => by simp [h u (by simp)]⟩
    | zero => exact ⟨∅, by simp, by simp⟩
    | add a b _ _ ha hb =>
      obtain ⟨F, hF, h⟩ := ha
      obtain ⟨F', hF', h'⟩ := hb
      refine ⟨F ∪ F', fun u hu => (Finset.mem_union.1 hu).elim (hF u) (hF' u), fun l' hl => ?_⟩
      rw [map_add (f := _), h l' fun c hc => hl c (Finset.mem_union_left _ hc), h' l' fun c hc => hl c (Finset.mem_union_right _ hc),
        add_zero]
    | smul t a _ ha =>
      obtain ⟨F, hF, h⟩ := ha
      exact ⟨F, hF, fun l' hl => by rw [map_smul, h l' hl, smul_zero]⟩
  obtain ⟨F, hFN, hF⟩ := hF
  obtain ⟨C, hC, hCN, hFC⟩ := hN F hFN
  obtain ⟨l₂, hl₂, hl₂v⟩ := avg hρ C hC χ hχ (fun a ha b hb => hmul a (hCN ha) b (hCN hb)) l₁ v K hK' K.one_mem
    (fun c hc => by
      by_cases hcK : c ∈ K
      · rw [ite_eq_left (by exact hcK), hv _ (K.inv_mem hcK), map_smul, hl₁v, smul_eq_mul, mul_one, hinv c hcK]
      · rw [ite_eq_right (by exact hcK)]
        obtain ⟨k, hk, hk', hne⟩ := hint c⁻¹ (N.inv_mem (hCN hc)) (fun h => hcK (by simpa using K.inv_mem h))
        have h1 := hl₁ _ hk' (ρ c⁻¹ v)
        rw [← mul_apply_eq_comp, ← map_mul, inv_mul_cancel_right, map_mul, mul_apply_eq_comp, hv k hk, map_smul,
          map_smul, smul_eq_mul] at h1
        rw [(mul_eq_mul_right_iff.1 h1).resolve_left hne.symm, mul_zero])
  exact one_ne_zero (hl₂v.symm.trans (hF l₂ fun c hc => hl₂ c (hFC c hc)))

end UpperTheory.ConvolutionTheory.Loc
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.Match
section
open MeasureTheory ValuativeRel GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets PositivityTheory.Rg.Tf.Loc

noncomputable section

namespace UpperTheory.ConvolutionTheory.Loc

variable {k E : Type} [Field k] [Field E] [Algebra k E] {n : ℕ} [TopologicalSpace k] [TopologicalSpace E]
  [MeasurableSpace (GL (Fin n) E)] [MeasurableSpace (GL (Fin n) k)]

def Match (σ : E ≃ₐ[k] E) (μE : Measure (GL (Fin n) E)) (μk : Measure (GL (Fin n) k)) (φ : GL (Fin n) E → ℂ) (f : GL (Fin n) k → ℂ) : Prop :=
  (∀ (δ : GL (Fin n) E) (γ : GL (Fin n) k) (h : GL (Fin n) E)
      (μδ : Measure (twCent (sigmaGL σ) δ)) (μγ : Measure (Subgroup.centralizer {γ})),
      IsTwRegSemisimple σ δ → normGL σ δ = h * incl γ * h⁻¹ → μδ.IsHaarMeasure → μγ.IsHaarMeasure →
      Measure.map (fun x : twCent (sigmaGL σ) δ => h⁻¹ * (x : GL (Fin n) E) * h) μδ =
        Measure.map (fun t : Subgroup.centralizer {γ} => incl (t : GL (Fin n) k)) μγ →
      twOrbIntegralC (sigmaGL σ) μE δ μδ φ = orbIntegralC μk γ μγ f) ∧
  ∀ (γ : GL (Fin n) k) (μγ : Measure (Subgroup.centralizer {γ})),
    IsRegSemisimple γ → (¬ ∃ δ : GL (Fin n) E, IsNormOf σ δ γ) → μγ.IsHaarMeasure → orbIntegralC μk γ μγ f = 0

end UpperTheory.ConvolutionTheory.Loc

end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.RootConj
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets UpperTheory.ConvolutionTheory.Loc

section SlopeTestRemainingChoices

variable {E : Type} [Field E] {Γ : Type} [LinearOrderedCommGroupWithZero Γ] {n : ℕ}

private def Bd (v : Valuation E Γ) (X : Matrix (Fin n) (Fin n) E) (c : Γ) : Prop := ∀ i j, v (X i j) ≤ c

private lemma Bd.add {v : Valuation E Γ} {X Y : Matrix (Fin n) (Fin n) E} {c : Γ} (hX : Bd v X c) (hY : Bd v Y c) :
    Bd v (X + Y) c := fun i j => by
  rw [Matrix.add_apply]; exact v.map_add_le (hX i j) (hY i j)

private lemma Bd.mul {v : Valuation E Γ} {X Y : Matrix (Fin n) (Fin n) E} {c d : Γ} (hX : Bd v X c) (hY : Bd v Y d) :
    Bd v (X * Y) (c * d) := fun i j => by
  rw [Matrix.mul_apply]
  refine v.map_sum_le fun k _ => ?_
  rw [v.map_mul]
  exact mul_le_mul' (hX i k) (hY k j)

private lemma Bd.mono {v : Valuation E Γ} {X : Matrix (Fin n) (Fin n) E} {c d : Γ} (hX : Bd v X c) (h : c ≤ d) :
    Bd v X d := fun i j => (hX i j).trans h

private lemma Bd.one (v : Valuation E Γ) : Bd v (1 : Matrix (Fin n) (Fin n) E) 1 := fun i j => by
  rw [Matrix.one_apply]; split_ifs <;> simp

private lemma val_nat_le (v : Valuation E Γ) (m : ℕ) : v (m : E) ≤ 1 := by
  induction m with
  | zero => simp
  | succ m ih => rw [Nat.cast_succ]; exact v.map_add_le ih (by simp)

private lemma Bd.nsmul {v : Valuation E Γ} {X : Matrix (Fin n) (Fin n) E} {c : Γ} (hX : Bd v X c) (m : ℕ) :
    Bd v ((m : E) • X) c := fun i j => by
  rw [Matrix.smul_apply, smul_eq_mul, v.map_mul]
  simpa using mul_le_mul' (val_nat_le v m) (hX i j)

private lemma Bd.pow_sub {v : Valuation E Γ} {B : Matrix (Fin n) (Fin n) E} {r : Γ} (hr : r ≤ 1)
    (hB : Bd v (B - 1) r) (m : ℕ) : Bd v (B ^ m - 1) r := by
  induction m with
  | zero => intro i j; simp
  | succ m ih =>
    have h1 : Bd v (B ^ m - 1 + 1) 1 := (ih.mono hr).add (Bd.one v)
    have h2 := (hB.mul h1).mono (mul_one r).le
    have e : B ^ (m + 1) - 1 = (B - 1) * (B ^ m - 1 + 1) + (B ^ m - 1) := by
      rw [pow_succ']; noncomm_ring
    rw [e]; exact h2.add ih

private lemma Bd.tele {v : Valuation E Γ} {A B g : Matrix (Fin n) (Fin n) E} {r c : Γ} (hr : r ≤ 1)
    (hA : Bd v (A - 1) r) (hB : Bd v (B - 1) r) (hh : Bd v (A * g - g * B) c) (m : ℕ) :
    Bd v (A ^ m * g - g * B ^ m - (m : E) • (A * g - g * B)) (r * c) := by
  induction m with
  | zero => intro i j; simp
  | succ m ih =>
    have hrc : r * c ≤ c := by simpa using mul_le_mul' hr (le_refl c)
    have h1 := hA.mul ((ih.mono hrc).add (hh.nsmul m))
    have h2 := (hh.mul (hB.pow_sub hr m)).mono (mul_comm c r).le
    have e : A ^ (m + 1) * g - g * B ^ (m + 1) - ((m + 1 : ℕ) : E) • (A * g - g * B) =
        (A - 1) * (A ^ m * g - g * B ^ m - (m : E) • (A * g - g * B) + (m : E) • (A * g - g * B)) +
          (A * g - g * B) * (B ^ m - 1) + (A ^ m * g - g * B ^ m - (m : E) • (A * g - g * B)) := by
      rw [Nat.cast_succ, add_smul, one_smul, pow_succ', pow_succ']
      generalize (m : E) • (A * g - g * B) = Z
      noncomm_ring
    rw [e]; exact (h1.add h2).add ih

private lemma intertwine (v : Valuation E Γ) {A B g : Matrix (Fin n) (Fin n) E} {r : Γ} {q : ℕ} (hq : r < v (q : E))
    (hA : Bd v (A - 1) r) (hB : Bd v (B - 1) r) (h : A ^ q * g = g * B ^ q) : A * g = g * B := by
  rw [← sub_eq_zero]
  ext i0 j0
  obtain ⟨⟨i, j⟩, -, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin n × Fin n))
    (fun p => v ((A * g - g * B) p.1 p.2)) ⟨(i0, j0), Finset.mem_univ _⟩
  have hh : Bd v (A * g - g * B) (v ((A * g - g * B) i j)) := fun a b => hmax (a, b) (Finset.mem_univ _)
  have ht := Bd.tele (hq.le.trans (val_nat_le v q)) hA hB hh q i j
  rw [h, sub_self, zero_sub, Matrix.neg_apply, v.map_neg, Matrix.smul_apply, smul_eq_mul, v.map_mul] at ht
  have h0 : v ((A * g - g * B) i j) = 0 := by
    by_contra hne
    exact absurd ht (not_le.2 (mul_lt_mul_of_pos_right hq (zero_lt_iff.2 hne)))
  have := hh i0 j0
  rw [h0, le_zero_iff, v.zero_iff] at this
  simpa using this

end SlopeTestRemainingChoices

theorem UpperTheory.ConvolutionTheory.Loc.rootConj :
    ∀ (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] (n : ℕ) (q : ℕ) (r : ValueGroupWithZero E), r < valuation E (q : E) →
      ∀ u ∈ ball n r, ∀ u' ∈ ball n r, ∀ g : GL (Fin n) E, g⁻¹ * u ^ q * g = u' ^ q → g⁻¹ * u * g = u' := by
  intro E _ _ _ _ n q r hq u hu u' hu' g h
  have h1 : u ^ q * g = g * u' ^ q := by rw [← h]; group
  have h2 : (u : Matrix (Fin n) (Fin n) E) * g = g * u' :=
    intertwine (valuation E) hq (fun i j => hu i j) (fun i j => hu' i j)
      (by simpa using congrArg Units.val h1)
  have h3 : u * g = g * u' := Units.ext (by simpa using h2)
  rw [mul_assoc, h3]; group
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.SbInv
section
open GlobalTheory.SplitWeil

theorem UpperTheory.ConvolutionTheory.Loc.sbInv :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G], ∀ φ ∈ SB G, ∀ K : Subgroup G, IsOpen (K : Set G) → IsCompact (K : Set G) → TotallyDisconnectedSpace G →
      ∃ U : Subgroup G, IsOpen (U : Set G) ∧ U ≤ K ∧ ∀ u ∈ U, ∀ g, φ (u * g) = φ g ∧ φ (g * u) = φ g := by
  intro G _ _ _ φ hφ K hKo hKc hG
  obtain ⟨hl, hc⟩ := hφ
  have key : ∀ ψ : G × G → G, Continuous ψ → (∀ g, ψ (1, g) = g) → ∀ᶠ u in nhds (1 : G), ∀ g ∈ tsupport φ, φ (ψ (u, g)) = φ g := by
    intro ψ hψ h1
    apply IsCompact.eventually_forall_of_forall_eventually hc
    intro g _
    have a := (hl.comp_continuous hψ).eventually_eq (1, g)
    have b := (hl.comp_continuous continuous_snd).eventually_eq ((1 : G), g)
    filter_upwards [a, b] with z ha hb
    simp only [Function.comp, h1] at ha hb
    rw [ha, hb]
  have a := key (fun p => p.1 * p.2) (by fun_prop) (by simp)
  have b := key (fun p => p.2 * p.1) (by fun_prop) (by simp)
  obtain ⟨W, hW, hWo, hW1⟩ := mem_nhds_iff.1 (a.and b)
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hKc
  obtain ⟨N, hN⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one (G := K) (U := Subtype.val ⁻¹' W) (hWo.preimage continuous_subtype_val) hW1
  have hU : ∀ u ∈ N.toSubgroup.map K.subtype, u ∈ W := by
    rintro _ ⟨x, hx, rfl⟩
    exact hN hx
  refine ⟨N.toSubgroup.map K.subtype, ?_, Subgroup.map_subtype_le _, fun u hu g => ⟨?_, ?_⟩⟩
  · exact hKo.isOpenMap_subtype_val _ N.isOpen
  · by_cases h : g ∈ tsupport φ
    · exact (hW (hU u hu)).1 g h
    · by_cases h' : u * g ∈ tsupport φ
      · have := (hW (hU _ (inv_mem hu))).1 _ h'
        simpa using this.symm
      · rw [image_eq_zero_of_notMem_tsupport h, image_eq_zero_of_notMem_tsupport h']
  · by_cases h : g ∈ tsupport φ
    · exact (hW (hU u hu)).2 g h
    · by_cases h' : g * u ∈ tsupport φ
      · have := (hW (hU _ (inv_mem hu))).2 _ h'
        simpa using this.symm
      · rw [image_eq_zero_of_notMem_tsupport h, image_eq_zero_of_notMem_tsupport h']
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.SgIterateEqSelf
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets UpperTheory.ConvolutionTheory.Loc

namespace UpperTheory.ConvolutionTheory.Loc

variable {E : Type} [Field E] {n : ℕ}

theorem nrm_succ (σ : E ≃+* E) (q : ℕ) (δ : GL (Fin n) E) :
    nrm σ (q + 1) δ = nrm σ q δ * (sg σ)^[q] δ := by
  simp [nrm, List.range_succ]

theorem sg_iterate_apply (σ : E ≃+* E) (q : ℕ) (x : GL (Fin n) E) (i j : Fin n) :
    (((sg σ)^[q] x : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i j = σ^[q] ((x : Matrix (Fin n) (Fin n) E) i j) := by
  induction q with
  | zero => rfl
  | succ q ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]
    rfl

theorem sg_iterate_eq_self {σ : E ≃+* E} {q : ℕ} (h : ∀ a, σ^[q] a = a) (x : GL (Fin n) E) : (sg σ)^[q] x = x := by
  apply Units.ext
  ext i j
  rw [sg_iterate_apply, h]

theorem nrm_conj_iterate (σ : E ≃+* E) (q : ℕ) (δ x : GL (Fin n) E) :
    nrm σ q (x⁻¹ * δ * sg σ x) = x⁻¹ * nrm σ q δ * (sg σ)^[q] x := by
  induction q with
  | zero => simp [nrm]
  | succ q ih =>
    rw [nrm_succ, nrm_succ, ih, iterate_map_mul, iterate_map_mul, iterate_map_inv, Function.iterate_succ_apply]
    group

theorem nrm_conj {σ : E ≃+* E} {q : ℕ} (h : ∀ a, σ^[q] a = a) (δ x : GL (Fin n) E) :
    nrm σ q (x⁻¹ * δ * sg σ x) = x⁻¹ * nrm σ q δ * x := by
  rw [nrm_conj_iterate, sg_iterate_eq_self h]

end UpperTheory.ConvolutionTheory.Loc
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.StrictNormal
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets UpperTheory.ConvolutionTheory.Loc

theorem UpperTheory.ConvolutionTheory.Loc.strictNormal :
    ∀ (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] (n : ℕ) (σ : E ≃+* E) (q : ℕ), Cyc σ q → ∀ t t' : Fin n → Eˣ, Strict t → Strict t' → ∀ x : GL (Fin n) E,
      x⁻¹ * diagT E (Fin n) t * sg σ x = diagT E (Fin n) t' → ∃ s : Fin n → Eˣ, x = diagT E (Fin n) s := by
  intro E _ _ _ _ n σ q hσ t t' ht ht' x hx
  have hd : ∀ s : Fin n → Eˣ, (diagT E (Fin n) s : Matrix (Fin n) (Fin n) E) = diagonal (fun a => (s a : E)) :=
    fun _ => val_diagT ..
  have h1 : diagT E (Fin n) t * sg σ x = x * diagT E (Fin n) t' := by
    rw [← hx]; group

  have key : ∀ i j, (x : Matrix (Fin n) (Fin n) E) i j ≠ 0 →
      valuation E (t i : E) = valuation E (t' j : E) := by
    intro i j hij
    have h2 := congrArg (fun g : GL (Fin n) E => valuation E ((g : Matrix (Fin n) (Fin n) E) i j)) h1
    simp only [Units.val_mul, hd, diagonal_mul, mul_diagonal, map_mul] at h2
    have h3 : (sg σ x : Matrix (Fin n) (Fin n) E) i j = σ ((x : Matrix (Fin n) (Fin n) E) i j) := rfl
    rw [h3, hσ.isom, mul_comm] at h2
    exact mul_left_cancel₀ ((Valuation.ne_zero_iff _).2 hij) h2
  have hm : StrictMono fun i => valuation E (t i : E) := fun i j h => ht i j h
  have hm' : StrictMono fun i => valuation E (t' i : E) := fun i j h => ht' i j h
  have hdet : (x : Matrix (Fin n) (Fin n) E).det ≠ 0 := GeneralLinearGroup.det_ne_zero x
  obtain ⟨w, hw⟩ : ∃ w : Equiv.Perm (Fin n), ∀ j, (x : Matrix (Fin n) (Fin n) E) (w j) j ≠ 0 := by
    by_contra hcon
    apply hdet
    rw [det_apply]
    refine Finset.sum_eq_zero fun w _ => ?_
    have : ∃ j, (x : Matrix (Fin n) (Fin n) E) (w j) j = 0 := by
      by_contra h
      exact hcon ⟨w, fun j hj => h ⟨j, hj⟩⟩
    obtain ⟨j, hj⟩ := this
    rw [Finset.prod_eq_zero (f := fun i => (x : Matrix (Fin n) (Fin n) E) (w i) i) (Finset.mem_univ j) hj, smul_zero]
  have hwm : StrictMono w := by
    intro a b hab
    apply hm.lt_iff_lt.1
    simp only [key _ _ (hw a), key _ _ (hw b)]
    exact hm' hab
  have hwid : ∀ j, w j = j := by
    intro j
    have := Subsingleton.elim (hwm.orderIsoOfSurjective w w.surjective) (OrderIso.refl _)
    exact congrArg (fun e : Fin n ≃o Fin n => e j) this
  have hdiag : ∀ j, (x : Matrix (Fin n) (Fin n) E) j j ≠ 0 := fun j => by
    have := hw j
    rwa [hwid] at this
  refine ⟨fun j => Units.mk0 _ (hdiag j), Units.ext ?_⟩
  rw [hd]
  ext i j
  by_cases hij : i = j
  · subst hij
    simp
  · rw [diagonal_apply_ne _ hij]
    by_contra hne
    exact hij (hm.injective ((key i j hne).trans (key j j (hdiag j)).symm))
end

