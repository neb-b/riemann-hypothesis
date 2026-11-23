module

public import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.HoweSpace
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NontrivialTwJacquetOfSurjective
public import GroundTheory.LocalFields.Uniqueness
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsHilbertSchmidtOfFiniteDimensional

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4HoweTheory.CharDual
section
open MeasureTheory ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets UpperTheory.ConvolutionTheory.Loc

theorem UpperTheory.V.Z.Tf.L4.charDual :
    ∀ (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] (ϖ : Eˣ), valuation E (ϖ : E) = uniformizer E → ∀ (ψ₀ ψ : AddChar E Circle) (d e : ℤ), HasConductor ψ₀ (ϖ ^ d) → HasConductor ψ (ϖ ^ e) →
  ∃ β : Eˣ, valuation E (β : E) = valuation E ((ϖ ^ (d - e) : Eˣ) : E) ∧ ∀ x, ψ x = ψ₀ (β * x) := by
  intro E _ _ _ _ ϖ _ ψ₀ ψ d e h0 h
  obtain ⟨b, hb⟩ := GlobalTheory.LocGL.exists_eq_mulShift h0.continuous h0.ne_one h.continuous
  have hb0 : b ≠ 0 := fun e0 => h.ne_one (by rw [hb, e0, AddChar.mulShift_zero])
  have hv : ∀ x, ψ x = ψ₀ (b * x) := fun x => by rw [hb, AddChar.mulShift_apply]
  have hvb : 0 < valuation E b := zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hb0)
  have key : ∀ x : E, valuation E x ≤ valuation E ((ϖ ^ e : Eˣ) : E) ↔ valuation E (b * x) ≤ valuation E ((ϖ ^ d : Eˣ) : E) := fun x => by
    rw [← h x, ← h0 (b * x)]
    refine ⟨fun H y hy => ?_, fun H y hy => ?_⟩
    · have := H (b⁻¹ * y) (by
        rw [map_mul] at hy
        rw [map_mul, map_inv₀, inv_mul_le_iff₀ hvb]
        exact hy)
      rwa [hv, mul_inv_cancel_left₀ hb0] at this
    · rw [hv]
      exact H _ (by rw [map_mul, map_mul]; exact mul_le_mul_right hy _)
  have hve : 0 < valuation E ((ϖ ^ e : Eˣ) : E) := zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 (Units.ne_zero _))
  have h1 := (key _).1 le_rfl
  have h2 := (key (b⁻¹ * ((ϖ ^ d : Eˣ) : E))).2 (by rw [mul_inv_cancel_left₀ hb0])
  rw [map_mul, map_inv₀, inv_mul_le_iff₀ hvb] at h2
  rw [map_mul] at h1
  refine ⟨Units.mk0 b hb0, ?_, hv⟩
  rw [zpow_sub, Units.val_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀, ← le_antisymm h1 h2, Units.val_mk0,
    mul_inv_cancel_right₀ hve.ne']
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4HoweTheory.GalIsom
section
open MeasureTheory ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets UpperTheory.ConvolutionTheory.Loc

theorem UpperTheory.V.Z.Tf.L4.galIsom :
    ∀ (k E : Type) [Field k] [CharZero k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
      [Algebra k E] [ValuativeExtension k E] [FiniteDimensional k E] [IsGalois k E] (σ : E ≃ₐ[k] E) (x : E), valuation E (σ x) = valuation E x := by
  intro k E _ _ _ _ _ _ _ _ _ _ _ _ _ σ x
  exact GroundTheory.LocalField.valuation_algEquiv_apply k E σ x
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4HoweTheory.HoweBall
section
open MeasureTheory ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets UpperTheory.ConvolutionTheory.Loc

theorem UpperTheory.V.Z.Tf.L4.howeBall :
    ∀ (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] (n : ℕ) (ϖ : Eˣ), valuation E (ϖ : E) = uniformizer E → ∀ (c : ℤ) (ρ : ValueGroupWithZero E), 0 < ρ →
      ∃ a₀ : ℤ, ∀ a ≥ a₀, howeSet n ϖ a c ⊆ ball n ρ := by
  intro E _ _ _ _ n ϖ hϖ c ρ hρ
  have h1 : valuation E (ϖ : E) < 1 := by rw [hϖ]; exact uniformizer_lt_one
  have h0 : 0 < valuation E (ϖ : E) := by rw [hϖ]; exact uniformizer_pos
  haveI : MulArchimedean (ValueGroupWithZero E) := isRankLeOne_iff_mulArchimedean.1 inferInstance
  obtain ⟨N, hN⟩ := exists_pow_lt₀ h1 (Units.mk0 ρ hρ.ne')
  refine ⟨N + |c| * n, fun a ha g hg i j => (hg i j).trans ?_⟩
  rw [Units.val_zpow_eq_zpow_val, map_zpow₀]
  refine le_trans ?_ hN.le
  rw [← zpow_natCast]
  refine zpow_le_zpow_right_of_le_one₀ h0 h1.le ?_
  have hi := i.2
  have hj := j.2
  have h2 : |((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)| ≤ n := by
    rw [abs_le]; constructor <;> omega
  have h3 : |c * (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ))| ≤ |c| * n := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
  have h4 := (abs_le.1 h3).1
  linarith
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4HoweTheory.HoweChar
section
open MeasureTheory ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets UpperTheory.ConvolutionTheory.Loc

namespace UpperTheory.V.Z.Tf.L4

variable {E : Type} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]

private theorem hc_triv {ψ : AddChar E Circle} {d : Eˣ} (h : HasConductor ψ d) {y : E}
    (hy : valuation E y ≤ valuation E (d : E)) : ψ y = 1 :=
  (h d).2 le_rfl y hy

private theorem hc_lc {ψ : AddChar E Circle} {d : Eˣ} (h : HasConductor ψ d) :
    IsLocallyConstant (fun t : E => (ψ t : ℂ)) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro t
  have hd : valuation E (d : E) ≠ 0 := by simp
  have hm : {z : E | valuation E (z - t) < valuation E (d : E)} ∈ nhds t :=
    IsValuativeTopology.mem_nhds_iff'.2 ⟨Units.mk0 _ hd, fun z hz => hz⟩
  filter_upwards [hm] with z hz
  have h1 : ψ (z - t) = 1 := hc_triv h (le_of_lt hz)
  have h2 : ψ z = ψ (z - t) * ψ t := by rw [← AddChar.map_add_eq_mul, sub_add_cancel]
  rw [h2, h1, one_mul]

private theorem hc_cont {n : ℕ} : Continuous (fun x : GL (Fin n) E => GlobalTheory.Whittaker.superDiag x) := by
  unfold GlobalTheory.Whittaker.superDiag
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  exact (Units.continuous_val).matrix_elem i j

private theorem hc_cross {n : ℕ} {ϖ : Eˣ} {a c : ℤ} {x y : GL (Fin n) E} (hx : x ∈ howeSet n ϖ a c)
    (hy : y ∈ howeSet n ϖ a c) {i j : Fin n} (hij : j.val = i.val + 1) :
    valuation E ((((x : Matrix (Fin n) (Fin n) E) - 1) * ((y : Matrix (Fin n) (Fin n) E) - 1)) i j) ≤
      valuation E ((ϖ ^ (2 * a - c) : Eˣ) : E) := by
  rw [Matrix.mul_apply]
  refine Valuation.map_sum_le _ fun k _ => ?_
  rw [map_mul, Matrix.sub_apply, Matrix.sub_apply]
  refine (mul_le_mul' (hx i k) (hy k j)).trans (le_of_eq ?_)
  rw [← map_mul, ← Units.val_mul, ← zpow_add]
  congr 3
  rw [hij]
  push_cast
  ring

end UpperTheory.V.Z.Tf.L4

theorem UpperTheory.V.Z.Tf.L4.howeChar :
    ∀ (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] (n : ℕ) (ϖ : Eˣ), valuation E (ϖ : E) = uniformizer E → ∀ a c : ℤ, 1 ≤ a →
      ∀ ψ : AddChar E Circle, HasConductor ψ (ϖ ^ (2 * a - c)) →
        IsLocallyConstant (fun x : GL (Fin n) E => (ψ (GlobalTheory.Whittaker.superDiag x) : ℂ)) ∧
        ∀ x ∈ howeSet n ϖ a c, ∀ y ∈ howeSet n ϖ a c,
          ψ (GlobalTheory.Whittaker.superDiag (x * y)) = ψ (GlobalTheory.Whittaker.superDiag x) * ψ (GlobalTheory.Whittaker.superDiag y) := by
  intro E _ _ _ _ n ϖ _ a c _ ψ hψ
  refine ⟨(UpperTheory.V.Z.Tf.L4.hc_lc hψ).comp_continuous UpperTheory.V.Z.Tf.L4.hc_cont, fun x hx y hy => ?_⟩
  set M := ((x : Matrix (Fin n) (Fin n) E) - 1) * ((y : Matrix (Fin n) (Fin n) E) - 1) with hM
  set r : E := ∑ i : Fin n, ∑ j : Fin n with j.val = i.val + 1, M i j with hr
  have hr1 : ψ r = 1 := by
    refine UpperTheory.V.Z.Tf.L4.hc_triv hψ ?_
    refine Valuation.map_sum_le _ fun i _ => Valuation.map_sum_le _ fun j hj => ?_
    exact UpperTheory.V.Z.Tf.L4.hc_cross hx hy (Finset.mem_filter.1 hj).2
  have hs : GlobalTheory.Whittaker.superDiag (x * y) =
      GlobalTheory.Whittaker.superDiag x + GlobalTheory.Whittaker.superDiag y + r := by
    simp only [GlobalTheory.Whittaker.superDiag, hr, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j hj => ?_
    have hij : i ≠ j := by
      have := (Finset.mem_filter.1 hj).2
      rintro rfl
      omega
    have e : ((x * y : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) =
        (x : Matrix (Fin n) (Fin n) E) + (y : Matrix (Fin n) (Fin n) E) + M - 1 := by
      rw [hM, Units.val_mul]
      noncomm_ring
    rw [e, Matrix.sub_apply, Matrix.one_apply_ne hij, sub_zero, Matrix.add_apply, Matrix.add_apply]
  rw [hs, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, hr1, mul_one]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4HoweTheory.HoweConj
section
open MeasureTheory ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets UpperTheory.ConvolutionTheory.Loc

private noncomputable def dg {E : Type} [Field E] (n : ℕ) (β : Eˣ) : GL (Fin n) E :=
  ⟨Matrix.diagonal fun i => ((β ^ (-((i : ℕ) : ℤ)) : Eˣ) : E), Matrix.diagonal fun i => ((β ^ ((i : ℕ) : ℤ) : Eˣ) : E),
    by
      rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1; funext i
      rw [← Units.val_mul, ← zpow_add, neg_add_cancel, zpow_zero, Units.val_one],
    by
      rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1; funext i
      rw [← Units.val_mul, ← zpow_add, add_neg_cancel, zpow_zero, Units.val_one]⟩

private theorem dg_conj {E : Type} [Field E] {n : ℕ} (β : Eˣ) (x : GL (Fin n) E) (i j : Fin n) :
    ((dg n β * x * (dg n β)⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i j =
      ((β ^ (((j : ℕ) : ℤ) - ((i : ℕ) : ℤ)) : Eˣ) : E) * (x : Matrix (Fin n) (Fin n) E) i j := by
  change (Matrix.diagonal (fun i : Fin n => ((β ^ (-((i : ℕ) : ℤ)) : Eˣ) : E)) * (x : Matrix (Fin n) (Fin n) E) *
    Matrix.diagonal (fun i : Fin n => ((β ^ ((i : ℕ) : ℤ) : Eˣ) : E))) i j = _
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, sub_eq_add_neg, zpow_add, Units.val_mul]
  ring

theorem UpperTheory.V.Z.Tf.L4.howeConj :
    ∀ (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) E) V) (ϖ β : Eˣ) (a c t : ℤ),
      valuation E (β : E) = valuation E ((ϖ ^ t : Eˣ) : E) → ∀ ψ₀ ψ : AddChar E Circle, (∀ x, ψ x = ψ₀ (β * x)) →
      howeSpace π ψ₀ (howeSet n ϖ a (c - t)) ≠ ⊥ → howeSpace π ψ (howeSet n ϖ a c) ≠ ⊥ := by
  intro E _ _ _ _ n V _ _ π ϖ β a c t hβ ψ₀ ψ hψ h
  obtain ⟨w, hw, h0⟩ := (Submodule.ne_bot_iff _).1 h
  refine (Submodule.ne_bot_iff _).2 ⟨π (dg n β)⁻¹ w, fun x hx => ?_, fun e => h0 ?_⟩
  · have hy : dg n β * x * (dg n β)⁻¹ ∈ howeSet n ϖ a (c - t) := fun i j => by
      have e : ((dg n β * x * (dg n β)⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i j - (1 : Matrix (Fin n) (Fin n) E) i j =
          ((β ^ (((j : ℕ) : ℤ) - ((i : ℕ) : ℤ)) : Eˣ) : E) *
            ((x : Matrix (Fin n) (Fin n) E) i j - (1 : Matrix (Fin n) (Fin n) E) i j) := by
        rw [dg_conj, mul_sub]
        congr 1
        by_cases hij : i = j
        · subst hij; simp
        · simp [Matrix.one_apply_ne hij]
      have e2 : valuation E ((β ^ (((j : ℕ) : ℤ) - ((i : ℕ) : ℤ)) : Eˣ) : E) =
          valuation E ((ϖ ^ (t * (((j : ℕ) : ℤ) - ((i : ℕ) : ℤ))) : Eˣ) : E) := by
        rw [zpow_mul, Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val (ϖ ^ t), map_zpow₀, map_zpow₀, hβ]
      rw [e, map_mul, e2, show a + (c - t) * (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)) =
        t * (((j : ℕ) : ℤ) - ((i : ℕ) : ℤ)) + (a + c * (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ))) by ring, zpow_add, Units.val_mul, map_mul]
      exact mul_le_mul_right (hx i j) _
    have hs : GlobalTheory.Whittaker.superDiag (dg n β * x * (dg n β)⁻¹) = β * GlobalTheory.Whittaker.superDiag x := by
      simp only [GlobalTheory.Whittaker.superDiag, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j hj => ?_
      rw [dg_conj, (Finset.mem_filter.1 hj).2]
      simp
    have h1 := hw _ hy
    rw [hs, ← hψ] at h1
    rw [← map_smul, ← h1, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
    congr 2
    group
  · have := congrArg (π (dg n β)) e
    rwa [map_zero, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at this
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4HoweTheory.HoweGroup
section
open MeasureTheory ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets UpperTheory.ConvolutionTheory.Loc

namespace UpperTheory.V.Z.Tf.L4

variable {E : Type} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] {n : ℕ}

omit [TopologicalSpace E] [IsNonarchimedeanLocalField E] in
private theorem mul_bd {X Y : Matrix (Fin n) (Fin n) E} {s : ValueGroupWithZero E}
    (hX : ∀ i j, valuation E (X i j) ≤ s) (hY : ∀ i j, valuation E (Y i j) ≤ 1) (i j : Fin n) :
    valuation E ((X * Y) i j) ≤ s := by
  rw [Matrix.mul_apply]
  refine Valuation.map_sum_le _ fun l _ => ?_
  rw [map_mul]
  simpa using mul_le_mul' (hX i l) (hY l j)

omit [TopologicalSpace E] [IsNonarchimedeanLocalField E] in
private theorem one_bd (i j : Fin n) : valuation E ((1 : Matrix (Fin n) (Fin n) E) i j) ≤ 1 := by
  rw [Matrix.one_apply]
  split_ifs <;> simp

omit [TopologicalSpace E] [IsNonarchimedeanLocalField E] in
private theorem val_bd {g : GL (Fin n) E} (h : ∀ i j, valuation E ((g.val - 1) i j) < 1) (i j : Fin n) :
    valuation E (g.val i j) ≤ 1 := by
  have e : g.val i j = (g.val - 1) i j + (1 : Matrix (Fin n) (Fin n) E) i j := by simp
  rw [e]
  exact Valuation.map_add_le _ (h i j).le (one_bd i j)

omit [TopologicalSpace E] [IsNonarchimedeanLocalField E] in
private theorem inv_bd {g : GL (Fin n) E} (h : ∀ i j, valuation E ((g.val - 1) i j) < 1) (i j : Fin n) :
    valuation E ((g⁻¹).val i j) ≤ 1 := by
  obtain ⟨m, -, hm⟩ := Finset.exists_max_image Finset.univ (fun i => valuation E ((g⁻¹).val i j)) ⟨i, Finset.mem_univ _⟩
  refine (hm i (Finset.mem_univ _)).trans ?_
  by_contra hlt
  rw [not_le] at hlt
  have h0 : 0 < valuation E ((g⁻¹).val m j) := lt_of_le_of_lt zero_le hlt
  have e0 : (g⁻¹).val = 1 - (g.val - 1) * (g⁻¹).val := by
    rw [sub_mul, Units.mul_inv]; noncomm_ring
  have e : (g⁻¹).val m j = (1 : Matrix (Fin n) (Fin n) E) m j - ((g.val - 1) * (g⁻¹).val) m j :=
    congrFun (congrFun e0 m) j
  have h1 : valuation E (((g.val - 1) * (g⁻¹).val) m j) < valuation E ((g⁻¹).val m j) := by
    rw [Matrix.mul_apply]
    refine Valuation.map_sum_lt _ h0.ne' fun l _ => ?_
    rw [map_mul]
    calc _ ≤ valuation E ((g.val - 1) m l) * valuation E ((g⁻¹).val m j) :=
          mul_le_mul' le_rfl (hm l (Finset.mem_univ _))
      _ < 1 * valuation E ((g⁻¹).val m j) := mul_lt_mul_of_pos_right (h _ _) h0
      _ = _ := one_mul _
  have h2 := Valuation.map_sub_lt (valuation E) ((one_bd m j).trans_lt hlt) h1
  rw [← e] at h2
  exact lt_irrefl _ h2

private def cg (n : ℕ) (c : Eˣ) (hc : valuation E (c : E) < 1) : Subgroup (GL (Fin n) E) where
  carrier := {g | ∀ i j, valuation E ((g.val - 1) i j) ≤ valuation E (c : E)}
  one_mem' := fun i j => by simp
  mul_mem' := by
    intro x y hx hy i j
    have e : (x * y).val - 1 = (x.val - 1) * y.val + (y.val - 1) := by
      rw [Units.val_mul]; noncomm_ring
    rw [e, Matrix.add_apply]
    exact Valuation.map_add_le _ (mul_bd hx (val_bd fun i j => (hy i j).trans_lt hc) i j) (hy i j)
  inv_mem' := by
    intro x hx i j
    have e : (x⁻¹).val - 1 = -((x.val - 1) * (x⁻¹).val) := by
      rw [sub_mul, Units.mul_inv]; noncomm_ring
    rw [e, Matrix.neg_apply, Valuation.map_neg]
    exact mul_bd hx (inv_bd fun i j => (hx i j).trans_lt hc) i j

private theorem isOpen_cg (n : ℕ) (c : Eˣ) (hc : valuation E (c : E) < 1) :
    IsOpen (cg n c hc : Set (GL (Fin n) E)) := by
  have e : (cg n c hc : Set (GL (Fin n) E)) =
      (fun g : GL (Fin n) E => ((c⁻¹ : Eˣ) : E) • (g.val - 1)) ⁻¹' {A : Matrix (Fin n) (Fin n) E | ∀ i j, A i j ∈ 𝒪[E]} := by
    ext g
    refine forall_congr' fun i => forall_congr' fun j => ?_
    change _ ↔ valuation E (((c⁻¹ : Eˣ) : E) * (g.val - 1) i j) ≤ 1
    rw [map_mul, Units.val_inv_eq_inv_val, map_inv₀,
      inv_mul_le_one₀ ((Valuation.pos_iff _).2 c.ne_zero)]
  rw [e]
  have hc : Continuous fun g : GL (Fin n) E => ((c⁻¹ : Eˣ) : E) • (g.val - 1) :=
    (Units.continuous_val.sub continuous_const).const_smul ((c⁻¹ : Eˣ) : E)
  exact GlobalTheory.SplitFlip.isOpen_intMatrix.preimage hc

private theorem isCompact_cg (n : ℕ) (c : Eˣ) (hc : valuation E (c : E) < 1) :
    IsCompact (cg n c hc : Set (GL (Fin n) E)) :=
  GlobalTheory.SplitFlip.isCompact_KO.of_isClosed_subset (Subgroup.isClosed_of_isOpen _ (isOpen_cg n c hc)) fun g hg =>
    (GlobalTheory.SplitFlip.mem_KO_iff g).2
      ⟨val_bd fun i j => (hg i j).trans_lt hc, inv_bd fun i j => (hg i j).trans_lt hc⟩

omit [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] in
private theorem conj_entry (t : Fin n → Eˣ) (g : GL (Fin n) E) (i j : Fin n) :
    ((GlobalTheory.SplitFlip.diagGL t * g * (GlobalTheory.SplitFlip.diagGL t)⁻¹).val - 1) i j =
      (g.val i j - (1 : Matrix (Fin n) (Fin n) E) i j) * ((t i * (t j)⁻¹ : Eˣ) : E) := by
  have e : (GlobalTheory.SplitFlip.diagGL t * g * (GlobalTheory.SplitFlip.diagGL t)⁻¹).val =
      (Matrix.diagonal fun i => (t i : E)) * g.val * Matrix.diagonal fun i => (((t i)⁻¹ : Eˣ) : E) := rfl
  rw [e, Matrix.sub_apply, Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases h : i = j
  · subst h
    simp [sub_mul, mul_right_comm]
  · simp [Matrix.one_apply_ne h]
    ring

end UpperTheory.V.Z.Tf.L4

theorem UpperTheory.V.Z.Tf.L4.howeGroup :
    ∀ (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] (n : ℕ) (ϖ : Eˣ), valuation E (ϖ : E) = uniformizer E → ∀ a c : ℤ, 1 ≤ a →
      ∃ J : Subgroup (GL (Fin n) E), (J : Set (GL (Fin n) E)) = howeSet n ϖ a c ∧ IsOpen (J : Set (GL (Fin n) E)) ∧ IsCompact (J : Set (GL (Fin n) E)) := by
  intro E _ _ _ _ n ϖ hϖ a c ha
  have hlt : valuation E ((ϖ ^ a : Eˣ) : E) < 1 := by
    rw [Units.val_zpow_eq_zpow_val, map_zpow₀, hϖ]
    exact zpow_lt_one₀ (by rw [← hϖ]; exact (Valuation.pos_iff _).2 ϖ.ne_zero) uniformizer_lt_one (by omega)
  let t : Fin n → Eˣ := fun i => ϖ ^ (-(c * ((i : ℕ) : ℤ)))
  let d : GL (Fin n) E := GlobalTheory.SplitFlip.diagGL t
  let φ : GL (Fin n) E ≃ₜ GL (Fin n) E := (Homeomorph.mulLeft d).trans (Homeomorph.mulRight d⁻¹)
  refine ⟨(cg n (ϖ ^ a) hlt).comap (MulAut.conj d).toMonoidHom, ?_, (isOpen_cg n _ hlt).preimage φ.continuous,
    φ.isCompact_preimage.2 (isCompact_cg n _ hlt)⟩
  ext g
  change (∀ i j, valuation E (((d * g * d⁻¹).val - 1) i j) ≤ valuation E ((ϖ ^ a : Eˣ) : E)) ↔ _
  refine forall_congr' fun i => forall_congr' fun j => ?_
  have e : (ϖ ^ a : Eˣ) = ϖ ^ (a + c * (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ))) * (t i * (t j)⁻¹) := by
    simp only [t]
    rw [← zpow_neg, ← zpow_add, ← zpow_add]
    congr 1
    ring
  rw [conj_entry, e, Units.val_mul (ϖ ^ (a + _)), map_mul, map_mul]
  exact mul_le_mul_iff_left₀ ((Valuation.pos_iff (valuation E)).2 (t i * (t j)⁻¹).ne_zero)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4HoweTheory.IdemOp
section
open MeasureTheory ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets UpperTheory.ConvolutionTheory.Loc

theorem UpperTheory.V.Z.Tf.L4.idemOp :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G), μ.IsHaarMeasure →
      ∀ (J : Subgroup G), IsOpen (J : Set G) → IsCompact (J : Set G) → ∀ χ : G → ℂ, IsLocallyConstant χ → (∀ x, ‖χ x‖ = 1) →
      (∀ x ∈ J, ∀ y ∈ J, χ (x * y) = χ x * χ y) →
      ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V), IsSmooth π →
        ∃ (B : V →ₗ[ℂ] V) (m : ℂ), m ≠ 0 ∧ IsIntegralOp μ π ((J : Set G).indicator fun x => (χ x)⁻¹) B ∧
          (∀ v, ∀ x ∈ J, π x (B v) = χ x • B v) ∧ ∀ v, (∀ x ∈ J, π x v = χ x • v) → B v = m • v := by
  intro G _ _ _ _ _ _ μ hμ J hJo hJc χ hχ hn hm V _ _ π hπ
  classical
  set f : G → ℂ := (J : Set G).indicator fun x => (χ x)⁻¹ with hfdef
  have hne : ∀ x, χ x ≠ 0 := fun x h => by simpa [h] using hn x
  have hJcl : IsClopen (J : Set G) := ⟨hJc.isClosed, hJo⟩
  have hf : IsLocallyConstant f := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    have h1 := (IsLocallyConstant.iff_eventually_eq χ).1 hχ x
    by_cases hx : x ∈ (J : Set G)
    · filter_upwards [h1, hJo.mem_nhds hx] with y hy hyJ
      simp only [hfdef, Set.indicator_of_mem hx, Set.indicator_of_mem hyJ, hy]
    · filter_upwards [hJcl.isClosed.isOpen_compl.mem_nhds hx] with y hyJ
      simp only [hfdef, Set.indicator_of_notMem hx, Set.indicator_of_notMem hyJ]
  have hc : HasCompactSupport f :=
    HasCompactSupport.intro hJc fun x hx => Set.indicator_of_notMem hx _
  have hB : IsIntegralOp μ π f (GlobalTheory.OpTrace.smoothOp π μ f) := by
    intro v l
    have hi := hπ.smoothOp_integrand hf hc v
    refine ⟨?_, ?_⟩
    · have := GlobalTheory.OpTrace.integrable_map (μ := μ) hi.1 hi.2 l l.map_zero
      simpa only [map_smul, smul_eq_mul] using this
    · rw [hπ.map_smoothOp (μ := μ) hf hc l v]
      simp only [smul_eq_mul]
  generalize GlobalTheory.OpTrace.smoothOp π μ f = B at hB
  refine ⟨B, (μ.real (J : Set G) : ℂ), ?_, hB, ?_, ?_⟩
  · have h0 : μ (J : Set G) ≠ 0 := (hJo.measure_pos μ ⟨1, J.one_mem⟩).ne'
    have h1 : μ (J : Set G) ≠ ⊤ := hJc.measure_lt_top.ne
    have : μ.real (J : Set G) ≠ 0 := by
      rw [Measure.real, ENNReal.toReal_ne_zero]
      exact ⟨h0, h1⟩
    exact_mod_cast this
  · intro v x hx
    rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
    intro l
    have h1 := (hB v (l ∘ₗ π x)).2
    have h2 := (hB v l).2
    rw [map_sub, map_smul, sub_eq_zero, h2, smul_eq_mul, ← integral_const_mul,
      ← integral_mul_left_eq_self (fun g => χ x * (f g * l (π g v))) x]
    refine h1.trans (integral_congr_ae (Filter.Eventually.of_forall fun g => ?_))
    have e : χ x * f (x * g) = f g := by
      by_cases hg : g ∈ J
      · have hxg : x * g ∈ (J : Set G) := J.mul_mem hx hg
        have hg' : g ∈ (J : Set G) := hg
        simp only [hfdef, Set.indicator_of_mem hxg, Set.indicator_of_mem hg', hm x hx g hg]
        have := hne x
        have := hne g
        field_simp
      · have hxg : x * g ∉ (J : Set G) := fun h => hg ((J.mul_mem_cancel_left hx).1 h)
        have hg' : g ∉ (J : Set G) := hg
        simp only [hfdef, Set.indicator_of_notMem hxg, Set.indicator_of_notMem hg', mul_zero]
    simp only [← mul_assoc, e, map_mul, LinearMap.comp_apply, Module.End.mul_apply]
  · intro v hv
    rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
    intro l
    rw [map_sub, map_smul, sub_eq_zero, (hB v l).2]
    have e : (fun g => f g * l (π g v)) = (J : Set G).indicator fun _ => l v := by
      funext g
      by_cases hg : g ∈ (J : Set G)
      · simp only [hfdef, Set.indicator_of_mem hg, hv g hg, map_smul, smul_eq_mul]
        rw [← mul_assoc, inv_mul_cancel₀ (hne g), one_mul]
      · simp only [hfdef, Set.indicator_of_notMem hg, zero_mul]
    rw [e, integral_indicator_const _ hJo.measurableSet]
    simp
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4HoweTheory.TraceLine
section
open MeasureTheory ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets UpperTheory.ConvolutionTheory.Loc

theorem UpperTheory.V.Z.Tf.L4.traceLine :
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (W : Submodule ℂ V), Module.finrank ℂ W = 1 → ∀ (B : V →ₗ[ℂ] V) (m : ℂ), m ≠ 0 →
      (∀ v, B v ∈ W) → (∀ v ∈ W, B v = m • v) → ∀ A : V ≃ₗ[ℂ] V, (∀ v ∈ W, A v ∈ W) →
        ∃ c : ℂ, c ≠ 0 ∧ HasFinTrace (B ∘ₗ (A : V →ₗ[ℂ] V)) c := by
  intro V _ _ W hW B m hm hB hBW A hA
  have hR : LinearMap.range (B ∘ₗ (A : V →ₗ[ℂ] V)) = W := by
    apply le_antisymm
    · rintro _ ⟨v, rfl⟩
      exact hB _
    · intro w hw
      refine ⟨A.symm (m⁻¹ • w), ?_⟩
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
      rw [hBW _ (W.smul_mem _ hw), smul_smul, mul_inv_cancel₀ hm, one_smul]
  have h1 : Module.finrank ℂ (LinearMap.range (B ∘ₗ (A : V →ₗ[ℂ] V))) = 1 := by rw [hR, hW]
  have hfin : FiniteDimensional ℂ (LinearMap.range (B ∘ₗ (A : V →ₗ[ℂ] V))) :=
    Module.finite_of_finrank_eq_succ h1
  refine ⟨_, ?_, hfin, rfl⟩
  set f := (B ∘ₗ (A : V →ₗ[ℂ] V)).restrict (p := LinearMap.range (B ∘ₗ (A : V →ₗ[ℂ] V)))
    (q := LinearMap.range (B ∘ₗ (A : V →ₗ[ℂ] V)))
    (fun v _ => LinearMap.mem_range_self (B ∘ₗ (A : V →ₗ[ℂ] V)) v) with hf
  obtain ⟨v, hv, hgen⟩ := finrank_eq_one_iff'.1 h1
  obtain ⟨c, hc⟩ := hgen (f v)
  have hfc : f = c • LinearMap.id := by
    ext1 w
    obtain ⟨a, rfl⟩ := hgen w
    rw [map_smul, ← hc, LinearMap.smul_apply, LinearMap.id_apply, smul_comm]
  have hc0 : c ≠ 0 := by
    rintro rfl
    have h2 : ((f v : LinearMap.range (B ∘ₗ (A : V →ₗ[ℂ] V))) : V) = 0 := by
      rw [← hc]; simp
    have h3 : B (A (v : V)) = 0 := h2
    have hvW : (v : V) ∈ W := hR ▸ v.2
    rw [hBW _ (hA _ hvW), smul_eq_zero] at h3
    rcases h3 with h3 | h3
    · exact hm h3
    · exact hv (Subtype.ext (by simpa using h3))
  rw [hfc, map_smul, LinearMap.trace_id, h1]
  simpa using hc0
end

