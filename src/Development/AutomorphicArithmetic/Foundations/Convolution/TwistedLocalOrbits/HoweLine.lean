module

public import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.Bundle0006
public import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.HoweSpace
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4HoweTheory.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4HoweTheory.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4HoweTheory.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4HoweTheory.InjMat
public import Development.DiscreteGroups.GlobalIrreducibility.DzGenCpt

@[expose] public section

open MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets UpperTheory.ConvolutionTheory.Loc UpperTheory.V.Z.Tf.L4

theorem UpperTheory.V.Z.Tf.L4.howeEx0 :
    ∀ (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) E) V), IsSmooth π →
      ∀ ϖ : Eˣ, valuation E (ϖ : E) = uniformizer E → ∀ (ψ : AddChar E Circle) (d : ℤ), HasConductor ψ (ϖ ^ d) → GlobalTheory.LocGL.IsGenericFor ψ π →
      ∃ a₀ : ℤ, ∀ a ≥ a₀, howeSpace π ψ (howeSet n ϖ a (2 * a - d)) ≠ ⊥ := by
  intro E _ _ _ _ n V _ _ π hs ϖ hϖ ψ d hψ hg
  obtain ⟨l, v, hlv, hl⟩ : ∃ (l : Module.Dual ℂ V) (v : V), l v ≠ 0 ∧
      ∀ u ∈ unipB E (Fin n), ∀ x, l (π u x) = (ψ (GlobalTheory.Whittaker.superDiag u) : ℂ) * l x := by
    have : Nontrivial (TwJacquet π (unipB E (Fin n)) (GlobalTheory.LocGL.whitChar ψ n)) := hg
    obtain ⟨w, hw⟩ := exists_ne (0 : TwJacquet π (unipB E (Fin n)) (GlobalTheory.LocGL.whitChar ψ n))
    obtain ⟨l₀, h₀⟩ := Module.Projective.exists_dual_ne_zero ℂ hw
    obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective _ w
    refine ⟨l₀ ∘ₗ Submodule.mkQ _, v, h₀, fun u hu x => ?_⟩
    have h1 : π u x - (GlobalTheory.LocGL.whitChar ψ n ⟨u, hu⟩ : ℂ) • x ∈ twKer π (unipB E (Fin n)) (GlobalTheory.LocGL.whitChar ψ n) :=
      Submodule.subset_span ⟨⟨u, hu⟩, x, rfl⟩
    have h2 : (GlobalTheory.LocGL.whitChar ψ n ⟨u, hu⟩ : ℂ) = (ψ (GlobalTheory.Whittaker.superDiag u) : ℂ) := by
      have : (∑ p : Fin n × Fin n with (p.2 : ℕ) = p.1 + 1, u.val p.1 p.2) = GlobalTheory.Whittaker.superDiag u := by
        rw [GlobalTheory.Whittaker.superDiag, Finset.sum_filter, Fintype.sum_prod_type]
        simp only [Finset.sum_filter]
      rw [← this]
      rfl
    have h3 := (Submodule.Quotient.eq _).2 h1
    simp only [LinearMap.comp_apply, Submodule.mkQ_apply]
    rw [h3, h2, Submodule.Quotient.mk_smul, map_smul, smul_eq_mul]
  obtain ⟨a₀, h₀⟩ := UpperTheory.V.Z.Tf.L4.lowFix E n ϖ hϖ d {g | π g v = v} ((hs v).mem_nhds (by simp))
  refine ⟨max 1 a₀, fun a ha => ?_⟩
  have ha1 : 1 ≤ a := le_trans (le_max_left _ _) ha
  have hψ' : HasConductor ψ (ϖ ^ (2 * a - (2 * a - d))) := by rwa [sub_sub_cancel]
  obtain ⟨J, hJ, ho, hk⟩ := UpperTheory.V.Z.Tf.L4.howeGroup E n ϖ hϖ a (2 * a - d) ha1
  obtain ⟨hlc, hmul⟩ := UpperTheory.V.Z.Tf.L4.howeChar E n ϖ hϖ a (2 * a - d) ha1 ψ hψ'
  have hmem : ∀ x, x ∈ J ↔ x ∈ howeSet n ϖ a (2 * a - d) := fun x => by rw [← hJ]; rfl
  have : LocallyCompactSpace (GL (Fin n) E) := hk.locallyCompactSpace_of_mem_nhds_of_group (ho.mem_nhds J.one_mem)
  borelize (GL (Fin n) E)
  let μ : Measure (GL (Fin n) E) := Measure.haar
  obtain ⟨B, m, -, hB, hB1, -⟩ := UpperTheory.V.Z.Tf.L4.idemOp (GL (Fin n) E) μ inferInstance J ho hk _ hlc (fun x => Circle.norm_coe _)
    (fun x hx y hy => by rw [hmul x ((hmem x).1 hx) y ((hmem y).1 hy), Circle.coe_mul]) V π hs
  refine (Submodule.ne_bot_iff _).2 ⟨B v, fun x hx => hB1 v x ((hmem x).2 hx), fun h => ?_⟩
  have h1 := (hB v l).2
  have e : (fun g => (J : Set (GL (Fin n) E)).indicator (fun x => ((ψ (GlobalTheory.Whittaker.superDiag x) : ℂ))⁻¹) g * l (π g v)) =
      (J : Set (GL (Fin n) E)).indicator fun _ => l v := by
    funext g
    by_cases hgJ : g ∈ (J : Set (GL (Fin n) E))
    · rw [Set.indicator_of_mem hgJ, Set.indicator_of_mem hgJ]
      obtain ⟨u, hu, b, hb, hub, hlow⟩ := UpperTheory.V.Z.Tf.L4.ulFact E n ϖ hϖ a (2 * a - d) ha1 g ((hmem g).1 hgJ)
      have hbv : π b v = v := h₀ a (le_trans (le_max_right _ _) ha) b hb hlow
      have huJ : u ∈ J := by
        have : u = g * b⁻¹ := by rw [hub, mul_inv_cancel_right]
        rw [this]
        exact J.mul_mem hgJ (J.inv_mem ((hmem b).2 hb))
      have hsd : GlobalTheory.Whittaker.superDiag b = 0 :=
        Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j hj => hlow i j (by
          have := (Finset.mem_filter.1 hj).2
          rw [Fin.lt_def]
          omega)
      rw [hub, hmul u ((hmem u).1 huJ) b hb, hsd, AddChar.map_zero_eq_one, mul_one, map_mul, mul_apply_eq_comp, hbv,
        hl u hu, ← mul_assoc, inv_mul_cancel₀ (Circle.coe_ne_zero _), one_mul]
    · rw [Set.indicator_of_notMem hgJ, Set.indicator_of_notMem hgJ, zero_mul]
  rw [e, h, map_zero, integral_indicator_const _ ho.measurableSet] at h1
  rcases smul_eq_zero.1 h1.symm with h2 | h2
  · exact ((ENNReal.toReal_pos (ho.measure_ne_zero μ ⟨1, J.one_mem⟩) hk.measure_lt_top.ne).ne') h2
  · exact hlv h2

theorem UpperTheory.ConvolutionTheory.Loc.howeEx :
    ∀ (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) E) V), IsSmooth π → ∀ ϖ : Eˣ, valuation E (ϖ : E) = uniformizer E → GlobalTheory.LocGL.IsGeneric π → ∀ c : ℤ, ∃ a₀ : ℤ, ∀ a ≥ a₀,
      ∀ ψ : AddChar E Circle, HasConductor ψ (ϖ ^ (2 * a - c)) → howeSpace π ψ (howeSet n ϖ a c) ≠ ⊥ := by
  intro E _ _ _ _ n V _ _ π hs ϖ hϖ ⟨ψ₀, h1, h2, h3⟩ c
  obtain ⟨d, hd⟩ := UpperTheory.V.Z.Tf.L4.condEx E ϖ hϖ ψ₀ h1 h2
  obtain ⟨a₀, h⟩ := UpperTheory.V.Z.Tf.L4.howeEx0 E n V π hs ϖ hϖ ψ₀ d hd h3
  refine ⟨a₀, fun a ha ψ hψ => ?_⟩
  obtain ⟨β, hβ, e⟩ := UpperTheory.V.Z.Tf.L4.charDual E ϖ hϖ ψ₀ ψ d _ hd hψ
  refine UpperTheory.V.Z.Tf.L4.howeConj E n V π ϖ β a c _ hβ ψ₀ ψ e ?_
  rw [show c - (d - (2 * a - c)) = 2 * a - d by ring]
  exact h a ha

section

variable {E : Type} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] {n : ℕ}

private theorem conj_sub (ϖ : Eˣ) (c : ℤ) (g : GL (Fin n) E) (i j : Fin n) :
    ((diagT E (Fin n) (fun i => ϖ ^ (c * (i : ℕ))) * g * (diagT E (Fin n) (fun i => ϖ ^ (c * (i : ℕ))))⁻¹ : GL (Fin n) E) :
      Matrix (Fin n) (Fin n) E) i j - (1 : Matrix (Fin n) (Fin n) E) i j =
      ((ϖ ^ (c * (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ))) : Eˣ) : E) * ((g : Matrix (Fin n) (Fin n) E) i j - (1 : Matrix (Fin n) (Fin n) E) i j) := by
  rw [DiscreteGroups.sglob.DzType.diag_conj_apply, mul_right_comm, ← Units.val_mul, ← _root_.zpow_sub, ← mul_sub, mul_sub ((ϖ ^ _ : Eˣ) : E)]
  congr 1
  by_cases h : i = j
  · subst h; simp
  · simp [Matrix.one_apply_ne h]

private theorem conj_mem (ϖ : Eˣ) (a c : ℤ) (g : GL (Fin n) E) :
    diagT E (Fin n) (fun i => ϖ ^ (c * (i : ℕ))) * g * (diagT E (Fin n) (fun i => ϖ ^ (c * (i : ℕ))))⁻¹ ∈ howeSet n ϖ a c ↔
      Bd (valuation E ((ϖ ^ a : Eˣ) : E)) ((g : Matrix (Fin n) (Fin n) E) - 1) := by
  refine forall_congr' fun i => forall_congr' fun j => ?_
  rw [conj_sub, add_comm a, _root_.zpow_add, Units.val_mul, map_mul, map_mul, Matrix.sub_apply]
  exact mul_le_mul_iff_right₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 (Units.ne_zero _)))

private theorem conj_sd (ϖ : Eˣ) (c : ℤ) (g : GL (Fin n) E) :
    GlobalTheory.Whittaker.superDiag (diagT E (Fin n) (fun i => ϖ ^ (c * (i : ℕ))) * g * (diagT E (Fin n) (fun i => ϖ ^ (c * (i : ℕ))))⁻¹) =
      ((ϖ ^ (-c) : Eˣ) : E) * GlobalTheory.Whittaker.superDiag g := by
  simp only [GlobalTheory.Whittaker.superDiag, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j hj => ?_
  have h := (Finset.mem_filter.1 hj).2
  rw [DiscreteGroups.sglob.DzType.diag_conj_apply, mul_right_comm, ← Units.val_mul, ← _root_.zpow_sub, h]
  congr 3
  push_cast
  ring

omit [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] in
private theorem whit_eq (ψ : AddChar E Circle) (u : unipB E (Fin n)) :
    ((GlobalTheory.LocGL.whitChar ψ n u : ℂˣ) : ℂ) = (ψ (GlobalTheory.Whittaker.superDiag (u : GL (Fin n) E)) : ℂ) := by
  change ((ψ _ : Circle) : ℂ) = _
  congr 2
  simp only [GlobalTheory.Whittaker.superDiag, Finset.sum_filter]
  exact Fintype.sum_prod_type _

end

theorem UpperTheory.ConvolutionTheory.Loc.howeInj :
    ∀ (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) E) V), IsSmooth π → ∀ ϖ : Eˣ, valuation E (ϖ : E) = uniformizer E → ∀ a c : ℤ, 1 ≤ a →
      ∀ ψ : AddChar E Circle, HasConductor ψ (ϖ ^ (2 * a - c)) → ∀ v ∈ howeSpace π ψ (howeSet n ϖ a c),
        v ∈ twKer π (unipB E (Fin n)) (GlobalTheory.LocGL.whitChar ψ n) → v = 0 := by
  intro E _ _ _ _ n V _ _ π hs ϖ hϖ a c ha ψ hψ v hv hk
  obtain ⟨J, hJ, ho, hc⟩ := howeGroup E n ϖ hϖ a c ha
  have hmem : ∀ x, x ∈ J ↔ x ∈ howeSet n ϖ a c := fun x => by rw [← hJ]; rfl
  refine eq_zero_of_no_intertwining hs J (unipB E (Fin n)) hc ho DiscreteGroups.sglob.DzType.exists_compact_unip
    (fun x => (ψ (GlobalTheory.Whittaker.superDiag x) : ℂ)) (howeChar E n ϖ hϖ a c ha ψ hψ).1.continuous (fun x hx y hy => ?_)
    (fun u hu hn => ?_) v (fun k h => hv k ((hmem k).1 h)) (Submodule.span_mono ?_ hk)
  · have := congrArg Units.val (map_mul (GlobalTheory.LocGL.whitChar ψ n) ⟨x, hx⟩ ⟨y, hy⟩)
    rwa [Units.val_mul, whit_eq, whit_eq, whit_eq] at this
  · obtain ⟨d, hd⟩ : ∃ d, d = diagT E (Fin n) (fun i => ϖ ^ (c * (i : ℕ))) := ⟨_, rfl⟩
    have hu' : d⁻¹ * u * d ∈ unipB E (Fin n) := by
      have e : diagT E (Fin n) (fun i => (ϖ ^ (c * (i : ℕ)))⁻¹) = d⁻¹ := by rw [hd, ← map_inv]; rfl
      have := DiscreteGroups.sglob.DzType.diag_conj_mem_unipB (fun i => (ϖ ^ (c * (i : ℕ)))⁻¹) hu
      rwa [e, inv_inv] at this
    have hp : valuation E ((ϖ ^ a : Eˣ) : E) < 1 := by
      rw [Units.val_zpow_eq_zpow_val, map_zpow₀, hϖ]
      exact zpow_lt_one₀ (zero_lt_iff.2 uniformizer_ne_zero) uniformizer_lt_one (by omega)
    obtain ⟨k, h1, h2, h3⟩ := not_intertwine (ϖ ^ a) hp (ψ.mulShift ((ϖ ^ (-c) : Eˣ) : E)) (fun x hx => by
      have h0 : 0 < valuation E ((ϖ ^ (-c) : Eˣ) : E) := zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 (Units.ne_zero _))
      have h4 : ¬ valuation E (((ϖ ^ (-c) : Eˣ) : E) * x) ≤ valuation E ((ϖ ^ (2 * a - c) : Eˣ) : E) := by
        rw [show 2 * a - c = -c + (a + a) by ring, _root_.zpow_add, _root_.zpow_add, Units.val_mul, Units.val_mul, map_mul, map_mul _ ((ϖ ^ (-c) : Eˣ) : E),
          mul_le_mul_iff_right₀ h0]
        exact not_le.2 hx
      rw [← hψ] at h4
      push Not at h4
      obtain ⟨y, h5, h6⟩ := h4
      refine ⟨((ϖ ^ (-c) : Eˣ) : E)⁻¹ * y, ?_, by rwa [AddChar.mulShift_apply, mul_inv_cancel_left₀ (Units.ne_zero _)]⟩
      rwa [map_mul, map_inv₀, inv_mul_le_iff₀ h0, ← map_mul]) (d⁻¹ * u * d) hu' fun h => hn (by
        have := (conj_mem ϖ a c _).2 h
        rw [← hd, show d * (d⁻¹ * u * d) * d⁻¹ = u by group] at this
        exact (hmem u).2 this)
    have e : u * (d * k * d⁻¹) * u⁻¹ = d * (d⁻¹ * u * d * k * (d⁻¹ * u * d)⁻¹) * d⁻¹ := by group
    refine ⟨d * k * d⁻¹, (hmem _).2 (hd ▸ (conj_mem ϖ a c k).2 h1), ?_, fun h => h3 (Circle.ext ?_)⟩
    · rw [e]
      generalize d⁻¹ * u * d * k * (d⁻¹ * u * d)⁻¹ = z at h2
      exact (hmem _).2 (hd ▸ (conj_mem ϖ a c z).2 h2)
    · rw [e] at h
      generalize d⁻¹ * u * d * k * (d⁻¹ * u * d)⁻¹ = z at h
      simp only [hd, conj_sd] at h
      exact h
  · rintro w ⟨u, x, rfl⟩
    exact ⟨u, u.2, x, by rw [whit_eq]⟩

theorem UpperTheory.ConvolutionTheory.Loc.howeLine :
    ∀ (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) E) V), IsSmooth π → π.IsIrreducible → GlobalTheory.LocGL.IsGeneric π → ∀ ϖ : Eˣ, valuation E (ϖ : E) = uniformizer E → ∀ c : ℤ, ∃ a₀ : ℤ, ∀ a ≥ a₀,
      ∀ ψ : AddChar E Circle, HasConductor ψ (ϖ ^ (2 * a - c)) → Module.finrank ℂ (howeSpace π ψ (howeSet n ϖ a c)) = 1 := by
  intro E _ _ _ _ n V _ _ π hs hi hg ϖ hϖ c
  obtain ⟨a₀, h⟩ := howeEx E n V π hs ϖ hϖ hg c
  refine ⟨max 1 a₀, fun a ha ψ hψ => ?_⟩
  have h1 := PositivityTheory.rg.gu.whit.whitLeOne E n ψ V π hs hi hψ.continuous hψ.ne_one
  let f := (twKer π (unipB E (Fin n)) (GlobalTheory.LocGL.whitChar ψ n)).mkQ ∘ₗ (howeSpace π ψ (howeSet n ϖ a c)).subtype
  have hf : Function.Injective f := (injective_iff_map_eq_zero f).2 fun v hv =>
    Subtype.ext (howeInj E n V π hs ϖ hϖ a c (le_trans (le_max_left _ _) ha) ψ hψ v.1 v.2 ((Submodule.Quotient.mk_eq_zero _).1 hv))
  have h2 : Module.rank ℂ (howeSpace π ψ (howeSet n ϖ a c)) ≤ 1 := (LinearMap.rank_le_of_injective f hf).trans h1
  have h3 := Submodule.nontrivial_iff_ne_bot.2 (h a (le_trans (le_max_right _ _) ha) ψ hψ)
  exact Module.finrank_eq_of_rank_eq (le_antisymm (by simpa using h2) (by simpa using Cardinal.one_le_iff_pos.2 rank_pos))
