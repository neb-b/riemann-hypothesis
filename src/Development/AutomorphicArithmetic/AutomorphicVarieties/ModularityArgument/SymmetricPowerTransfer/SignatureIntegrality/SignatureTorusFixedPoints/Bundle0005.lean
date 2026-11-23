module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.HodgeTateFromSandwich
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.ThFacts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0022

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.FinFacts
section
noncomputable section

open ValuativeRel Matrix Polynomial GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob

private theorem exists_finite_residue_reps_mod_natCast {G : Type} [CommGroup G] (K : Subgroup G) (P : G → Prop) (C : Finset G)
    (hC : ∀ u, P u → ∃ t ∈ C, P t ∧ u / t ∈ K) :
    ∃ R : Finset G, (∀ e ∈ R, e ∈ C ∧ P e) ∧ ∀ u, P u → ∃! e, e ∈ R ∧ u / e ∈ K := by
  classical
  have hq : ∀ u, P u → ∃ t, t ∈ C ∧ P t ∧ (QuotientGroup.mk t : G ⧸ K) = QuotientGroup.mk u := by
    intro u hu
    obtain ⟨t, ht, hPt, hut⟩ := hC u hu
    refine ⟨t, ht, hPt, ?_⟩
    rw [QuotientGroup.eq, mul_comm, ← div_eq_mul_inv]
    exact hut
  let f : G ⧸ K → G := fun q => if h : ∃ t, t ∈ C ∧ P t ∧ (QuotientGroup.mk t : G ⧸ K) = q then h.choose else 1
  have hf : ∀ t, t ∈ C → P t → f (QuotientGroup.mk t) ∈ C ∧ P (f (QuotientGroup.mk t)) ∧
      (QuotientGroup.mk (f (QuotientGroup.mk t)) : G ⧸ K) = QuotientGroup.mk t := by
    intro t ht hPt
    have h : ∃ s, s ∈ C ∧ P s ∧ (QuotientGroup.mk s : G ⧸ K) = QuotientGroup.mk t := ⟨t, ht, hPt, rfl⟩
    simp only [f, dif_pos h]
    exact h.choose_spec
  refine ⟨(C.filter P).image (fun t : G => f (QuotientGroup.mk t)), ?_, ?_⟩
  · intro e he
    rw [Finset.mem_image] at he
    obtain ⟨t, ht, rfl⟩ := he
    rw [Finset.mem_filter] at ht
    exact ⟨(hf t ht.1 ht.2).1, (hf t ht.1 ht.2).2.1⟩
  · intro u hu
    obtain ⟨t0, ht0, hPt0, ht0u⟩ := hq u hu
    refine ⟨f (QuotientGroup.mk t0), ⟨?_, ?_⟩, ?_⟩
    · rw [Finset.mem_image]
      exact ⟨t0, Finset.mem_filter.mpr ⟨ht0, hPt0⟩, rfl⟩
    · have h3 := (hf t0 ht0 hPt0).2.2.trans ht0u
      rw [QuotientGroup.eq] at h3
      rw [div_eq_mul_inv, mul_comm]
      exact h3
    · rintro e ⟨he, heu⟩
      rw [Finset.mem_image] at he
      obtain ⟨t, ht, rfl⟩ := he
      rw [Finset.mem_filter] at ht
      have h3 := (hf t ht.1 ht.2).2.2
      have htu : (QuotientGroup.mk t : G ⧸ K) = QuotientGroup.mk t0 := by
        rw [← h3, ht0u, QuotientGroup.eq, mul_comm, ← div_eq_mul_inv]
        exact heu
      rw [htu]

theorem UpperTheory.V.Z.Sym.Sig.finFacts : UpperTheory.V.Z.Sym.Sig.FinFacts := by
  intro k _ _ _ _ V
  let φ : kˣ →* GL (Fin 1) k := (diagT k (Fin 1)).comp
    { toFun := fun u _ => u, map_one' := rfl, map_mul' := fun _ _ => rfl }
  have hφc : Subgroup.comap φ (Kc k 1 (V.c + 1)) = Uc k (V.c + 1) := by
    ext u
    rw [Subgroup.mem_comap]
    exact (dg_mem_Kc (k := k) (n := 1) (c := V.c + 1) (s := fun _ => u)).trans (by simp)
  have hidx : (Uc k (V.c + 1)).relIndex (Uo k) ≠ 0 := by
    rw [← hφc, Subgroup.relIndex_comap]
    apply GlAx.Kc_index
    rw [Subgroup.map_le_iff_le_comap]
    intro u hu
    rw [Subgroup.mem_comap]
    exact dg_mem_KO (k := k) (n := 1) (s := fun _ => u) (fun _ => hu)
  have hH : V.H.relIndex (Uo k) ≠ 0 :=
    ne_zero_of_dvd_ne_zero hidx (Subgroup.relIndex_dvd_of_le_left _ V.le)
  have hH2 : V.H2 ≤ Uo k := by
    intro u hu
    have h2 : u ^ 2 ∈ Uo k := V.H_le hu
    have h2' : valuation k (u : k) * valuation k (u : k) = 1 := by
      have : valuation k ((u ^ 2 : kˣ) : k) = 1 := h2
      rw [Units.val_pow_eq_pow_val, map_pow, sq] at this
      exact this
    show valuation k (u : k) = 1
    rcases lt_trichotomy (valuation k (u : k)) 1 with h | h | h
    · exact absurd h2' (ne_of_lt (mul_lt_one_of_lt_of_le h h.le))
    · exact h
    · exact absurd h2' (ne_of_gt (one_lt_mul_of_lt_of_le h h.le))
  have hHH2 : V.H ≤ V.H2 := by
    intro u hu
    show u ^ 2 ∈ V.H
    exact V.H.pow_mem hu 2
  obtain ⟨T, hTU, hT⟩ : ∃ T : Finset kˣ, (∀ t ∈ T, t ∈ Uo k) ∧ ∀ u ∈ Uo k, ∃ t ∈ T, u / t ∈ V.H := by
    classical
    haveI : (V.H.subgroupOf (Uo k)).FiniteIndex := ⟨hH⟩
    haveI := Fintype.ofFinite (Uo k ⧸ V.H.subgroupOf (Uo k))
    refine ⟨Finset.univ.image (fun q : Uo k ⧸ V.H.subgroupOf (Uo k) => ((Quotient.out q : Uo k) : kˣ)), ?_, ?_⟩
    · intro t ht
      obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp ht
      exact (Quotient.out q).2
    · intro u hu
      refine ⟨((Quotient.out (QuotientGroup.mk ⟨u, hu⟩ : Uo k ⧸ V.H.subgroupOf (Uo k)) : Uo k) : kˣ),
        Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩, ?_⟩
      have h := QuotientGroup.out_eq' (QuotientGroup.mk ⟨u, hu⟩ : Uo k ⧸ V.H.subgroupOf (Uo k))
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at h
      rw [div_eq_mul_inv, mul_comm]
      simpa using h
  refine ⟨hH, hH2, hHH2, ?_, ?_, ?_⟩
  · obtain ⟨R, hR1, hR2⟩ := exists_finite_residue_reps_mod_natCast V.H (· ∈ V.H2) T (by
      intro u hu
      obtain ⟨t, ht, hut⟩ := hT u (hH2 hu)
      refine ⟨t, ht, ?_, hut⟩
      rw [← div_div_cancel u t]
      exact V.H2.div_mem hu (hHH2 hut))
    exact ⟨R, fun e he => (hR1 e he).2, hR2⟩
  · classical
    let S : Subgroup kˣ := V.H ⊔ (powMonoidHom 2 : kˣ →* kˣ).range
    have hS : ∀ u y : kˣ, u / y ∈ S ↔ ∃ s, u / (y * s ^ 2) ∈ V.H := by
      intro u y
      constructor
      · intro h
        obtain ⟨a, ha, b, ⟨s, rfl⟩, hab⟩ := Subgroup.mem_sup.mp h
        refine ⟨s, ?_⟩
        rw [← div_div, ← hab]
        simpa using ha
      · rintro ⟨s, hs⟩
        refine Subgroup.mem_sup.mpr ⟨_, hs, s ^ 2, ⟨s, rfl⟩, ?_⟩
        rw [← div_div, div_mul_cancel]
    have hcov : ∀ u : kˣ, ∃ t ∈ T ∪ T.image (fun t => unif k * t), True ∧ u / t ∈ S := by
      intro u
      set m := ord k u
      set w := u / unif k ^ m
      have hw : w ∈ Uo k := GlAx.val_div_ord u
      obtain ⟨t0, ht0, hwt⟩ := hT w hw
      set s := unif k ^ (m / 2)
      have hu_eq : u = w * unif k ^ (m % 2) * s ^ 2 := by
        have : unif k ^ m = unif k ^ (m % 2) * s ^ 2 := by
          rw [← zpow_natCast s 2, ← _root_.zpow_mul, ← _root_.zpow_add]
          congr 1
          push_cast
          omega
        rw [mul_assoc, ← this, div_mul_cancel]
      rcases Int.emod_two_eq_zero_or_one m with hr | hr
      · refine ⟨t0, Finset.mem_union_left _ ht0, trivial, (hS u t0).mpr ⟨s, ?_⟩⟩
        rw [hu_eq, hr, zpow_zero, mul_one, mul_div_mul_right_eq_div]
        exact hwt
      · refine ⟨unif k * t0, Finset.mem_union_right _ (Finset.mem_image.mpr ⟨t0, ht0, rfl⟩), trivial,
          (hS u _).mpr ⟨s, ?_⟩⟩
        rw [hu_eq, hr, zpow_one, mul_div_mul_right_eq_div, mul_comm (unif k) t0, mul_div_mul_right_eq_div]
        exact hwt
    obtain ⟨R, hR1, hR2⟩ := exists_finite_residue_reps_mod_natCast S (fun _ => True) (T ∪ T.image (fun t => unif k * t))
      (fun u _ => hcov u)
    refine ⟨R, ?_, ?_⟩
    · intro y hy
      have hyC := (hR1 y hy).1
      have hu1 : valuation k ((unif k : kˣ) : k) ≤ 1 := by
        rw [GlAx.unif_spec]
        exact ValuativeRel.uniformizer_lt_one.le
      rcases Finset.mem_union.mp hyC with hyT | hyT
      · have : valuation k (y : k) = 1 := hTU y hyT
        rw [this]
        exact ⟨hu1, le_rfl⟩
      · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hyT
        have : valuation k (t : k) = 1 := hTU t ht
        rw [Units.val_mul, map_mul, this, mul_one]
        exact ⟨le_rfl, hu1⟩
    · intro u
      obtain ⟨e, ⟨he, heu⟩, huniq⟩ := hR2 u trivial
      refine ⟨e, ⟨he, (hS u e).mp heu⟩, ?_⟩
      rintro y ⟨hy, hyu⟩
      exact huniq y ⟨hy, (hS u y).mpr hyu⟩
  · intro n
    have hopen : IsOpen (V.J n : Set (GL (Fin n) k)) := Subgroup.isOpen_mono (kc_le V) (isOpen_Kc _)
    have hcpt : IsCompact (V.J n : Set (GL (Fin n) k)) :=
      GlobalTheory.SplitFlip.isCompact_KO.of_isClosed_subset (Subgroup.isClosed_of_isOpen _ hopen) V.J_le_KO
    refine ⟨?_, hopen, hcpt, V.J_le_KO⟩
    intro x
    show (MulAction.orbit (V.J n) (x : GL (Fin n) k ⧸ V.J n)).Finite
    haveI := QuotientGroup.discreteTopology hopen
    refine ((hcpt.image (f := fun g => ((g * x : GL (Fin n) k) : GL (Fin n) k ⧸ V.J n))
      (QuotientGroup.continuous_mk.comp (continuous_mul_const x))).finite_of_discrete).subset ?_
    rintro _ ⟨j, rfl⟩
    exact ⟨j, j.2, rfl⟩

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.FixG
section
noncomputable section

open ValuativeRel Matrix Polynomial GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob

private theorem sDom_of_valuation_lt_one {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (a : kˣ) (h1 : valuation k (a : k) < 1) : SDom ![a, 1, a⁻¹] := by
  have hne : valuation k (a : k) ≠ 0 := ((valuation k).ne_zero_iff).mpr a.ne_zero
  have h2 : 1 < (valuation k (a : k))⁻¹ :=
    (one_lt_inv₀ (((valuation k).pos_iff).mpr a.ne_zero)).mpr h1
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp at hij ⊢
  · exact h1
  · exact h1.trans h2
  · exact h2

theorem UpperTheory.V.Z.Sym.Sig.fixG : UpperTheory.V.Z.Sym.Sig.FixG := by
  intro k _ _ _ _ V d hd x₁ y₁ z₁ hxz y
  have hF := thFacts k V
  have hth : ∀ g, th k 3 g = (Phi k)⁻¹ * th' k g * Phi k := fun g => by
    rw [mul_assoc, hF.2.2.2.2.2.2 g]
    group
  have hdom : Dom d := fun i j hij => by
    rcases hij.lt_or_eq with h | h
    · exact (hd i j h).le
    · rw [h]
  have hmul : ∀ {a b g : GL (Fin 3) k}, a ∈ V.J 3 → b ∈ V.J 3 → g ∈ V.DC d → a * g * b ∈ V.DC d := by
    intro a b g ha hb hg
    obtain ⟨p, hp, q, hq, rfl⟩ := hg
    exact ⟨a * p, (V.J 3).mul_mem ha hp, q * b, (V.J 3).mul_mem hq hb, by group⟩
  have hDC : ∀ {a b g : GL (Fin 3) k}, a ∈ V.J 3 → b ∈ V.J 3 → (a * g * b ∈ V.DC d ↔ g ∈ V.DC d) := by
    intro a b g ha hb
    refine ⟨fun h => ?_, hmul ha hb⟩
    have h2 := hmul ((V.J 3).inv_mem ha) ((V.J 3).inv_mem hb) h
    simpa [mul_assoc] using h2
  have hL : y⁻¹ * (dg ![x₁, y₁, z₁] * Phi k) * th k 3 y * (Phi k)⁻¹ = y⁻¹ * dg ![x₁, y₁, z₁] * th' k y := by
    rw [hth]
    group
  rw [hL]
  have key : ∀ (u : Fin 3 → kˣ) (j : GL (Fin 3) k), j ∈ V.J 3 → y = dg u * j →
      (y⁻¹ * dg ![x₁, y₁, z₁] * th' k y ∈ V.DC d ↔
        (x₁ / (u 0 * u 2) / d 0 ∈ V.H ∧ y₁ / u 1 ^ 2 / d 1 ∈ V.H ∧ z₁ / (u 0 * u 2) / d 2 ∈ V.H)) := by
    intro u j hj hy
    have hu3 : dg u = dg ![u 0, u 1, u 2] := by
      congr 1
      funext i
      fin_cases i <;> rfl
    have hc : (dg ![u 0, u 1, u 2])⁻¹ * dg ![x₁, y₁, z₁] * dg ![(u 2)⁻¹, (u 1)⁻¹, (u 0)⁻¹] =
        dg ![x₁ / (u 0 * u 2), y₁ / u 1 ^ 2, z₁ / (u 0 * u 2)] := by
      simp only [dg, ← map_inv, ← map_mul]
      congr 1
      funext i
      fin_cases i <;> simp [div_eq_mul_inv, sq, mul_comm, mul_left_comm, mul_assoc]
    have e1 : y⁻¹ * dg ![x₁, y₁, z₁] * th' k y =
        j⁻¹ * dg ![x₁ / (u 0 * u 2), y₁ / u 1 ^ 2, z₁ / (u 0 * u 2)] * th' k j := by
      rw [hy, map_mul, hu3, hF.2.2.1, ← hc]
      group
    rw [e1, hDC ((V.J 3).inv_mem hj) (hF.2.1 j hj), diagDC k V 3 d _ hdom]
    constructor
    · intro h
      exact ⟨by simpa using h 0, by simpa using h 1, by simpa using h 2⟩
    · rintro ⟨h0, h1, h2⟩ i
      fin_cases i
      · simpa using h0
      · simpa using h1
      · simpa using h2
  constructor
  · intro hg
    obtain ⟨j, hj, s, hs, hjs⟩ := contract k V 3 (th' k) hF.1 d hd _ hg
    obtain ⟨h, hh, rfl⟩ := hs
    have hhH : ∀ i, h i ∈ V.H := fun i => hh i (Set.mem_univ i)
    set g := y⁻¹ * dg ![x₁, y₁, z₁] * th' k y with hg_def
    have hD : dg ![x₁, y₁, z₁] * dg ![z₁⁻¹, y₁⁻¹, x₁⁻¹] = dg ![x₁ / z₁, 1, (x₁ / z₁)⁻¹] := by
      simp only [dg, ← map_mul]
      congr 1
      funext i
      fin_cases i <;> simp [div_eq_mul_inv, mul_comm]
    have A : g * th' k g = y⁻¹ * dg ![x₁ / z₁, 1, (x₁ / z₁)⁻¹] * y := by
      have : g * th' k g = y⁻¹ * (dg ![x₁, y₁, z₁] * th' k (dg ![x₁, y₁, z₁])) * y := by
        rw [hg_def, map_mul, map_mul, map_inv, Pres.invol hF.1]
        simp only [mul_assoc, mul_inv_cancel_left]
      rw [this, hF.2.2.1, hD]
    set p := h 0 * d 0 / (h 2 * d 2) with hp
    have C : diagT k (Fin 3) h * dg d * th' k (diagT k (Fin 3) h * dg d) = dg ![p, 1, p⁻¹] := by
      have e : diagT k (Fin 3) h * dg d = dg ![h 0 * d 0, h 1 * d 1, h 2 * d 2] := by
        simp only [dg, ← map_mul]
        congr 1
        funext i
        fin_cases i <;> rfl
      rw [e, hF.2.2.1]
      simp only [dg, ← map_mul]
      congr 1
      funext i
      fin_cases i <;> simp [hp, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
    have B : (j⁻¹ * g * th' k j) * th' k (j⁻¹ * g * th' k j) = j⁻¹ * (g * th' k g) * j := by
      simp only [map_mul, map_inv, Pres.invol hF.1]
      group
    rw [hjs, C, A] at B
    have hconj : (y * j)⁻¹ * dg ![x₁ / z₁, 1, (x₁ / z₁)⁻¹] * (y * j) = dg ![p, 1, p⁻¹] := by
      rw [B]
      group
    have hp1 : valuation k (p : k) < 1 := by
      have e2 : p = h 0 / h 2 * (d 0 / d 2) := by
        rw [hp, div_mul_div_comm]
      have hv1 : valuation k ((h 0 / h 2 : kˣ) : k) = 1 := V.H_le (V.H.div_mem (hhH 0) (hhH 2))
      rw [e2, Units.val_mul, map_mul, hv1, one_mul, Units.val_div_eq_div_val, map_div₀]
      exact (div_lt_one₀ (((valuation k).pos_iff).mpr (d 2).ne_zero)).mpr (hd 0 2 (by decide))
    obtain ⟨-, u, hu⟩ := conjDiag k 3 _ _ (sDom_of_valuation_lt_one _ hxz) (sDom_of_valuation_lt_one _ hp1) (y * j) hconj
    have hy : y = dg u * j⁻¹ := by
      rw [← hu]
      group
    exact ⟨u, j⁻¹, (V.J 3).inv_mem hj, hy, (key u j⁻¹ ((V.J 3).inv_mem hj) hy).mp hg⟩
  · rintro ⟨u, j, hj, hy, hc⟩
    exact (key u j hj hy).mpr hc

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.Link
section
noncomputable section

open ValuativeRel Matrix Polynomial GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob

theorem UpperTheory.V.Z.Sym.Sig.link : UpperTheory.V.Z.Sym.Sig.Link := by
  intro k _ _ _ _ n
  have hTiw : (Lev.iw k).TH n = (glIwa k n).T := by
    apply le_antisymm (Lev.levelTorus_le_torus _)
    rintro _ ⟨t, ht, rfl⟩
    exact ⟨t, fun i _ => ht i, rfl⟩
  have h2 : (Lev.iw k).J n = (glIwa k n).Iw 0 := by
    show (glIwa k n).N ⊔ (Lev.iw k).TH n ⊔ (glIwa k n).Nm 0 = (glIwa k n).N ⊔ (glIwa k n).T ⊔ (glIwa k n).Nm 0
    rw [hTiw]
  refine ⟨?_, h2, ?_⟩
  · obtain ⟨-, -, -, hU⟩ := memIwC k n ⊤
    have hK : Kc k n 1 = KOne k (Fin n) := by
      unfold Kc KOne
      congr 1
      ext g
      simp only [MonoidHom.mem_ker, Matrix.GeneralLinearGroup.ext_iff, GeneralLinearGroup.map_apply,
        Units.val_one, Matrix.one_apply]
      refine forall_congr' fun i => forall_congr' fun j => ?_
      have h1 : ∀ (I : Ideal 𝒪[k]) (x : 𝒪[k]), Ideal.Quotient.mk I x = 1 ↔ x - 1 ∈ I := fun I x => by
        rw [← map_one (Ideal.Quotient.mk I), Ideal.Quotient.eq]
      have h0 : ∀ (I : Ideal 𝒪[k]) (x : 𝒪[k]), Ideal.Quotient.mk I x = 0 ↔ x ∈ I :=
        fun I x => Ideal.Quotient.eq_zero_iff_mem
      split_ifs
      · rw [h1]
        erw [h1]
        rw [pow_one]
      · rw [h0]
        erw [h0]
        rw [pow_one]
    have hTor : Subgroup.map (diagT k (Fin n)) (torC k n ⊤) = (Lev.iw k).TH n := by
      congr 1
      ext t
      simp only [torC, Subgroup.mem_pi, Set.mem_univ, true_implies]
      exact forall_congr' fun i => hU (t i)
    apply le_antisymm
    · show (glIwa k n).N ⊔ (Lev.iw k).TH n ⊔ (glIwa k n).Nm 0 ≤
        KOne k (Fin n) ⊔ unipO k n ⊔ Subgroup.map (diagT k (Fin n)) (torC k n ⊤)
      refine sup_le (sup_le ?_ ?_) ?_
      · exact le_sup_right.trans le_sup_left
      · rw [← hTor]
        exact le_sup_right
      · intro x hx
        have h1 : x ∈ Kc k n 1 := hx.2
        rw [hK] at h1
        exact (le_sup_left.trans le_sup_left :
          KOne k (Fin n) ≤ KOne k (Fin n) ⊔ unipO k n ⊔ Subgroup.map (diagT k (Fin n)) (torC k n ⊤)) h1
    · show KOne k (Fin n) ⊔ unipO k n ⊔ Subgroup.map (diagT k (Fin n)) (torC k n ⊤) ≤
        (glIwa k n).N ⊔ (Lev.iw k).TH n ⊔ (glIwa k n).Nm 0
      refine sup_le (sup_le ?_ ?_) ?_
      · rw [← hK]
        exact kc_le (Lev.iw k)
      · exact (Lev.iw k).N_le
      · rw [hTor]
        exact le_sup_right.trans le_sup_left
  · intro c
    have hT : (Lev.deep k c).TH n = (glIwa k n).Tc c := by
      apply le_antisymm _ (Lev.Tc_le_TH _)
      rintro _ ⟨s, hs, rfl⟩
      exact ⟨Lev.levelTorus_le_torus _ ⟨s, hs, rfl⟩, dg_mem_Kc.mpr fun i => hs i trivial⟩
    show (glIwa k n).N ⊔ (Lev.deep k c).TH n ⊔ (glIwa k n).Nm c =
      (glIwa k n).N ⊔ (glIwa k n).Tc c ⊔ (glIwa k n).Nm c
    rw [hT]

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.StabFin
section
noncomputable section

open ValuativeRel Matrix Polynomial GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob

theorem UpperTheory.V.Z.Sym.Sig.stabFin : UpperTheory.V.Z.Sym.Sig.StabFin := by
  intro k _ _ _ _ V n y
  obtain ⟨a, ha⟩ := GlAx.exists_bd y
  obtain ⟨b, hb⟩ := GlAx.exists_bd y⁻¹
  have big : ∀ (g : GL (Fin n) k) (a : ℕ), GlAx.Bd (-a) g → ∀ i j, valuation k (g.val i j) ≤ uniformizer k ^ (-a : ℤ) := fun g a h i j => by
    have e : g.val i j = (g.val - 1) i j + (1 : Matrix (Fin n) (Fin n) k) i j := by simp
    rw [e]
    refine Valuation.map_add_le _ (h i j) ?_
    have hone : valuation k ((1 : Matrix (Fin n) (Fin n) k) i j) ≤ uniformizer k ^ (-a : ℤ) := by
      by_cases hij : i = j
      · subst j
        simp only [Matrix.one_apply_eq, map_one]
        rw [← zpow_zero (uniformizer k)]
        exact GlAx.zpow_le (by omega)
      · simp [Matrix.one_apply_ne hij]
    exact hone
  have key : ∀ u : Fin n → kˣ, (∀ i, u i ∈ Uc k (V.c + 1 + a + b)) → GlAx.Bd ((V.c + 1 : ℕ) : ℤ) (y⁻¹ * dg u * y) := fun u hu i j => by
    have e : (y⁻¹ * dg u * y).val - 1 = (y⁻¹).val * ((dg u).val - 1) * y.val := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, ← Units.val_mul y⁻¹ y, inv_mul_cancel]; rfl
    rw [e, Matrix.mul_apply]
    refine Valuation.map_sum_le _ fun r _ => ?_
    rw [Matrix.mul_apply, Finset.sum_mul]
    refine Valuation.map_sum_le _ fun q _ => ?_
    rw [map_mul, map_mul]
    refine (mul_le_mul' (mul_le_mul' (big _ b hb i q) ((GlAx.mem_Kc.1 (dg_mem_Kc.2 hu)).1 q r)) (big _ a ha r j)).trans_eq ?_
    rw [← zpow_add₀ GlAx.unif_pos.ne', ← zpow_add₀ GlAx.unif_pos.ne']
    congr 1; push_cast; ring
  refine ⟨V.c + 1 + a + b, fun u hu => ?_⟩
  have h : y⁻¹ * dg u * y ∈ Kc k n (V.c + 1) := GlAx.mem_Kc.2 ⟨key u hu, by
    have := key u⁻¹ fun i => inv_mem (hu i)
    rw [dg, map_inv] at this
    convert this using 1; group⟩
  have h1 := (GlAx.mem_Kc.1 h).1
  have h0 := GlAx.bd_zero.1 (GlAx.mem_KO.1 (GlAx.Kc_le _ h)).1
  generalize y⁻¹ * dg u * y = g at h h1 h0
  refine (memJ k V n g).2 ⟨h0, fun i j hij => ?_, fun i => ?_⟩
  · have := h1 i j
    rw [Matrix.sub_apply, one_apply_ne hij.ne', sub_zero, zpow_natCast] at this
    rwa [GlAx.unif_spec]
  · have := h1 i i
    rw [Matrix.sub_apply, one_apply_eq] at this
    have h2 : valuation k (g.val i i - 1) < 1 := this.trans_lt (zpow_lt_one₀ GlAx.unif_pos uniformizer_lt_one (by omega))
    have h3 : valuation k (g.val i i) = 1 := by
      have := Valuation.map_one_add_of_lt _ h2
      rwa [add_sub_cancel] at this
    exact ⟨Units.mk0 _ (fun h => by simp [h] at h3), V.le (mem_Uc.2 ⟨h3, this⟩), rfl⟩

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.UnitaryDoubleCosetIndicatorAlt
section
noncomputable section

open ValuativeRel Matrix Polynomial GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob

theorem UpperTheory.V.Z.Sym.Sig.supp0 : UpperTheory.V.Z.Sym.Sig.Supp0 := by
  intro k _ _ _ _ V d hd g hg
  have hmem : g * (Phi k)⁻¹ ∈ V.DC d := by
    by_contra h
    exact hg (by simp [Lev.unitaryDoubleCosetIndicator, h])
  obtain ⟨hP, -, -, -, -, -, hcomm⟩ := thFacts k V
  obtain ⟨j, -, s, hs, hjs⟩ := contract k V 3 (th' k) hP d hd _ hmem
  obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hs
  refine ⟨j, t 0 * d 0, t 1 * d 1, t 2 * d 2, ?_, ?_⟩
  · have h1 : dg ![t 0 * d 0, t 1 * d 1, t 2 * d 2] = diagT k (Fin 3) t * dg d := by
      rw [dg, ← map_mul]
      congr 1
      funext i
      fin_cases i <;> rfl
    rw [h1, ← hjs]
    have h2 : th' k j * Phi k = Phi k * th k 3 j := hcomm j
    symm
    calc j * (j⁻¹ * (g * (Phi k)⁻¹) * th' k j) * Phi k * (th k 3 j)⁻¹
        = g * (Phi k)⁻¹ * (th' k j * Phi k) * (th k 3 j)⁻¹ := by group
      _ = g := by rw [h2]; group
  · have h3 : t 0 * d 0 / (t 2 * d 2) / (d 0 / d 2) = t 0 / t 2 := by
      rw [mul_div_mul_comm, mul_div_cancel_right]
    rw [h3]
    exact div_mem (ht 0 trivial) (ht 2 trivial)

end
end

