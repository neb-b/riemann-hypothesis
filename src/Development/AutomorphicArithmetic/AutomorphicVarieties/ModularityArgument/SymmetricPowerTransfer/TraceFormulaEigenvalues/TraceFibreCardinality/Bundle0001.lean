module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.Bundle0001
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0003

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.TraceFibreCardinality.CentFin
section
open UpperTheory.V.Z.Sym in
theorem UpperTheory.V.Z.Sym.Tf.centFin :
    UpperTheory.V.Z.Sym.Tf.CentFin := by
  intro Γ G V _ _ _ _ B hB tw f hf δ
  classical
  obtain ⟨S₀, hS₀⟩ := hB.cls
  choose D hD using fun g : G => UpperTheory.V.Z.Sym.Tf.finD B hB tw f hf g g
  let rep : G → Γ → Γ := fun g d =>
    if h : ∃ γ : Γ, ∃ z ∈ B.Γ₀, γ⁻¹ * δ * tw.θΓ γ = d * z then h.choose else 1
  have rep_spec : ∀ g d, (∃ γ : Γ, ∃ z ∈ B.Γ₀, γ⁻¹ * δ * tw.θΓ γ = d * z) →
      ∃ z ∈ B.Γ₀, (rep g d)⁻¹ * δ * tw.θΓ (rep g d) = d * z := by
    intro g d h
    simp only [rep, dif_pos h]
    exact h.choose_spec
  refine ⟨S₀.biUnion (fun g => (D g).image (fun d => B.ι (rep g d) * g)), ?_⟩
  intro y hy
  obtain ⟨γ, g, hg, u, hu, rfl⟩ := hS₀ y
  have hcomm : ∀ c : Γ, tw.θ (B.ι c) = B.ι (tw.θΓ c) := tw.comm
  have expand : (B.ι γ * g * u)⁻¹ * B.ι δ * tw.θ (B.ι γ * g * u) =
      u⁻¹ * (g⁻¹ * B.ι (γ⁻¹ * δ * tw.θΓ γ) * tw.θ g) * tw.θ u := by
    simp only [map_mul, map_inv, hcomm]
    group
  have hne : f (g⁻¹ * B.ι (γ⁻¹ * δ * tw.θΓ γ) * tw.θ g) ≠ 0 := by
    intro h0
    apply hy
    show f ((B.ι γ * g * u)⁻¹ * B.ι δ * tw.θ (B.ι γ * g * u)) = 0
    rw [expand]
    have e1 := hf.right ⟨u, hu⟩ (u⁻¹ * (g⁻¹ * B.ι (γ⁻¹ * δ * tw.θΓ γ) * tw.θ g))
    have e2 := hf.left ⟨u⁻¹, B.U.inv_mem hu⟩ (g⁻¹ * B.ι (γ⁻¹ * δ * tw.θΓ γ) * tw.θ g)
    simp only at e1 e2
    rw [e1, e2, h0, mul_zero, mul_zero]
  obtain ⟨d, hd, z₂, hz₂, hγ⟩ := hD g (γ⁻¹ * δ * tw.θΓ γ) hne
  obtain ⟨z₁, hz₁, hr⟩ := rep_spec g d ⟨γ, z₂, hz₂, hγ⟩
  set r := rep g d with hr_def
  have hdr : d = r⁻¹ * δ * tw.θΓ r * z₁⁻¹ := eq_mul_inv_of_mul_eq hr.symm
  have hc : z₁⁻¹ * z₂ ∈ Subgroup.center Γ :=
    B.cenΓ (B.Γ₀.mul_mem (B.Γ₀.inv_mem hz₁) hz₂)
  have hx : γ * r⁻¹ ∈ tw.Cent δ := by
    refine ⟨z₁⁻¹ * z₂, B.Γ₀.mul_mem (B.Γ₀.inv_mem hz₁) hz₂, ?_⟩
    calc (γ * r⁻¹)⁻¹ * δ * tw.θΓ (γ * r⁻¹)
        = r * (γ⁻¹ * δ * tw.θΓ γ) * (tw.θΓ r)⁻¹ := by
          simp only [map_mul, map_inv]
          group
      _ = r * (d * z₂) * (tw.θΓ r)⁻¹ := by rw [hγ]
      _ = δ * (tw.θΓ r * (z₁⁻¹ * z₂)) * (tw.θΓ r)⁻¹ := by
          rw [hdr]
          group
      _ = δ * ((z₁⁻¹ * z₂) * tw.θΓ r) * (tw.θΓ r)⁻¹ := by
          rw [(Subgroup.mem_center_iff.mp hc (tw.θΓ r)).symm]
      _ = δ * (z₁⁻¹ * z₂) := by group
  refine ⟨⟨γ * r⁻¹, hx⟩, B.ι r * g, ?_, u, hu, ?_⟩
  · exact Finset.mem_biUnion.mpr ⟨g, hg, Finset.mem_image.mpr ⟨d, hd, rfl⟩⟩
  · show B.ι γ * g * u = B.ι (γ * r⁻¹) * (B.ι r * g) * u
    rw [map_mul, map_inv]
    group
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.TraceFibreCardinality.EigVec
section
noncomputable section

namespace UpperTheory.V.Z.Sym.Tf

private lemma exists_ker_of_pow {M : Type} [AddCommGroup M] [Module ℂ M] (N : Module.End ℂ M) (W : Submodule ℂ M)
    (hW : ∀ w ∈ W, N w ∈ W) : ∀ (k : ℕ) (v : M), v ∈ W → v ≠ 0 → (N ^ k) v = 0 → ∃ w ∈ W, w ≠ 0 ∧ N w = 0 := by
  intro k
  induction k with
  | zero => intro v _ hv h; exact absurd (by simpa using h) hv
  | succ k ih =>
    intro v hvW hv h
    by_cases h0 : N v = 0
    · exact ⟨v, hvW, hv, h0⟩
    · exact ih (N v) (hW v hvW) h0 (by rw [pow_succ] at h; exact h)

theorem eigVec : EigVec := by
  intro Λ M _ _ _ u hc χ
  constructor
  · intro h
    set E : Submodule ℂ M := ⨅ a, (u a).maxGenEigenspace (χ a) with hE
    let S : Set (Submodule ℂ M) := {W | W ≠ ⊥ ∧ W ≤ E ∧ ∀ b, ∀ w ∈ W, u b w ∈ W}
    have hS : S.Nonempty := by
      refine ⟨E, h, le_rfl, fun b w hw => ?_⟩
      rw [hE, Submodule.mem_iInf] at hw ⊢
      intro a
      exact Module.End.mapsTo_maxGenEigenspace_of_comm (hc a b) (χ a) (hw a)
    obtain ⟨W, ⟨hW0, hWE, hWs⟩, hmin⟩ := (wellFounded_lt (α := Submodule ℂ M)).has_min S hS
    obtain ⟨v, hvW, hv⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
    refine ⟨v, hv, fun a => ?_⟩
    have key : W ⊓ (u a).eigenspace (χ a) ∈ S := by
      refine ⟨?_, inf_le_left.trans hWE, fun b w hw => ⟨hWs b w hw.1, ?_⟩⟩
      · have hva : v ∈ (u a).maxGenEigenspace (χ a) := by
          have := hWE hvW
          rw [hE, Submodule.mem_iInf] at this
          exact this a
        obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace _ _ _).1 hva
        obtain ⟨w, hwW, hw, hN⟩ := exists_ker_of_pow (u a - χ a • (1 : Module.End ℂ M)) W
          (fun w hw => by
            simpa using W.sub_mem (hWs a w hw) (W.smul_mem (χ a) hw)) k v hvW hv hk
        refine (Submodule.ne_bot_iff _).2 ⟨w, ⟨hwW, ?_⟩, hw⟩
        refine Module.End.mem_eigenspace_iff.2 ?_
        simpa [sub_eq_zero] using hN
      · have h2 := Module.End.mem_eigenspace_iff.1 hw.2
        refine Module.End.mem_eigenspace_iff.2 ?_
        have h3 : u a (u b w) = u b (u a w) := congrArg (fun f : Module.End ℂ M => f w) (hc a b).eq
        rw [h3, h2, map_smul]
    have heq : W ⊓ (u a).eigenspace (χ a) = W := by
      by_contra hne
      exact hmin _ key (lt_of_le_of_ne inf_le_left hne)
    rw [← heq] at hvW
    exact Module.End.mem_eigenspace_iff.1 hvW.2
  · rintro ⟨v, hv, h⟩
    refine (Submodule.ne_bot_iff _).2 ⟨v, ?_, hv⟩
    rw [Submodule.mem_iInf]
    intro a
    exact (Module.End.mem_maxGenEigenspace _ _ _).2 ⟨1, by simp [h a]⟩

end UpperTheory.V.Z.Sym.Tf
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.TraceFibreCardinality.Extract
section
private theorem artin {P : Type} [Mul P] (T : Finset (P → ℂ)) : ∀ c : (P → ℂ) → ℂ,
    (∀ χ ∈ T, χ ≠ 0 ∧ ∀ p q, χ (p * q) = χ p * χ q) → (∀ p, ∑ χ ∈ T, c χ * χ p = 0) → ∀ χ ∈ T, c χ = 0 :=
  _root_.UpperTheory.Reformulated.B.Qh30.artin T

private theorem grp {P I : Type} [DecidableEq (P → ℂ)] (S : Finset I) (a : I → ℂ) (α : I → P → ℂ) (T : Finset (P → ℂ))
    (h : ∀ i ∈ S, α i ≠ 0 → α i ∈ T) (p : P) :
    ∑ χ ∈ T, (∑ i ∈ S.filter (fun i => α i = χ), a i) * χ p = ∑ i ∈ S, a i * α i p := by
  simp only [Finset.sum_filter, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i hi => ?_
  by_cases h0 : α i = 0
  · rw [h0]; simp only [Pi.zero_apply, mul_zero]
    refine Finset.sum_eq_zero fun χ _ => ?_
    split_ifs with e
    · subst e; simp
    · simp
  · rw [Finset.sum_eq_single (α i) (fun χ _ e => by simp [e.symm]) fun e => absurd (h i hi h0) e]; simp

theorem UpperTheory.V.Z.Sym.Tf.extract :
    UpperTheory.V.Z.Sym.Tf.Extract := by
  classical
  intro P I J _ S S' a b α β hα hβ h χ hχ hb
  by_contra hn
  push Not at hn
  set T := (S.image α ∪ S'.image β).filter (· ≠ 0) with hT
  have key := artin T (fun χ => ∑ i ∈ S.filter (fun i => α i = χ), a i - ∑ j ∈ S'.filter (fun j => β j = χ), b j)
    (fun ψ hψ => by
      simp only [hT, Finset.mem_filter, Finset.mem_union, Finset.mem_image] at hψ
      refine ⟨hψ.2, ?_⟩
      rcases hψ.1 with ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩
      exacts [hα i hi, hβ i hi])
    (fun p => by
      simp only [sub_mul, Finset.sum_sub_distrib]
      rw [grp S a α T (fun i hi h0 => by simp only [hT, Finset.mem_filter, Finset.mem_union, Finset.mem_image]; exact ⟨.inl ⟨i, hi, rfl⟩, h0⟩),
        grp S' b β T (fun i hi h0 => by simp only [hT, Finset.mem_filter, Finset.mem_union, Finset.mem_image]; exact ⟨.inr ⟨i, hi, rfl⟩, h0⟩),
        h, sub_self])
  obtain ⟨j, hj, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero hb
  have hj' := Finset.mem_filter.1 hj
  have := key χ (by simp only [hT, Finset.mem_filter, Finset.mem_union, Finset.mem_image]; exact ⟨.inr ⟨j, hj'.1, hj'.2⟩, hχ⟩)
  rw [Finset.sum_eq_zero (s := S.filter _) fun i hi => by
    by_contra e; exact hn i (Finset.mem_filter.1 hi).1 e (Finset.mem_filter.1 hi).2, zero_sub, neg_eq_zero] at this
  exact hb (by convert this)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.TraceFibreCardinality.FormsFin
section
theorem UpperTheory.V.Z.Sym.Tf.formsFin :
    UpperTheory.V.Z.Sym.Tf.FormsFin := by
  intro Γ G V _ _ _ _ _ B hB
  obtain ⟨S, hS⟩ := hB.cls
  let L : B.Forms →ₗ[ℂ] (S → V) :=
    (LinearMap.funLeft ℂ V (fun s : S => (s : G))).comp B.Forms.subtype
  refine Module.Finite.of_injective L ?_
  intro φ ψ h
  apply Subtype.ext
  funext g
  obtain ⟨γ, s, hs, u, hu, rfl⟩ := hS g
  have hsv : φ.1 s = ψ.1 s := congrFun h ⟨s, hs⟩
  have e1 : φ.1 (B.ι γ * s * u) = (B.ω ⟨u, hu⟩ : ℂ) • φ.1 (B.ι γ * s) := φ.2.2 _ ⟨u, hu⟩
  have e2 : ψ.1 (B.ι γ * s * u) = (B.ω ⟨u, hu⟩ : ℂ) • ψ.1 (B.ι γ * s) := ψ.2.2 _ ⟨u, hu⟩
  have f1 : φ.1 (B.ι γ * s) = B.W γ (φ.1 s) := φ.2.1 γ s
  have f2 : ψ.1 (B.ι γ * s) = B.W γ (ψ.1 s) := ψ.2.1 γ s
  rw [e1, e2, f1, f2, hsv]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.TraceFibreCardinality.GqIndex
section
noncomputable section

namespace UpperTheory.V.Z.Sym.Tf

open MulAction

section

variable {H' H Y : Type} [Group H'] [Group H] [MulAction H Y] [MulAction H' Y]

private theorem orb_iff (φ : H' →* H) (hφ : ∀ (a : H') (y : Y), a • y = φ a • y) (H₀ : Subgroup H) [H₀.Normal]
    (h0 : ∀ z ∈ H₀, ∀ y : Y, z • y = y) (y y' : Y) :
    (Quotient.mk (orbitRel H' Y) y = Quotient.mk (orbitRel H' Y) y') ↔ ∃ c ∈ φ.range ⊔ H₀, c • y' = y := by
  rw [Quotient.eq, orbitRel_apply, mem_orbit_iff]
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨φ a, Subgroup.mem_sup_left ⟨a, rfl⟩, (hφ a y').symm⟩
  · rintro ⟨c, hc, rfl⟩
    obtain ⟨_, ⟨a, rfl⟩, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 hc
    exact ⟨a, by rw [hφ, mul_smul, h0 z hz]⟩

private theorem w_mul (φ : H' →* H) (hφ : ∀ (a : H') (y : Y), a • y = φ a • y) (H₀ : Subgroup H) [H₀.Normal]
    (h0 : ∀ z ∈ H₀, ∀ y : Y, z • y = y) (y : Y) :
    (H₀.comap φ).relIndex (stabilizer H' y) * (φ.range ⊔ H₀).relIndex (stabilizer H y) = H₀.relIndex (stabilizer H y) := by
  have hH₀S : H₀ ≤ stabilizer H y := fun z hz => h0 z hz y
  have hS' : stabilizer H' y = (stabilizer H y).comap φ := by
    ext a
    simp [mem_stabilizer_iff, hφ]
  have hdk : (φ.range ⊔ H₀) ⊓ stabilizer H y = (φ.range ⊓ stabilizer H y) ⊔ H₀ := by
    ext x
    simp only [Subgroup.mem_inf, Subgroup.mem_sup_of_normal_right]
    constructor
    · rintro ⟨⟨p, hp, z, hz, rfl⟩, hx⟩
      refine ⟨p, ⟨hp, ?_⟩, z, hz, rfl⟩
      have hpz : p = (p * z) * z⁻¹ := by group
      rw [hpz]
      exact Subgroup.mul_mem _ hx (Subgroup.inv_mem _ (hH₀S hz))
    · rintro ⟨p, ⟨hp, hpS⟩, z, hz, rfl⟩
      exact ⟨⟨p, hp, z, hz, rfl⟩, Subgroup.mul_mem _ hpS (hH₀S hz)⟩
  rw [hS', Subgroup.relIndex_comap, Subgroup.map_comap_eq,
    ← Subgroup.relIndex_sup_right (φ.range ⊓ stabilizer H y) H₀, ← hdk,
    ← Subgroup.inf_relIndex_right (φ.range ⊔ H₀) (stabilizer H y)]
  exact Subgroup.relIndex_mul_relIndex _ _ _ (le_inf le_sup_right hH₀S) inf_le_right

private theorem fib_card (K : Subgroup H) (g : H) (y : Y) :
    {x : H ⧸ K | ∃ c ∈ K, c • y = x.out⁻¹ • g • y}.ncard = K.relIndex (stabilizer H y) := by
  classical
  let f : stabilizer H y ⧸ K.subgroupOf (stabilizer H y) → H ⧸ K :=
    Quotient.map' (fun s : stabilizer H y => g * (s : H)) (fun a b hab => by
      rw [QuotientGroup.leftRel_apply] at hab ⊢
      rw [Subgroup.mem_subgroupOf] at hab
      simpa [mul_assoc] using hab)
  have hf : ∀ s : stabilizer H y, f (QuotientGroup.mk s) = QuotientGroup.mk (g * (s : H)) := fun s => rfl
  have hinj : Function.Injective f := by
    intro a b hab
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    rw [hf, hf, QuotientGroup.eq] at hab
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simpa [mul_assoc] using hab
  have hrange : {x : H ⧸ K | ∃ c ∈ K, c • y = x.out⁻¹ • g • y} = Set.range f := by
    ext x
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨k0, hout⟩ := QuotientGroup.mk_out_eq_mul K h
    simp only [Set.mem_setOf_eq, Set.mem_range, hout]
    constructor
    · rintro ⟨c, hc, hcy⟩
      have hs : g⁻¹ * (h * k0 * c) ∈ stabilizer H y := by
        rw [mem_stabilizer_iff, mul_smul, mul_smul, hcy, ← mul_smul, ← mul_smul]
        simp only [mul_inv_rev]
        rw [← mul_smul, show g⁻¹ * (h * (k0 : H)) * ((k0 : H)⁻¹ * h⁻¹) * g = 1 by group, one_smul]
      refine ⟨QuotientGroup.mk ⟨g⁻¹ * (h * k0 * c), hs⟩, ?_⟩
      rw [hf, QuotientGroup.eq]
      have hm : (c⁻¹ * (k0 : H)⁻¹) ∈ K := K.mul_mem (K.inv_mem hc) (K.inv_mem k0.2)
      simpa [mul_assoc] using hm
    · rintro ⟨q, hq⟩
      obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective q
      rw [hf, QuotientGroup.eq] at hq
      refine ⟨(h * k0)⁻¹ * (g * s), ?_, ?_⟩
      · have hm := K.mul_mem (K.inv_mem k0.2) (K.inv_mem hq)
        simpa [mul_assoc] using hm
      · rw [mul_smul, mul_smul, mem_stabilizer_iff.mp s.2]
  rw [hrange, ← Nat.card_coe_set_eq, Nat.card_range_of_injective hinj]
  rfl

private theorem w_conj (H₀ : Subgroup H) [hN : H₀.Normal] (g : H) (y : Y) :
    H₀.relIndex (stabilizer H (g • y)) = H₀.relIndex (stabilizer H y) := by
  have hmap : H₀.map (MulAut.conj g).toMonoidHom = H₀ := by
    ext x
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact hN.conj_mem a ha g
    · intro hx
      exact ⟨g⁻¹ * x * g, by simpa using hN.conj_mem x hx g⁻¹, by simp [mul_assoc]⟩
  rw [stabilizer_smul_eq_stabilizer_map_conj]
  conv_lhs => rw [← hmap]
  exact Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective

private theorem gq_index (φ : H' →* H) (hφ : ∀ (a : H') (y : Y), a • y = φ a • y) (H₀ : Subgroup H) [H₀.Normal]
    (h0 : ∀ z ∈ H₀, ∀ y : Y, z • y = y) (k : Y → ℂ) (hn : (φ.range ⊔ H₀).index ≠ 0) (hk : ∀ (h : H) y, k (h • y) = k y)
    (hS : ∃ S : Finset Y, ∀ y, k y ≠ 0 → ∃ h : H, ∃ x ∈ S, y = h • x)
    (hw : ∀ y, k y ≠ 0 → H₀.relIndex (stabilizer H y) ≠ 0) :
    gq (H₀.comap φ) k = ((φ.range ⊔ H₀).index : ℂ) * gq H₀ k := by
  classical
  haveI : (φ.range ⊔ H₀).FiniteIndex := ⟨hn⟩
  letI : Fintype (H ⧸ (φ.range ⊔ H₀)) := Fintype.ofFinite _
  obtain ⟨S0, hS0⟩ := hS
  let π : orbitRel.Quotient H' Y → orbitRel.Quotient H Y := fun q' => Quotient.mk (orbitRel H Y) q'.out
  let T : orbitRel.Quotient H Y → ℂ := fun q =>
    k q.out / (H₀.relIndex (stabilizer H q.out) : ℂ)
  let T' : orbitRel.Quotient H' Y → ℂ := fun q' =>
    k q'.out / ((H₀.comap φ).relIndex (stabilizer H' q'.out) : ℂ)
  have hgq : gq H₀ k = ∑ᶠ q, T q := rfl
  have hgq' : gq (H₀.comap φ) k = ∑ᶠ q', T' q' := rfl
  have mkH_smul : ∀ (h : H) (y : Y), Quotient.mk (orbitRel H Y) (h • y) = Quotient.mk (orbitRel H Y) y := by
    intro h y
    exact Quotient.sound (orbitRel_apply.mpr ⟨h, rfl⟩)
  have mkH_of : ∀ a b : Y, Quotient.mk (orbitRel H' Y) a = Quotient.mk (orbitRel H' Y) b →
      Quotient.mk (orbitRel H Y) a = Quotient.mk (orbitRel H Y) b := by
    intro a b hab
    obtain ⟨c, -, hc⟩ := (orb_iff φ hφ H₀ h0 a b).mp hab
    rw [← hc, mkH_smul]
  have hsame : ∀ q', ∃ h : H, (π q').out = h • q'.out := by
    intro q'
    have e : Quotient.mk (orbitRel H Y) (π q').out = Quotient.mk (orbitRel H Y) q'.out := Quotient.out_eq _
    obtain ⟨h, hh⟩ := mem_orbit_iff.mp (orbitRel_apply.mp (Quotient.exact e))
    exact ⟨h, hh.symm⟩
  have hT' : ∀ q', T' q' = T (π q') * ((φ.range ⊔ H₀).relIndex (stabilizer H q'.out) : ℂ) := by
    intro q'
    obtain ⟨h, hh⟩ := hsame q'
    show k q'.out / ((H₀.comap φ).relIndex (stabilizer H' q'.out) : ℂ) =
      k (π q').out / (H₀.relIndex (stabilizer H (π q').out) : ℂ) *
        ((φ.range ⊔ H₀).relIndex (stabilizer H q'.out) : ℂ)
    rw [hh, hk, w_conj]
    by_cases hk0 : k q'.out = 0
    · simp [hk0]
    · have hw0 := hw _ hk0
      have hm := w_mul φ hφ H₀ h0 q'.out
      rw [← hm] at hw0 ⊢
      have h1 : ((H₀.comap φ).relIndex (stabilizer H' q'.out) : ℂ) ≠ 0 := by
        exact_mod_cast left_ne_zero_of_mul hw0
      have h2 : ((φ.range ⊔ H₀).relIndex (stabilizer H q'.out) : ℂ) ≠ 0 := by
        exact_mod_cast right_ne_zero_of_mul hw0
      push_cast
      field_simp
  let Q0 : Finset (orbitRel.Quotient H Y) := S0.image (fun s => Quotient.mk (orbitRel H Y) s)
  let Q0' : Finset (orbitRel.Quotient H' Y) :=
    (S0 ×ˢ (Finset.univ : Finset (H ⧸ (φ.range ⊔ H₀)))).image
      (fun p => Quotient.mk (orbitRel H' Y) (p.2.out⁻¹ • p.1))
  have inQ0' : ∀ s ∈ S0, ∀ h : H, Quotient.mk (orbitRel H' Y) (h • s) ∈ Q0' := by
    intro s hs h
    obtain ⟨l, hl⟩ := QuotientGroup.mk_out_eq_mul (φ.range ⊔ H₀) h⁻¹
    refine Finset.mem_image.mpr ⟨(s, QuotientGroup.mk h⁻¹), Finset.mem_product.mpr ⟨hs, Finset.mem_univ _⟩, ?_⟩
    show Quotient.mk (orbitRel H' Y) ((QuotientGroup.mk h⁻¹ : H ⧸ (φ.range ⊔ H₀)).out⁻¹ • s) =
      Quotient.mk (orbitRel H' Y) (h • s)
    rw [orb_iff φ hφ H₀ h0]
    refine ⟨(l : H)⁻¹, Subgroup.inv_mem _ l.2, ?_⟩
    rw [hl, mul_inv_rev, inv_inv, mul_smul]
  have hsuppT : Function.support T ⊆ ↑Q0 := by
    intro q hq
    have hk0 : k q.out ≠ 0 := by
      intro h
      exact hq (by simp [T, h])
    obtain ⟨h, x, hx, hxq⟩ := hS0 _ hk0
    refine Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨x, hx, ?_⟩)
    rw [← mkH_smul h x, ← hxq, Quotient.out_eq]
  have hsuppT' : Function.support T' ⊆ ↑Q0' := by
    intro q' hq'
    have hk0 : k q'.out ≠ 0 := by
      intro h
      exact hq' (by simp [T', h])
    obtain ⟨h, x, hx, hxq⟩ := hS0 _ hk0
    have := inQ0' x hx h
    rw [← hxq, Quotient.out_eq] at this
    exact Finset.mem_coe.mpr this
  have hmaps : ∀ q' ∈ Q0', π q' ∈ Q0 := by
    intro q' hq'
    obtain ⟨⟨s, x⟩, hp, rfl⟩ := Finset.mem_image.mp hq'
    refine Finset.mem_image.mpr ⟨s, (Finset.mem_product.mp hp).1, ?_⟩
    show Quotient.mk (orbitRel H Y) s = Quotient.mk (orbitRel H Y)
      (Quotient.mk (orbitRel H' Y) (x.out⁻¹ • s)).out
    rw [mkH_of _ (x.out⁻¹ • s) (Quotient.out_eq _), mkH_smul]
  have hfib : ∀ q ∈ Q0, ∑ q' ∈ Q0' with π q' = q,
      ((φ.range ⊔ H₀).relIndex (stabilizer H q'.out) : ℂ) = ((φ.range ⊔ H₀).index : ℂ) := by
    intro q hq
    obtain ⟨s, hs, hsq⟩ := Finset.mem_image.mp hq
    let Φ : H ⧸ (φ.range ⊔ H₀) → orbitRel.Quotient H' Y := fun x => Quotient.mk (orbitRel H' Y) (x.out⁻¹ • q.out)
    obtain ⟨h1, hh1⟩ : ∃ h1 : H, q.out = h1 • s := by
      have e : Quotient.mk (orbitRel H Y) q.out = Quotient.mk (orbitRel H Y) s := by rw [Quotient.out_eq, hsq]
      obtain ⟨h, hh⟩ := mem_orbit_iff.mp (orbitRel_apply.mp (Quotient.exact e))
      exact ⟨h, hh.symm⟩
    have hΦ : Set.MapsTo Φ ↑(Finset.univ : Finset (H ⧸ (φ.range ⊔ H₀))) ↑(Q0'.filter (fun q' => π q' = q)) := by
      intro x _
      refine Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨?_, ?_⟩)
      · show Quotient.mk (orbitRel H' Y) (x.out⁻¹ • q.out) ∈ Q0'
        rw [hh1, ← mul_smul]
        exact inQ0' s hs _
      · show Quotient.mk (orbitRel H Y) (Quotient.mk (orbitRel H' Y) (x.out⁻¹ • q.out)).out = q
        rw [mkH_of _ (x.out⁻¹ • q.out) (Quotient.out_eq _), mkH_smul, Quotient.out_eq]
    have hcard := Finset.card_eq_sum_card_fiberwise hΦ
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, ← Subgroup.index_eq_card] at hcard
    rw [hcard]
    push_cast
    refine Finset.sum_congr rfl fun q' hq' => ?_
    have hπ : π q' = q := (Finset.mem_filter.mp hq').2
    obtain ⟨g, hg⟩ := hsame q'
    rw [hπ] at hg
    have hset : ((Finset.univ.filter (fun x => Φ x = q') : Finset (H ⧸ (φ.range ⊔ H₀))) : Set (H ⧸ (φ.range ⊔ H₀))) =
        {x : H ⧸ (φ.range ⊔ H₀) | ∃ c ∈ φ.range ⊔ H₀, c • q'.out = x.out⁻¹ • g • q'.out} := by
      ext x
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
      rw [← orb_iff φ hφ H₀ h0, Quotient.out_eq]
      show Quotient.mk (orbitRel H' Y) (x.out⁻¹ • q.out) = q' ↔ _
      rw [hg]
    rw [← Set.ncard_coe_finset, hset, fib_card]
  rw [hgq', hgq, finsum_eq_sum_of_support_subset T' hsuppT', finsum_eq_sum_of_support_subset T hsuppT,
    ← Finset.sum_fiberwise_of_maps_to hmaps, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [Finset.sum_congr rfl fun q' hq' => by rw [hT', (Finset.mem_filter.mp hq').2], ← Finset.mul_sum, hfib q hq,
    mul_comm]

end

theorem gqIndex : GqIndex := by
  intro H' H G _ _ _ φ j H₀ U k hN h0 hn hk hS hw
  letI : MulAction H (G ⧸ U) := MulAction.compHom _ j
  letI : MulAction H' (G ⧸ U) := MulAction.compHom _ (j.comp φ)
  exact gq_index φ (fun _ _ => rfl) H₀ h0 k hn hk hS hw

end UpperTheory.V.Z.Sym.Tf
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.TraceFibreCardinality.OrbReps
section
open UpperTheory.V.Z.Sym MulAction in
theorem UpperTheory.V.Z.Sym.Tf.orbReps :
    UpperTheory.V.Z.Sym.Tf.OrbReps := by
  classical
  intro T G _ _ ι C θ U f δ hf hδ J S x hx hs
  letI : MulAction T (G ⧸ U) := MulAction.compHom _ ι
  have sm : ∀ (t : T) (g : G), t • (g : G ⧸ U) = ((ι t * g : G) : G ⧸ U) := fun _ _ => rfl
  have k1 : ∀ (t : T) (g : G), ∀ u ∈ U, f ((ι t * g * u)⁻¹ * δ * θ (ι t * g * u)) = f (g⁻¹ * δ * θ g) := fun t g u hu => by
    rw [← hf u hu (g⁻¹ * δ * θ g)]
    congr 1
    conv_rhs => rw [← hδ t]
    simp [mul_assoc]
  have st : ∀ (t : T) (y : G ⧸ U), stabilizer T (t • y) = stabilizer T y := fun t y => by
    ext a
    simp only [mem_stabilizer_iff]
    rw [smul_smul, mul_comm, mul_smul, smul_left_cancel_iff]
  let q : J → orbitRel.Quotient T (G ⧸ U) := fun i => Quotient.mk'' (x i : G ⧸ U)
  have rel : ∀ (o : orbitRel.Quotient T (G ⧸ U)) (i : J), o = q i ↔ ∃ t, ∃ u ∈ U, o.out.out = ι t * x i * u := fun o i => by
    constructor
    · intro h
      have : orbitRel T _ o.out (x i : G ⧸ U) := Quotient.exact (by rw [Quotient.out_eq]; exact h)
      obtain ⟨t, ht⟩ := this
      obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul U (ι t * x i)
      exact ⟨t, u, u.2, by rw [← hu, ← sm]; exact congrArg _ ht.symm⟩
    · rintro ⟨t, u, hu, h⟩
      rw [← o.out_eq]
      refine Quotient.sound ⟨t, ?_⟩
      show t • _ = _
      rw [sm, ← o.out.out_eq', h]
      exact (QuotientGroup.mk_mul_of_mem _ hu).symm
  unfold orb wcount
  rw [finsum_eq_sum_of_support_subset (s := S.image q) _ fun o ho => ?_, Finset.sum_image fun i hi j hj h => ?_]
  · refine Finset.sum_congr rfl fun i _ => ?_
    obtain ⟨t, u, hu, h⟩ := (rel (q i) i).1 rfl
    have e : (q i).out = t • (x i : G ⧸ U) := by
      rw [sm, ← (q i).out.out_eq', h]; exact QuotientGroup.mk_mul_of_mem _ hu
    beta_reduce
    rw [h, k1 t _ u hu, e, st]
    rfl
  · obtain ⟨t, u, hu, h1⟩ := (rel (q i) i).1 rfl
    obtain ⟨t', u', hu', h2⟩ := (rel (q i) j).1 h
    refine hx i hi j hj (t'⁻¹ * t) (u * u'⁻¹) (mul_mem hu (inv_mem hu')) ?_
    have := h1.symm.trans h2
    rw [map_mul, map_inv, mul_assoc (ι t')⁻¹, mul_assoc (ι t')⁻¹, ← mul_assoc _ u, this]
    simp [mul_assoc]
  · obtain ⟨t, i, hi, u, hu, h⟩ := hs o.out.out (right_ne_zero_of_mul ho)
    exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨i, hi, ((rel o i).2 ⟨t, u, hu, h⟩).symm⟩)
end

