module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.IntegralDeterminants.PlaceConjAlt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0035
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0255
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1081
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0236
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.IntegralDeterminants.AbsBound
section
open NumberField IsDedekindDomain Matrix Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions.N GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.GalOfCusp UpperTheory.V.Af
open scoped Classical

namespace UpperTheory.V.Z.Int

section SlopeTestRemainingChoices

variable {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ)

private lemma nu_mul' (x y : ℂ) : nu ι (x * y) = nu ι x * nu ι y := by
  simp [nu]

private lemma nu_nonneg' (x : ℂ) : 0 ≤ nu ι x := norm_nonneg _

private lemma nu_pos' {x : ℂ} (h : x ≠ 0) : 0 < nu ι x := by
  unfold nu
  exact norm_pos_iff.mpr (by simpa using h)

private lemma nu_sum_le' {α : Type*} (t : Finset α) (f : α → ℂ) (b : ℝ) (hb : 0 ≤ b)
    (h : ∀ x ∈ t, nu ι (f x) ≤ b) : nu ι (∑ x ∈ t, f x) ≤ b := by
  unfold nu
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hb (fun x hx => h x hx)

private lemma nu_mulVec_le {I : Type} [Fintype I] (A : Matrix I I ℂ) (v : I → ℂ) (p q : ℝ)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hA : ∀ i j, nu ι (A i j) ≤ p) (hv : ∀ j, nu ι (v j) ≤ q) (i : I) :
    nu ι ((A *ᵥ v) i) ≤ p * q := by
  simp only [Matrix.mulVec, dotProduct]
  refine nu_sum_le' ι _ _ _ (mul_nonneg hp hq) fun j _ => ?_
  rw [nu_mul']
  exact mul_le_mul (hA i j) (hv j) (nu_nonneg' ι _) hp

end SlopeTestRemainingChoices

theorem absBound :
    UpperTheory.V.Z.Int.AbsBound := by
  intro l _ ι G _ Γ K I _ R F s a c C hc hfin hF hΓ hK heig hRK hRL
  set Nf : G → I → ℂ := fun g => R g⁻¹ *ᵥ F g with hN
  have Rinv : ∀ g, R g⁻¹ * R g = 1 := fun g => by rw [← map_mul, inv_mul_cancel, map_one]
  have Rinv' : ∀ g, R g * R g⁻¹ = 1 := fun g => by rw [← map_mul, mul_inv_cancel, map_one]
  have hNΓ : ∀ γ ∈ Γ, ∀ g, Nf (γ * g) = Nf g := by
    intro γ hγ g
    simp only [hN, hΓ γ hγ g, _root_.mul_inv_rev, map_mul, mulVec_mulVec]
    rw [mul_assoc, Rinv, mul_one]
  have hNK : ∀ k ∈ K, ∀ g, Nf (g * k) = R k⁻¹ *ᵥ Nf g := by
    intro k hk g
    simp only [hN, hK k hk g, _root_.mul_inv_rev, map_mul, mulVec_mulVec]
  have hNeig : ∀ h, a • Nf h = ∑ x ∈ s, R x *ᵥ Nf (h * x) := by
    intro h
    have h1 : ∀ x, R x *ᵥ Nf (h * x) = R h⁻¹ *ᵥ F (h * x) := by
      intro x
      simp only [hN, _root_.mul_inv_rev, map_mul, mulVec_mulVec]
      rw [← mul_assoc, Rinv', one_mul]
    simp only [h1]
    simp only [hN]
    rw [← Matrix.mulVec_smul, ← heig h, Matrix.mulVec_sum]

  obtain ⟨g0, i0, h0⟩ : ∃ g i, Nf g i ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    apply hF
    funext g
    have : F g = R g *ᵥ Nf g := by
      simp only [hN, mulVec_mulVec, Rinv', one_mulVec]
    rw [this, show Nf g = 0 from funext (hcon g)]
    simp
  have hC : 0 ≤ C := (nu_nonneg' ι _).trans (hRK 1 K.one_mem i0 i0)

  obtain ⟨B, hB0, hB⟩ : ∃ B : ℝ, 0 ≤ B ∧ ∀ g i, nu ι (Nf g i) ≤ B := by
    haveI := hfin
    letI := Fintype.ofFinite (DoubleCoset.Quotient (Γ : Set G) (K : Set G))
    set B0 : ℝ := ∑ q : DoubleCoset.Quotient (Γ : Set G) (K : Set G), ∑ i, nu ι (Nf q.out i) with hB0
    have hB0n : 0 ≤ B0 := Finset.sum_nonneg fun q _ => Finset.sum_nonneg fun i _ => nu_nonneg' ι _
    have hle : ∀ (q : DoubleCoset.Quotient (Γ : Set G) (K : Set G)) j, nu ι (Nf q.out j) ≤ B0 := by
      intro q j
      calc nu ι (Nf q.out j) ≤ ∑ i, nu ι (Nf q.out i) :=
            Finset.single_le_sum (f := fun i => nu ι (Nf q.out i)) (fun i _ => nu_nonneg' ι _) (Finset.mem_univ j)
        _ ≤ B0 := Finset.single_le_sum (f := fun q : DoubleCoset.Quotient (Γ : Set G) (K : Set G) => ∑ i, nu ι (Nf q.out i))
            (fun q _ => Finset.sum_nonneg fun i _ => nu_nonneg' ι _) (Finset.mem_univ q)
    refine ⟨C * B0, mul_nonneg hC hB0n, fun g i => ?_⟩
    obtain ⟨h, hh, k, hk, e⟩ := DoubleCoset.mk_out_eq_mul Γ K g
    have hg : g = h⁻¹ * ((DoubleCoset.mk Γ K g).out * k⁻¹) := by
      rw [e]; group
    have hNg : Nf g = R (k⁻¹)⁻¹ *ᵥ Nf (DoubleCoset.mk Γ K g).out := by
      conv_lhs => rw [hg]
      rw [hNΓ _ (Γ.inv_mem hh), hNK _ (K.inv_mem hk)]
    rw [hNg]
    exact nu_mulVec_le ι _ _ C B0 hC hB0n (hRK _ (K.inv_mem (K.inv_mem hk))) (hle _) i

  have hstep : ∀ (L : List G), a • (R L.prod *ᵥ Nf (g0 * L.prod)) =
      ∑ x ∈ s, R (L ++ [x]).prod *ᵥ Nf (g0 * (L ++ [x]).prod) := by
    intro L
    rw [← Matrix.mulVec_smul, hNeig, Matrix.mulVec_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [List.prod_append, List.prod_singleton, map_mul, mulVec_mulVec, mul_assoc]
  have hit : ∀ (n : ℕ) (L : List G), (∀ x ∈ L, x ∈ s) → ∀ i,
      nu ι a ^ n * nu ι ((R L.prod *ᵥ Nf (g0 * L.prod)) i) ≤ C * B * c ^ (L.length + n) := by
    intro n
    induction n with
    | zero =>
      intro L hL i
      have := nu_mulVec_le ι (R L.prod) (Nf (g0 * L.prod)) (C * c ^ L.length) B
        (mul_nonneg hC (pow_nonneg hc _)) hB0 (hRL L hL) (hB _) i
      simp only [pow_zero, one_mul, add_zero]
      calc _ ≤ _ := this
        _ = _ := by ring
    | succ n ih =>
      intro L hL i
      have e : a * (R L.prod *ᵥ Nf (g0 * L.prod)) i =
          ∑ x ∈ s, (R (L ++ [x]).prod *ᵥ Nf (g0 * (L ++ [x]).prod)) i := by
        have := congrFun (hstep L) i
        simpa [Finset.sum_apply] using this
      have hD : 0 ≤ C * B * c ^ (L.length + (n + 1)) :=
        mul_nonneg (mul_nonneg hC hB0) (pow_nonneg hc _)
      calc nu ι a ^ (n + 1) * nu ι ((R L.prod *ᵥ Nf (g0 * L.prod)) i)
          = nu ι a ^ n * nu ι (a * (R L.prod *ᵥ Nf (g0 * L.prod)) i) := by
            rw [nu_mul']; ring
        _ = nu ι a ^ n * nu ι (∑ x ∈ s, (R (L ++ [x]).prod *ᵥ Nf (g0 * (L ++ [x]).prod)) i) := by rw [e]
        _ ≤ C * B * c ^ (L.length + (n + 1)) := by
            by_cases hz : nu ι a ^ n = 0
            · rw [hz, zero_mul]; exact hD
            have hp : 0 < nu ι a ^ n := lt_of_le_of_ne (pow_nonneg (nu_nonneg' ι _) _) (Ne.symm hz)
            rw [← le_div_iff₀' hp]
            refine nu_sum_le' ι _ _ _ (div_nonneg hD hp.le) fun x hx => ?_
            rw [le_div_iff₀' hp]
            have := ih (L ++ [x]) (fun y hy => by
              rcases List.mem_append.mp hy with h | h
              · exact hL y h
              · simp at h; exact h ▸ hx) i
            simpa [List.length_append, add_assoc, add_comm 1 n] using this
  have hfinal : ∀ n : ℕ, nu ι a ^ n * nu ι (Nf g0 i0) ≤ C * B * c ^ n := by
    intro n
    have := hit n [] (by simp) i0
    simpa [hN] using this
  have hd : 0 < nu ι (Nf g0 i0) := nu_pos' ι h0
  by_contra hlt
  push_neg at hlt
  rcases hc.eq_or_lt with h0c | hcpos
  · have := hfinal 1
    rw [← h0c] at this hlt
    simp only [pow_one, mul_zero] at this
    have : 0 < nu ι a * nu ι (Nf g0 i0) := mul_pos hlt hd
    linarith
  · have hr : 1 < nu ι a / c := (one_lt_div hcpos).mpr hlt
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (C * B / nu ι (Nf g0 i0)) hr
    rw [div_lt_iff₀ hd, div_pow, div_mul_eq_mul_div, lt_div_iff₀ (pow_pos hcpos n)] at hn
    linarith [hfinal n]

end UpperTheory.V.Z.Int
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.IntegralDeterminants.PlaceHom
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual

namespace UpperTheory.V.Z.Int

private theorem val_le_one_iff {l : ℕ} [Fact l.Prime] {E : Type} [Field E] [NumberField E]
    (c : E →+* Qbar l) (u : HeightOneSpectrum (𝓞 E))
    (hu : ∀ x : E, u.valuation E x < 1 ↔ ‖c x‖ < 1) (x : E) :
    u.valuation E x ≤ 1 ↔ ‖c x‖ ≤ 1 := by
  by_cases hx : x = 0
  · simp [hx]
  have h0 : 0 < u.valuation E x := zero_lt_iff.2 ((map_ne_zero _).2 hx)
  have h1 : 0 < ‖c x‖ := norm_pos_iff.2 ((map_ne_zero c).2 hx)
  have h := hu x⁻¹
  rw [map_inv₀, map_inv₀, norm_inv, inv_lt_one₀ h0, inv_lt_one₀ h1] at h
  rw [← not_lt, ← not_lt, h]

theorem placeHom : PlaceHom := by
  intro l _ ι E _ _ τ
  let c : E →+* Qbar l := ι.symm.toRingHom.comp τ
  have hc : ∀ x, c x = ι.symm (τ x) := fun _ => rfl
  obtain ⟨u, hu⟩ := GlobalTheory.LadicPlace.exists_place_of_embedding E l c
  obtain ⟨j, hj, hjE⟩ := GlobalTheory.exists_continuous_extension_adicCompletion E l c u hu
  have hjx : ∀ x : E, j (algebraMap E (u.adicCompletion E) x) = c x :=
    fun x => DFunLike.congr_fun hjE x
  refine ⟨u, ι.toRingHom.comp j, fun x => ?_, fun x => ?_, fun w => ?_⟩
  · change ι (j (algebraMap E (u.adicCompletion E) x)) = τ x
    rw [hjx, hc, RingEquiv.apply_symm_apply]
  · have hnu : ∀ y, nu ι ((ι.toRingHom.comp j) y) = ‖j y‖ := fun y => by
      change ‖ι.symm (ι (j y))‖ = _
      rw [RingEquiv.symm_apply_apply]
    rw [hnu]
    have hB : IsClopen {y : u.adicCompletion E | ‖j y‖ ≤ 1} := by
      have := (IsUltrametricDist.isClopen_closedBall (0 : Qbar l) one_ne_zero).preimage hj
      simpa [Set.preimage, Metric.closedBall] using this
    have hC : IsClopen {y : u.adicCompletion E | Valued.v y ≤ 1} :=
      Valued.isClopen_integer (u.adicCompletion E)
    have hT : IsClosed {y : u.adicCompletion E | ‖j y‖ ≤ 1 ↔ Valued.v y ≤ 1} := by
      have : {y : u.adicCompletion E | ‖j y‖ ≤ 1 ↔ Valued.v y ≤ 1} =
          ({y | ‖j y‖ ≤ 1} ∩ {y | Valued.v y ≤ 1}) ∪
            ({y | ‖j y‖ ≤ 1}ᶜ ∩ {y | Valued.v y ≤ 1}ᶜ) := by
        ext y
        simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_inter_iff, Set.mem_compl_iff]
        tauto
      rw [this]
      exact (hB.isClosed.inter hC.isClosed).union (hB.compl.isClosed.inter hC.compl.isClosed)
    refine (HeightOneSpectrum.denseRange_algebraMap (R := 𝓞 E) (K := E) u).induction_on
      (p := fun y => ‖j y‖ ≤ 1 ↔ Valued.v y ≤ 1) x hT fun a => ?_
    have hv : Valued.v (algebraMap E (u.adicCompletion E) a) = u.valuation E a :=
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' u a
    rw [hjx, hv, val_le_one_iff c u hu a]
  · have hw : ∀ a : 𝓞 E, nu ι (τ a) = ‖c a‖ := fun _ => rfl
    have hmem : ∀ a : 𝓞 E, a ∈ u.asIdeal ↔ ‖c a‖ < 1 := fun a => by
      rw [← hu, HeightOneSpectrum.valuation_lt_one_iff_mem]
    simp only [Ov, Finset.mem_filter, Finset.mem_univ, true_and, hw]
    constructor
    · intro h
      exact HeightOneSpectrum.ext (Ideal.ext fun a => (h a).trans (hmem a).symm)
    · rintro rfl
      exact hmem

end UpperTheory.V.Z.Int
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.IntegralDeterminants.RootBound
section
open NumberField IsDedekindDomain Matrix Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions.N GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.GalOfCusp UpperTheory.V.Af
open scoped Classical

theorem UpperTheory.V.Z.Int.rootBound :
    UpperTheory.V.Z.Int.RootBound := by
  intro l _ ι S c hc h b hb
  by_contra hlt
  have hlt' : c < ‖ι.symm b‖ := not_le.mp hlt
  have hroot : Polynomial.eval b (S.map fun t => Polynomial.X - Polynomial.C t).prod = 0 := by
    rw [Polynomial.eval_multiset_prod]
    apply Multiset.prod_eq_zero
    rw [Multiset.mem_map]
    refine ⟨Polynomial.X - Polynomial.C b, Multiset.mem_map.mpr ⟨b, hb, rfl⟩, by simp⟩
  rw [Multiset.prod_X_sub_X_eq_sum_esymm, Polynomial.eval_finsetSum, Finset.sum_range_succ'] at hroot
  have hn : 0 < S.card := Multiset.card_pos_iff_exists_mem.mpr ⟨b, hb⟩
  have h0 : S.esymm 0 = 1 := by simp [Multiset.esymm]
  simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_neg, Polynomial.eval_one,
    Polynomial.eval_C, Polynomial.eval_X, pow_zero, one_mul, Nat.sub_zero, h0] at hroot
  have hK := congrArg ι.symm hroot
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_add (f := _), map_sum, map_mul, map_pow, map_neg, map_one, map_zero] at hK
  have heq : ‖ι.symm b‖ ^ S.card = ‖∑ j ∈ Finset.range S.card, (-1 : PadicAlgCl l) ^ (j + 1) * (ι.symm (S.esymm (j + 1)) * ι.symm b ^ (S.card - (j + 1)))‖ := by
    rw [eq_neg_of_add_eq_zero_left hK, norm_neg, norm_pow]
  obtain ⟨i, hi, hle⟩ := IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty
    (Finset.nonempty_range_iff.mpr hn.ne')
    (fun j => (-1 : PadicAlgCl l) ^ (j + 1) * (ι.symm (S.esymm (j + 1)) * ι.symm b ^ (S.card - (j + 1))))
  have hi' : i + 1 ≤ S.card := Finset.mem_range.mp hi
  have hj := h (i + 1) (by omega) hi'
  have hj' : ‖ι.symm (S.esymm (i + 1))‖ ≤ c ^ (i + 1) := hj
  have hpos : 0 < ‖ι.symm b‖ := lt_of_le_of_lt hc hlt'
  have hcp : c ^ (i + 1) < ‖ι.symm b‖ ^ (i + 1) := pow_lt_pow_left₀ hlt' hc (by omega)
  have hterm : ‖(-1 : PadicAlgCl l) ^ (i + 1) * (ι.symm (S.esymm (i + 1)) * ι.symm b ^ (S.card - (i + 1)))‖
      < ‖ι.symm b‖ ^ S.card := by
    rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_mul, norm_pow]
    calc ‖ι.symm (S.esymm (i + 1))‖ * ‖ι.symm b‖ ^ (S.card - (i + 1))
        < ‖ι.symm b‖ ^ (i + 1) * ‖ι.symm b‖ ^ (S.card - (i + 1)) :=
          mul_lt_mul_of_pos_right (lt_of_le_of_lt hj' hcp) (pow_pos hpos _)
      _ = ‖ι.symm b‖ ^ S.card := by rw [← pow_add]; congr 1; omega
  exact absurd (heq.le.trans hle) (not_le.mpr hterm)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.IntegralDeterminants.VecForm
section
open NumberField IsDedekindDomain Matrix Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions.N GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.GalOfCusp UpperTheory.V.Af
open scoped Classical

private noncomputable def fixW {E : Type} [Field E] [NumberField E] [IsCMField E] (n : ℕ)
    (w : HeightOneSpectrum (𝓞 E)) : Submodule ℂ (UA E n → ℂ) where
  carrier := {ψ | ∀ y ∈ locU n w, cLoc w y ∈ GlobalTheory.LFun.KGL w (n := n) → RU E n y ψ = ψ}
  add_mem' ha hb y hy hk := by rw [map_add (f := _), ha y hy hk, hb y hy hk]
  zero_mem' _ _ _ := map_zero _
  smul_mem' c _ ha y hy hk := by rw [map_smul, ha y hy hk]

private theorem span_sub {H S Y V : Type} [Group H] [AddCommGroup S] [Module ℂ S] [AddCommGroup Y] [Module ℂ Y]
    [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ H S) (π : Representation ℂ H Y)
    (ρ : Representation ℂ H V) (hσ : σ.IsIrreducible) (j : Y →ₗ[ℂ] V) (hj : Function.Injective j)
    (he : ∀ g y, j (π g y) = ρ g (j y))
    (h : (⨆ f : σ.IntertwiningMap ρ, LinearMap.range f.toLinearMap) = ⊤) :
    (⨆ f : σ.IntertwiningMap π, LinearMap.range f.toLinearMap) = ⊤ := by
  have h1 : ∀ y, j y ∈ ⨆ f : {f : S →ₗ[ℂ] V // ∀ g v, f (σ g v) = ρ g (f v)}, LinearMap.range f.1 := by
    intro y
    have hle : (⨆ f : σ.IntertwiningMap ρ, LinearMap.range f.toLinearMap) ≤
        ⨆ f : {f : S →ₗ[ℂ] V // ∀ g v, f (σ g v) = ρ g (f v)}, LinearMap.range f.1 :=
      iSup_le fun f => le_iSup_of_le ⟨f.toLinearMap, fun g v => Representation.IntertwiningMap.isIntertwining σ ρ f g v⟩ le_rfl
    exact hle (h ▸ Submodule.mem_top)
  rw [eq_top_iff]
  intro y _
  have h2 := UpperTheory.V.PiLin.iso_sub σ π ρ hσ j hj he h1 y
  have hle : (⨆ f : {f : S →ₗ[ℂ] Y // ∀ g v, f (σ g v) = π g (f v)}, LinearMap.range f.1) ≤
      ⨆ f : σ.IntertwiningMap π, LinearMap.range f.toLinearMap :=
    iSup_le fun f => le_iSup_of_le ⟨f.1, fun g => LinearMap.ext fun v => f.2 g v⟩ le_rfl
  exact hle h2

theorem UpperTheory.V.Z.Int.vecForm :
    UpperTheory.V.Z.Int.VecForm := by
  intro E _ _ _ n hn V hV φ hφ lam hW w hw
  obtain ⟨φ₀, hφ₀, hne, hfix⟩ := hw
  let π : GlobalTheory.DefU.AutSub E n := ⟨V, hV⟩
  let N : Submodule ℂ (UA E n → ℂ) := V ⊓ fixW n w
  have hNV : N ≤ V := inf_le_left
  have hmemN : ∀ ψ, ψ ∈ N ↔ ψ ∈ V ∧ ∀ y ∈ locU n w, cLoc w y ∈ GlobalTheory.LFun.KGL w (n := n) → RU E n y ψ = ψ :=
    fun _ => Iff.rfl
  have hst : ∀ (x : infU E n), ∀ ψ ∈ N, ((RU E n).comp (infU E n).subtype) x ψ ∈ N := by
    intro x ψ hψ
    obtain ⟨h1, h2⟩ := (hmemN ψ).1 hψ
    refine (hmemN _).2 ⟨hV.stable _ _ h1, fun y hy hk => ?_⟩
    change RU E n y (RU E n x.1 ψ) = RU E n x.1 ψ
    rw [GlobalTheory.DefU.RU_RU, GlobalTheory.DefU.fin_mul_inf hy.1 x.2, ← GlobalTheory.DefU.RU_RU, h2 y hy hk]
  let ρ : Representation ℂ (infU E n) N := GlobalTheory.PRep.sub ((RU E n).comp (infU E n).subtype) N hst
  let s : ∀ v : InfinitePlace E, embU n (φ v) →* infU E n := fun v => Subgroup.inclusion inf_le_left
  let σ : ∀ v, Representation ℂ (embU n (φ v)) (nablaSq ℂ n (lam v)) := fun v =>
    (GlobalTheory.Branching.sqRep ℂ n (lam v)).comp ((cEmb (φ v)).comp (embU n (φ v)).subtype)
  have hirr : ∀ v, (σ v).IsIrreducible := fun v => by
    obtain ⟨e, he⟩ := _root_.GlobalTheory.EmbUnitary.exists_equiv_unitaryGroup E n (φ v)
    obtain ⟨h1, h2⟩ := (GlobalTheory.CuspRep.isIrreducible_iff _).1
      (GlobalTheory.Branching.isIrreducible_smallRep_unitary n (lam v))
    refine (GlobalTheory.CuspRep.isIrreducible_iff _).2 ⟨h1, fun S hS => h2 S fun g u hu => ?_⟩
    obtain ⟨x, rfl⟩ := e.surjective g
    have h3 := hS x u hu
    change GlobalTheory.Branching.sqRep ℂ n (lam v) (cEmb (φ v) (x : UA E n)) u ∈ S at h3
    change GlobalTheory.Branching.sqRep ℂ n (lam v) (GlobalTheory.Branching.unitaryIncl n (e x)) u ∈ S
    rwa [he]
  have hcomm : ∀ u v, u ≠ v → ∀ a b, Commute (s u a) (s v b) := fun u v huv a b =>
    Subtype.ext (GlobalTheory.T.commute_unitaryArchimedeanPoints_distinct_places E n (φ u) (φ v) (by rwa [hφ, hφ]) _ a.2 _ b.2)
  have hspan : ∀ v, (⨆ f : (σ v).IntertwiningMap (ρ.comp (s v)), LinearMap.range f.toLinearMap) = ⊤ :=
    fun v => span_sub (σ v) (ρ.comp (s v)) (π.rep.comp (embU n (φ v)).subtype) (hirr v)
      (Submodule.inclusion hNV) (Submodule.inclusion_injective hNV) (fun g y => Subtype.ext rfl)
      (_root_.GlobalTheory.DefU.iSup_range_weight_eq_top E n π (φ v) (lam v) (hW v))
  haveI : Nontrivial N := ⟨⟨⟨φ₀, (hmemN _).2 ⟨hφ₀, hfix⟩⟩, 0, fun h => hne (congrArg Subtype.val h)⟩⟩
  obtain ⟨F, hF0, hF⟩ := GlobalTheory.T.exists_multilinearMap_of_isotypic_commuting_subgroups (InfinitePlace E) (infU E n) N (fun v => embU n (φ v))
    (fun v => nablaSq ℂ n (lam v)) ρ s σ inferInstance hirr hcomm hspan
  let f : MultilinearMap (RingHom.id ℂ) (fun v => nablaSq ℂ n (lam v)) (UA E n → ℂ) := N.subtype.compMultilinearMap F
  have hfN : ∀ x, f x ∈ N := fun x => (F x).2
  have hfne : f ≠ 0 := fun h => hF0 (MultilinearMap.ext fun x => Subtype.ext (congrArg (fun m => m x) h))
  have hfF : ∀ v (h : embU n (φ v)) (x : ∀ u, nablaSq ℂ n (lam u)),
      RU E n h.1 (f x) = f (Function.update x v (σ v h (x v))) := fun v h x =>
    congrArg Subtype.val (hF v h x)
  have hE : ∀ v, embU n (φ v) = embU n v.embedding := fun v => by
    unfold embU
    rw [hφ v, InfinitePlace.mk_embedding]
  have hact : ∀ g ∈ infU E n, ∀ x : (∀ v, nablaSq ℂ n (lam v)),
      f (fun v => GlobalTheory.Branching.sqRep ℂ n (lam v) (cEmb (φ v) g) (x v)) = RU E n g (f x) := by
    intro g hg x
    obtain ⟨y, hy, -, hprod⟩ := _root_.GlobalTheory.DefU.infU_eq_list_prod_embU E n g hg
    have hy' : ∀ v, y v ∈ embU n (φ v) := fun v => (hE v).symm ▸ hy v
    have hone : ∀ u v, u ≠ v → cEmb (φ v) (y u) = 1 := by
      intro u v huv
      have h2 : y u ∈ ⨅ (τ' : E →+* ℂ) (_ : InfinitePlace.mk τ' ≠ InfinitePlace.mk (φ u)),
          (cEmb (E := E) (n := n) τ').ker := (hy' u).2
      rw [Subgroup.mem_iInf] at h2
      have h3 := h2 (φ v)
      rw [Subgroup.mem_iInf] at h3
      exact h3 (by rw [hφ, hφ]; exact huv.symm)
    have hlist : ∀ v, ∀ L : List (InfinitePlace E), L.Nodup →
        cEmb (φ v) (L.map y).prod = if v ∈ L then cEmb (φ v) (y v) else 1 := by
      intro v L
      induction L with
      | nil => intro _; simp
      | cons a L ih =>
        intro hL
        rw [List.nodup_cons] at hL
        rw [List.map_cons, List.prod_cons, map_mul, ih hL.2]
        by_cases ha : a = v
        · subst ha
          simp [hL.1]
        · rw [hone a v ha, one_mul]
          simp [List.mem_cons, Ne.symm ha]
    have hcg : ∀ v, cEmb (φ v) g = cEmb (φ v) (y v) := by
      intro v
      rw [← hprod, hlist v _ (Finset.nodup_toList _)]
      simp
    have h1 := GlobalTheory.DefU.prod_list_apply_multilinear (H := fun v => embU n (φ v))
      (Wv := fun v => nablaSq ℂ n (lam v)) (RU E n) (fun v => (embU n (φ v)).subtype) σ f hfF
      (fun v => (⟨y v, hy' v⟩ : embU n (φ v))) x Finset.univ.toList (Finset.nodup_toList _)
    have h2 : (Finset.univ.toList.map fun v => (embU n (φ v)).subtype ⟨y v, hy' v⟩).prod = g := hprod
    rw [h2] at h1
    rw [h1]
    congr 1
    funext v
    rw [hcg v]
    simp [σ]
  let Kint : Subgroup (finU (E := E) (n := n)) :=
    (GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E n).comap (GlobalTheory.BCT.GlobLev.finPart E n)
  let Kst : Subgroup (finU (E := E) (n := n)) :=
    { carrier := {k | ∀ x, RU E n k.1 (f x) = f x}
      one_mem' := fun x => by simp
      mul_mem' := fun {a b} ha hb x => by
        rw [Subgroup.coe_mul, map_mul, Module.End.mul_apply, hb x, ha x]
      inv_mem' := fun {a} ha x => by
        calc RU E n (a⁻¹).1 (f x) = RU E n (a⁻¹).1 (RU E n a.1 (f x)) := by rw [ha x]
          _ = RU E n ((a⁻¹).1 * a.1) (f x) := by rw [GlobalTheory.DefU.RU_RU]
          _ = f x := by simp }
  have hO1 : IsOpen (Kint : Set (finU (E := E) (n := n))) :=
    (GroundTheory.Automorphic.AdelicGLn.isOpen_integralFiniteGL E n).preimage GlobalTheory.BCT.GlobLev.continuous_finPart
  have hO2 : IsOpen (Kst : Set (finU (E := E) (n := n))) := by
    let B := fun v => Module.finBasis ℂ (nablaSq ℂ n (lam v))
    have e : (Kst : Set (finU (E := E) (n := n))) = ⋂ t : (∀ v, Fin (Module.finrank ℂ (nablaSq ℂ n (lam v)))),
        {k : finU (E := E) (n := n) | RU E n k.1 (f fun v => B v (t v)) = f fun v => B v (t v)} := by
      ext k
      simp only [Set.mem_iInter]
      refine ⟨fun h t => h _, fun h x => ?_⟩
      have h4 : (RU E n k.1).compMultilinearMap f = f := Module.Basis.ext_multilinear B fun t => h t
      exact congrArg (fun m => m x) h4
    rw [e]
    exact isOpen_iInter_of_finite fun t => (hV.aut _ ((hmemN _).1 (hfN _)).1).level
  refine ⟨f, Kint ⊓ Kst, hfne, fun x => ((hmemN _).1 (hfN x)).1, hact, ?_,
    fun k hk => (GlobalTheory.Cong.AdaptLev.finPart_mem_integral_iff k).1 hk.1, fun k hk => hk.2,
    fun y hy hk x => ((hmemN _).1 (hfN x)).2 y hy hk⟩
  rw [Subgroup.coe_inf]
  exact hO1.inter hO2
end

