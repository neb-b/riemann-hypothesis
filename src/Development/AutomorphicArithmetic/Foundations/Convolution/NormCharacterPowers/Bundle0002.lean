module

public import Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.SumSatUnit
public import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.JacquetShalikaRigidity
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0302
public import Development.AbelianVarietyTheory.BlockTheory.AdelicCMFields.UnitaryHeckeCharacterIdele
public import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.AbsoluteRigidity.AbsRigClosed
public import Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.BcSumD
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.GaloisGenerators.LocRoots

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.CoverEx
section
open UpperTheory.ConvolutionTheory.R
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V.Published PositivityTheory.RgJS

private theorem normV_eq {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    normV v = Ideal.absNorm v.asIdeal := by
  rw [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]

private theorem one_lt_normV {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) : 1 < normV v := by
  rw [normV_eq]
  exact NumberField.HeightOneSpectrum.one_lt_absNorm v

theorem UpperTheory.ConvolutionTheory.R.coverEx :
    Decomp → CoverEx := by
  classical
  intro hD K M _ _ _ _ _ _ _ _ hl η hη S₀ T₀
  have hD' := hD K M hl
  obtain ⟨⟨-, -, hN⟩, hG⟩ := hη
  have hNG := hN.and hG
  beta_reduce at hD'
  rw [Filter.eventually_cofinite] at hD' hNG
  have hten : Filter.Tendsto (fun w : HeightOneSpectrum (𝓞 M) => w.under (𝓞 K)) Filter.cofinite Filter.cofinite :=
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.tendsto_under K M
  set S : Finset (HeightOneSpectrum (𝓞 K)) :=
    S₀ ∪ hD'.toFinset ∪ (T₀ ∪ hNG.toFinset).image (fun w => w.under (𝓞 K)) with hS
  have hTfin : {w : HeightOneSpectrum (𝓞 M) | w.under (𝓞 K) ∈ S}.Finite := by
    have := hten.eventually S.eventually_cofinite_notMem
    rw [Filter.eventually_cofinite] at this
    simpa using this
  set T := hTfin.toFinset with hT
  have hmemT : ∀ w, w ∈ T ↔ w.under (𝓞 K) ∈ S := fun w => by simp [hT]
  have hgood : ∀ w : HeightOneSpectrum (𝓞 M), w.under (𝓞 K) ∉ S →
      (∀ f : ℕ, normV w = normV (w.under (𝓞 K)) ^ f → η.val (w.under (𝓞 K)) ^ f = 1) ∧ η.UnrAt (w.under (𝓞 K)) ∧
      (normV w = normV (w.under (𝓞 K)) ∨ IsPrimitiveRoot (η.val (w.under (𝓞 K))) (Module.finrank K M)) := by
    intro w hw
    by_contra h
    exact hw (Finset.mem_union_right _ (Finset.mem_image_of_mem _
      (Finset.mem_union_right _ (hNG.mem_toFinset.2 h))))
  have hdec : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
      (Nat.card {w : HeightOneSpectrum (𝓞 M) // w.under (𝓞 K) = v} = Module.finrank K M ∧
        ∀ w : HeightOneSpectrum (𝓞 M), w.under (𝓞 K) = v → normV w = normV v) ∨
      (Nat.card {w : HeightOneSpectrum (𝓞 M) // w.under (𝓞 K) = v} = 1 ∧
        ∀ w : HeightOneSpectrum (𝓞 M), w.under (𝓞 K) = v → normV w = normV v ^ Module.finrank K M) := by
    intro v hv
    by_contra h
    exact hv (Finset.mem_union_left _ (Finset.mem_union_right _ (hD'.mem_toFinset.2 h)))
  have hex : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ∃ w : HeightOneSpectrum (𝓞 M), w.under (𝓞 K) = v := by
    intro v hv
    have : Nat.card {w : HeightOneSpectrum (𝓞 M) // w.under (𝓞 K) = v} ≠ 0 := by
      rcases hdec v hv with h | h
      · rw [h.1]; exact hl.ne_zero
      · rw [h.1]; exact one_ne_zero
    obtain ⟨⟨w, hw⟩⟩ := (Nat.card_ne_zero.1 this).1
    exact ⟨w, hw⟩
  have hne : ∀ v : HeightOneSpectrum (𝓞 K), normV v ^ Module.finrank K M ≠ normV v := by
    intro v
    have := Nat.pow_lt_pow_right (one_lt_normV v) hl.one_lt
    rw [pow_one] at this
    exact this.ne'
  let u : Off M T → Off K S := fun w => ⟨w.1.under (𝓞 K), fun h => w.2 ((hmemT _).2 h)⟩
  let f : Off M T → ℕ := fun w => if normV w.1 = normV (w.1.under (𝓞 K)) then 1 else Module.finrank K M
  have hnorm : ∀ w, normV w.1 = normV (u w).1 ^ f w := by
    intro w
    by_cases h : normV w.1 = normV (w.1.under (𝓞 K))
    · simp only [f, if_pos h, pow_one]; exact h
    · simp only [f, if_neg h]
      rcases hdec _ (u w).2 with h' | h'
      · exact absurd (h'.2 _ rfl) h
      · exact h'.2 _ rfl
  have hcard : ∀ v : Off K S, Nat.card {w // u w = v} =
      Nat.card {w : HeightOneSpectrum (𝓞 M) // w.under (𝓞 K) = v.1} := by
    intro v
    exact Nat.card_congr
      { toFun := fun w => ⟨w.1.1, congrArg Subtype.val w.2⟩
        invFun := fun w => ⟨⟨w.1, fun h => v.2 (w.2 ▸ (hmemT _).1 h)⟩, Subtype.ext w.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  refine ⟨S, T, u, f, fun v hv => Finset.mem_union_left _ (Finset.mem_union_left _ hv), fun w hw => (hmemT w).2
    (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_union_left _ hw))), fun _ => rfl, ?_, hnorm, ?_, ?_⟩
  · intro v
    obtain ⟨w, hw⟩ := hex v.1 v.2
    exact hw ▸ (hgood w (hw ▸ v.2)).2.1
  · intro w
    simpa only [nq, normV_eq] using hnorm w
  · intro v
    obtain ⟨w₀, hw₀⟩ := hex v.1 v.2
    have hg := hgood w₀ (hw₀ ▸ v.2)
    rw [hw₀] at hg
    rcases hdec v.1 v.2 with h | h
    · refine Or.inl ⟨(hcard v).trans h.1, fun w hw => ?_, ?_⟩
      · have hw' : w.1.under (𝓞 K) = v.1 := congrArg Subtype.val hw
        exact if_pos (hw' ▸ h.2 _ hw')
      · have := hg.1 1 (by rw [pow_one]; exact h.2 _ hw₀)
        rw [pow_one] at this
        simp [this]
    · refine Or.inr ⟨(hcard v).trans h.1, fun w hw => ?_, ?_⟩
      · have hw' : w.1.under (𝓞 K) = v.1 := congrArg Subtype.val hw
        refine if_neg ?_
        rw [h.2 _ hw', hw']
        exact hne _
      · rcases hg.2.2 with h' | h'
        · exact absurd ((h.2 _ hw₀).symm.trans h') (hne _)
        · exact IsPrimitiveRoot.coe_units_iff.2 h'
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.Decomp
section
open UpperTheory.ConvolutionTheory.R
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual

section

variable (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]

private theorem normV_inertia (w : HeightOneSpectrum (𝓞 M)) :
    normV w = normV (w.under (𝓞 K)) ^ w.asIdeal.inertiaDeg (𝓞 K) := by
  have : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩
  have := w.isMaximal
  have := (w.under (𝓞 K)).isMaximal
  have norm_eq {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
      normV v = Ideal.absNorm v.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    rfl
  rw [norm_eq, norm_eq]
  rw [← Ideal.absNorm_relNorm (𝓞 K) (𝓞 M) w.asIdeal,
    Ideal.relNorm_eq_pow_of_isMaximal w.asIdeal (w.under (𝓞 K)).asIdeal, map_pow]

private theorem unram_ae : ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
    ∀ w : HeightOneSpectrum (𝓞 M), w.under (𝓞 K) = v → w.asIdeal.ramificationIdx (𝓞 K) = 1 := by
  have hfin : {w : HeightOneSpectrum (𝓞 M) | w.asIdeal ∣ differentIdeal (𝓞 K) (𝓞 M)}.Finite :=
    Ideal.finite_factors differentIdeal_ne_bot
  refine Filter.eventually_cofinite.2 ((hfin.image fun w => w.under (𝓞 K)).subset ?_)
  intro v hv
  by_contra hn
  refine hv fun w hw => ?_
  have := w.isPrime
  have hnd : ¬ w.asIdeal ∣ differentIdeal (𝓞 K) (𝓞 M) := fun h => hn ⟨w, h, hw⟩
  exact Ideal.ramificationIdx_eq_one_iff.2 (not_dvd_differentIdeal_iff.1 hnd)

private theorem card_fibre (v : HeightOneSpectrum (𝓞 K)) :
    Nat.card {w : HeightOneSpectrum (𝓞 M) // w.under (𝓞 K) = v} = (v.asIdeal.primesOver (𝓞 M)).ncard := by
  rw [← Nat.card_coe_set_eq]
  refine Nat.card_congr (Equiv.ofBijective
    (fun w => ⟨w.1.asIdeal, w.1.isPrime, ⟨(congrArg HeightOneSpectrum.asIdeal w.2).symm⟩⟩) ⟨fun a b h => ?_, fun P => ?_⟩)
  · exact Subtype.ext (HeightOneSpectrum.ext (congrArg Subtype.val h))
  · obtain ⟨P, hP, hPv⟩ := P
    exact ⟨⟨⟨P, hP, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P⟩,
      HeightOneSpectrum.ext hPv.over.symm⟩, rfl⟩

end

theorem UpperTheory.ConvolutionTheory.R.decomp :
    Decomp := by
  intro K M _ _ _ _ _ _ _ _ hl
  filter_upwards [unram_ae K M] with v hv
  have := v.isPrime
  have hfund := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn v.asIdeal (𝓞 M) Gal(M/K)
  obtain ⟨⟨P, hP, hPv⟩⟩ := (inferInstance : Nonempty (v.asIdeal.primesOver (𝓞 M)))
  have he : v.asIdeal.ramificationIdxIn (𝓞 M) = 1 := by
    rw [Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal P Gal(M/K)]
    exact hv ⟨P, hP, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P⟩ (HeightOneSpectrum.ext hPv.over.symm)
  have hn : ∀ w : HeightOneSpectrum (𝓞 M), w.under (𝓞 K) = v →
      normV w = normV v ^ v.asIdeal.inertiaDegIn (𝓞 M) := by
    rintro w rfl
    have := w.isPrime
    have : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩
    rw [Ideal.inertiaDegIn_eq_inertiaDeg _ w.asIdeal Gal(M/K)]
    exact normV_inertia K M w
  rw [he, one_mul, IsGalois.card_aut_eq_finrank, ← card_fibre] at hfund
  rcases hl.eq_one_or_self_of_dvd _ (Dvd.intro_left _ hfund) with h | h
  · rw [h, mul_one] at hfund
    exact Or.inl ⟨hfund, fun w hw => by rw [hn w hw, h, pow_one]⟩
  · rw [h] at hfund
    exact Or.inr ⟨Nat.eq_of_mul_eq_mul_right hl.pos (hfund.trans (one_mul _).symm),
      fun w hw => by rw [hn w hw, h]⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.FibreCG
section
open UpperTheory.ConvolutionTheory.R

open GlobalTheory.CuspRep Formalism.L2.Host

theorem UpperTheory.ConvolutionTheory.R.fibreCG :
    ClassChar → Count → NormCharPow → FibreCG := by
  intro hC hN hP K M _ _ _ _ _ _ _ _ hl n π P hn hπ
  classical
  obtain ⟨η, hη⟩ := hC K M hl
  obtain ⟨hp1, hp2⟩ := hP K M hl η hη
  have key : ∀ π₁ : CG K n, UpperTheory.V.Published.WeakBC π₁.HasSat P.HasSat →
      ((Finset.range (Module.finrank K M)).filter fun j => π₁ = π.twist (η ^ j)).card = 1 := by
    intro π₁ h₁
    have := hN K M hl η hη n π π₁ Unit (fun _ => n) (fun _ => P) hn (fun _ => hn)
      (by rw [sumSat_unit]; exact hπ) (by rw [sumSat_unit]; exact h₁)
    convert this using 1
    simp
  refine ⟨fun χ hχ he => ?_, fun π₁ h₁ => ?_⟩
  · obtain ⟨j, hj0, hjl, rfl⟩ := hp1 χ hχ
    obtain ⟨a, ha⟩ := Finset.card_eq_one.1 (key π hπ)
    have h0 : 0 ∈ (Finset.range (Module.finrank K M)).filter fun j => π = π.twist (η ^ j) := by
      rw [Finset.mem_filter, Finset.mem_range, pow_zero, CG.twist_one]
      exact ⟨hl.pos, rfl⟩
    have h1 : j ∈ (Finset.range (Module.finrank K M)).filter fun j => π = π.twist (η ^ j) := by
      rw [Finset.mem_filter, Finset.mem_range]
      exact ⟨hjl, he.symm⟩
    rw [ha, Finset.mem_singleton] at h0 h1
    omega
  · obtain ⟨a, ha⟩ := Finset.card_eq_one.1 (key π₁ h₁)
    have h1 : a ∈ (Finset.range (Module.finrank K M)).filter fun j => π₁ = π.twist (η ^ j) := by
      rw [ha]; exact Finset.mem_singleton_self a
    rw [Finset.mem_filter, Finset.mem_range] at h1
    refine ⟨η ^ a, ?_, h1.2.symm⟩
    rcases Nat.eq_zero_or_pos a with rfl | h
    · exact Or.inl (pow_zero _)
    · exact Or.inr (hp2 a h h1.1)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.Imports
section
open UpperTheory.ConvolutionTheory.R

open NumberField in
private theorem not_both (F : Type) [Field F] [NumberField F] (h : IsTotallyReal F) (h' : IsTotallyComplex F) : False := by
  obtain ⟨v⟩ : Nonempty (InfinitePlace F) := inferInstance
  exact (InfinitePlace.not_isReal_iff_isComplex.2 (h'.isComplex v)) (h.isReal v)

theorem UpperTheory.ConvolutionTheory.R.fibre :
    FibreCG → Fibre := by
  intro H K M _ _ _ _ _ _ hK hM hp n hn π P hbc
  rcases π with @⟨_, π⟩ | @⟨hR, π⟩
  swap
  · exact (not_both K hR hK).elim
  rcases P with @⟨_, P⟩ | @⟨hR, P⟩
  swap
  · exact (not_both M hR hM).elim
  obtain ⟨h1, h2⟩ := H K M hp n (GlobalTheory.CuspRep.CG.mk π) (GlobalTheory.CuspRep.CG.mk P) hn hbc
  refine ⟨fun η hη hi => h1 η hη (Quotient.sound hi), fun π₁ hbc₁ => ?_⟩
  rcases π₁ with @⟨_, π₁⟩ | @⟨hR, π₁⟩
  swap
  · exact (not_both K hR hK).elim
  obtain ⟨η, hη, e⟩ := h2 (GlobalTheory.CuspRep.CG.mk π₁) hbc₁
  exact ⟨η, hη, Quotient.exact e⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.LiftPow
section
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V.Published UpperTheory.CBC PositivityTheory.RgJS
open UpperTheory.ConvolutionTheory.R

private theorem exPow (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] : ∃ ν : ℂ → HChar E,
    ∀ z v, (ν z).UnrAt v ∧ ((ν z).val v : ℂ) = (normV v : ℂ) ^ (-z) := by
  obtain ⟨a, ha⟩ : ∃ a : ℝ → HChar E, ∀ t, (a t).IsAbsPow t :=
    ⟨UnitExponent.nu E, fun t => GlobalTheory.Mem.Chr.CharModel.absChar_isAbsPow (F := E) t⟩
  obtain ⟨b, hb, -⟩ := norm_exponent_equality E
  refine ⟨fun z => a z.re * b z.im, fun z v => ⟨fun x hx => ?_, ?_⟩⟩
  · change (a z.re).loc v x * (b z.im).loc v x = 1
    rw [(ha _).1 v x hx, (hb _ v).1 x hx, one_mul]
  · have h0 : ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ≠ 0 := by
      exact_mod_cast fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
    rw [HChar.val_mul, Units.val_mul, (ha _).2.1 v, (hb _ v).2, ← Complex.cpow_add _ _ h0, ← neg_add, Complex.re_add_im]
    rw [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.LiftSum
section
open UpperTheory.ConvolutionTheory.R

theorem UpperTheory.ConvolutionTheory.R.liftSum :
    LiftSum := by
  intro K M _ _ _ _ _ _ _ _ _ ι _ κ _ n m π P h
  have h' := Filter.eventually_all.2 h
  refine h'.mono fun w hw f hf => ?_
  choose B hB C hC e using fun i => hw i f hf
  refine ⟨∑ i, B i, ⟨B, hB, rfl⟩, fun a => C a.1 a.2, fun a => hC a.1 a.2, ?_⟩
  rw [Fintype.sum_sigma]
  have : (∑ i, B i).map (· ^ f) = ∑ i, (B i).map (· ^ f) :=
    map_sum (Multiset.mapAddMonoidHom (· ^ f)) B Finset.univ
  rw [this]
  exact Finset.sum_congr rfl fun i _ => e i
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.NormCharPow
section
open UpperTheory.ConvolutionTheory.R

open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.L2.Host UpperTheory.V.Published

theorem UpperTheory.ConvolutionTheory.R.normCharPow :
    Count → NormCharPow := by
  classical
  intro hN K M _ _ _ _ _ _ _ _ hl η hη
  have hp : ∀ (n : ℕ) (v : HeightOneSpectrum (𝓞 K)), (η ^ n).val v = η.val v ^ n :=
    fun n v => MonoidHom.pow_apply η.1 n _
  refine ⟨fun χ hχ => ?_, fun j hj0 hjl => ⟨fun h => ?_, ?_, ?_⟩⟩
  · have hW : ∀ ψ : HChar K, (∀ᶠ w : HeightOneSpectrum (𝓞 M) in Filter.cofinite, ∀ f : ℕ,
        Formalism.ConjugateSelfDual.normV w = Formalism.ConjugateSelfDual.normV (w.under (𝓞 K)) ^ f → ψ.val (w.under (𝓞 K)) ^ f = 1) →
        WeakBC (CG.ofChar ψ).HasSat (sumSat (m := fun _ : Unit => 1) fun _ => CG.ofChar (1 : HChar M)) := by
      intro ψ h
      rw [sumSat_unit]
      filter_upwards [h, (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.tendsto_under K M).eventually
        (Filter.eventually_cofinite.2 (GlobalTheory.Mem.UnrAe.finite_ramified ψ))] with w h1 h2 f hf
      refine ⟨_, CG.hasSat_ofChar h2, ?_⟩
      rw [Multiset.map_singleton, h1 f hf]
      exact CG.hasSat_ofChar (χ := 1) (w := w) fun _ _ => rfl
    have h1 := hN K M hl η hη 1 (CG.ofChar 1) (CG.ofChar χ) Unit (fun _ => 1) (fun _ => CG.ofChar 1) le_rfl
      (fun _ => le_rfl) (hW 1 (Filter.Eventually.of_forall fun w f _ => one_pow f)) (hW χ hχ.2.2)
    have h2 : 0 < ((Finset.range (Module.finrank K M)).filter
        fun j => CG.ofChar χ = (CG.ofChar 1).twist (η ^ j)).card := by
      rw [h1]
      exact Finset.card_pos.2 ⟨((), ()), by simp⟩
    obtain ⟨j, hj⟩ := Finset.card_pos.1 h2
    rw [Finset.mem_filter, Finset.mem_range, CG.twist_ofChar, one_mul] at hj
    have e := CG.ofChar_injective hj.2
    refine ⟨j, Nat.pos_of_ne_zero ?_, hj.1, e⟩
    rintro rfl
    exact hχ.1 (e.trans (pow_zero _))
  · haveI := Fact.mk hl
    have ho := orderOf_eq_prime hη.1.2.1 hη.1.1
    have := Nat.le_of_dvd hj0 (orderOf_dvd_of_pow_eq_one h)
    omega
  · rw [← pow_mul, mul_comm, pow_mul, hη.1.2.1, one_pow]
  · refine hη.1.2.2.mono fun w hw f hf => ?_
    rw [hp, ← pow_mul, mul_comm, pow_mul, hw f hf, one_pow]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.PartBOfDecomposition
section
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep PositivityTheory.RgJS PositivityTheory.Rg.Tf.ChR

namespace UpperTheory.ConvolutionTheory.R

namespace Pb2

theorem val_pow {E : Type} [Field E] [NumberField E] (η : HChar E) (j : ℕ) (v : HeightOneSpectrum (𝓞 E)) :
    (η ^ j).val v = η.val v ^ j := by
  induction j with
  | zero => rfl
  | succ j ih => rw [pow_succ, pow_succ, ← ih]; rfl

end Pb2

open Pb2

end UpperTheory.ConvolutionTheory.R
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.SysEx
section
open UpperTheory.ConvolutionTheory.R

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep PositivityTheory.RgJS in
theorem UpperTheory.ConvolutionTheory.R.sysEx :
    SysEx := by
  intro E _ _ _ X hfin hX
  classical
  have hRSU : RSU := rankin_selberg_unitary_of_pole norm_exponent_equality satake_twist_holds PositivityTheory.AdelicQuotientData.rsPole
  have hBd : GlobalTheory.Published.JacquetShalikaBound := PositivityTheory.JacquetShalikaLocal.jacquetShalikaBound
  have hDO : DetOne := determinant_one_condition_holds
  have hPO : PrimeOff := prime_sum_converges_and_diverges
  have : Fintype X := hfin.fintype
  choose S0 hS0 using fun x y : X =>
    hRSU E x.1.1 y.1.1 x.1.2 y.1.2 (hX x x.2).1 (hX y y.2).1 (hX x x.2).2.1 (hX y y.2).2.1
  have hw : ∀ᶠ w in Filter.cofinite, ∀ x : X, ∃ B, x.1.2.HasSat w B :=
    Filter.eventually_all.2 fun x => (hX x x.2).2.2
  refine ⟨(Filter.eventually_cofinite.1 hw).toFinset ∪ Finset.univ.biUnion (fun p : X × X => S0 p.1 p.2), fun S hS => ?_⟩
  have hex : ∀ (x : X) (w : Off E S), ∃ f : Fin x.1.1 → ℂˣ, x.1.2.HasSat w.1 (Finset.univ.val.map f) := by
    intro x w
    have h : ∀ x : X, ∃ B, x.1.2.HasSat w.1 B := by
      by_contra h
      exact w.2 (hS (Finset.mem_union_left _ (by rw [Set.Finite.mem_toFinset]; exact h)))
    obtain ⟨B, hB⟩ := h x
    obtain ⟨f, hf⟩ := RigidityLemmas.exists_fin _ hB.card
    exact ⟨f, hf ▸ hB⟩
  choose α hα using hex
  have hsub : ∀ x y : X, S0 x y ⊆ S := fun x y z hz =>
    hS (Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨(x, y), Finset.mem_univ _, hz⟩))
  refine ⟨α, hα, hPO E S, fun x => (hX x x.2).1, fun x w a => ?_, fun x w => ?_, fun x y => ?_⟩
  · have h := (hBd E x.1.1 x.1.2 (hX x x.2).2.1 w.1 _ (hα x w) (α x w a)
      (Multiset.mem_map_of_mem _ (Finset.mem_univ_val _))).2
    show ‖((α x w a : ℂˣ) : ℂ)‖ ≤ Real.sqrt ((Ideal.absNorm w.1.asIdeal : ℕ) : ℝ)
    rw [Real.sqrt_eq_rpow]
    exact h.le
  · have h := hDO E x.1.1 x.1.2 w.1 _ (hX x x.2).2.1 (hα x w)
    rw [← Finset.prod_eq_multiset_prod, Units.coe_prod] at h
    exact h
  · obtain ⟨F, σ₀, hF, hFe⟩ := hS0 x y S (hsub x y) (α x) (α y) (hα x) (hα y)
    refine ⟨F, σ₀, hF, fun σ hσ => ?_⟩
    rw [hFe σ hσ]
    by_cases hxy : x = y
    · subst hxy
      rw [if_pos rfl, if_pos rfl]
      rfl
    · rw [if_neg (fun h => hxy (Subtype.ext (by simpa using h))), if_neg hxy]
      rfl
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.TwoParts
section
open UpperTheory.ConvolutionTheory.R

theorem UpperTheory.ConvolutionTheory.R.twoParts :
    ClassChar → Count → NormCharPow → TwoParts := by
  classical
  intro hC hCount hN K M _ _ _ _ _ _ _ _ hp n π ι _ m P hn hm hι hW
  obtain ⟨η, hη⟩ := hC K M hp
  have h1 := hCount K M hp η hη n π π ι m P hn hm hW hW
  obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card (show 1 < Fintype.card ι from hι)
  have h2 : 1 < ((Finset.range (Module.finrank K M)).filter fun j => π = π.twist (η ^ j)).card := by
    rw [h1, Finset.one_lt_card]
    refine ⟨(a, a), by simp, (b, b), by simp, fun h => hab (congrArg Prod.fst h)⟩
  obtain ⟨j, hj, hj0⟩ := Finset.exists_mem_ne h2 0
  rw [Finset.mem_filter, Finset.mem_range] at hj
  exact ⟨η ^ j, (hN K M hp η hη).2 j (Nat.pos_of_ne_zero hj0) hj.1, hj.2.symm⟩
end

