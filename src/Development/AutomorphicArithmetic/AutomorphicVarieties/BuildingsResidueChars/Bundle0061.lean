module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.GLDenseRanges.KirCusp
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.IsTheta
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.LocCFTAll
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.GlBridge
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IsSplitAtOfDecompositionLeRestrictionRange
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1799
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitaryClassSetFinite
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0215
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0057

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.MemFixedOfCharacterSumProjection
section
open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.Z.Desc.V0

private theorem chi_orth {Q : Type} [Group Q] [Fintype Q] (f g : Q →* ℂˣ) (h : f ≠ g) :
    ∑ x, (((f x)⁻¹ : ℂˣ) : ℂ) * ((g x : ℂˣ) : ℂ) = 0 := by
  obtain ⟨y, hy⟩ : ∃ y, f y ≠ g y := by
    by_contra hne
    push_neg at hne
    exact h (MonoidHom.ext hne)
  have ha : ((f y)⁻¹ * g y : ℂˣ) ≠ 1 := by
    intro h1
    exact hy (inv_mul_eq_one.mp h1)
  have ha' : ((((f y)⁻¹ * g y : ℂˣ)) : ℂ) ≠ 1 := by
    intro h1
    exact ha (Units.val_eq_one.mp h1)
  have key : ∑ x, (((f x)⁻¹ : ℂˣ) : ℂ) * ((g x : ℂˣ) : ℂ)
      = ((((f y)⁻¹ * g y : ℂˣ)) : ℂ) * ∑ x, (((f x)⁻¹ : ℂˣ) : ℂ) * ((g x : ℂˣ) : ℂ) := by
    rw [Finset.mul_sum, ← Equiv.sum_comp (Equiv.mulLeft y)]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [Equiv.coe_mulLeft, map_mul, _root_.mul_inv_rev, Units.val_mul]
    ring
  have h2 : (((((f y)⁻¹ * g y : ℂˣ)) : ℂ) - 1) * ∑ x, (((f x)⁻¹ : ℂˣ) : ℂ) * ((g x : ℂˣ) : ℂ) = 0 := by
    linear_combination -key
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact absurd (sub_eq_zero.mp h3) ha'
  · exact h3

private theorem c_conv {Q I : Type} [Group Q] [Fintype Q] [Fintype I]
    (χ : I → Q →* ℂˣ) (hχ : Function.Injective χ) (c : Q → ℤ)
    (hc : ∀ x, (c x : ℂ) = ∑ t, (((χ t x)⁻¹ : ℂˣ) : ℂ)) (w : Q) :
    ∑ x, c x * c (x⁻¹ * w) = (Fintype.card Q : ℤ) * c w := by
  classical
  have hQ : ∀ t s : I, ∑ x, (((χ t x)⁻¹ : ℂˣ) : ℂ) * ((χ s x : ℂˣ) : ℂ)
      = if t = s then (Fintype.card Q : ℂ) else 0 := by
    intro t s
    split_ifs with hts
    · subst hts
      simp
    · exact chi_orth _ _ (fun e => hts (hχ e))
  have term : ∀ (x : Q) (t s : I), (((χ t x)⁻¹ : ℂˣ) : ℂ) * (((χ s (x⁻¹ * w))⁻¹ : ℂˣ) : ℂ)
      = (((χ s w)⁻¹ : ℂˣ) : ℂ) * ((((χ t x)⁻¹ : ℂˣ) : ℂ) * ((χ s x : ℂˣ) : ℂ)) := by
    intro x t s
    simp only [map_mul, map_inv, _root_.mul_inv_rev, inv_inv, Units.val_mul]
    ring
  apply Int.cast_injective (α := ℂ)
  simp only [Int.cast_sum, Int.cast_mul, Int.cast_natCast, hc]
  calc ∑ x, (∑ t, (((χ t x)⁻¹ : ℂˣ) : ℂ)) * ∑ s, (((χ s (x⁻¹ * w))⁻¹ : ℂˣ) : ℂ)
      = ∑ x, ∑ t, ∑ s, (((χ s w)⁻¹ : ℂˣ) : ℂ) * ((((χ t x)⁻¹ : ℂˣ) : ℂ) * ((χ s x : ℂˣ) : ℂ)) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun s _ => term x t s
    _ = ∑ t, ∑ s, ∑ x, (((χ s w)⁻¹ : ℂˣ) : ℂ) * ((((χ t x)⁻¹ : ℂˣ) : ℂ) * ((χ s x : ℂˣ) : ℂ)) :=
        Finset.sum_comm.trans (Finset.sum_congr rfl fun t _ => Finset.sum_comm)
    _ = ∑ t, ∑ s, (((χ s w)⁻¹ : ℂˣ) : ℂ) * (if t = s then (Fintype.card Q : ℂ) else 0) := by
        simp only [← Finset.mul_sum, hQ]
    _ = (Fintype.card Q : ℂ) * ∑ t, (((χ t w)⁻¹ : ℂˣ) : ℂ) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun t _ => ?_
        simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
        ring

private theorem opE_sum {G R W Q : Type} [Group G] [CommRing R] [AddCommGroup W] [Module R W]
    [Fintype Q] (ρ : Representation R G W) (g : Q → G) (c : Q → ℤ) :
    opE ρ (∑ x, Finsupp.single (g x) (c x)) = ∑ x, c x • ρ (g x) := by
  show (∑ x, Finsupp.single (g x) (c x)).sum (fun h n => n • ρ h) = _
  rw [← Finsupp.sum_finsetSum_index (fun a => zero_smul ℤ (ρ a)) (fun a m n => add_smul m n (ρ a))]
  exact Finset.sum_congr rfl fun x _ => Finsupp.sum_single_index (zero_smul ℤ (ρ (g x)))

theorem UpperTheory.mem_fixed_of_character_sum_projection :
    ∀ {G Q A I : Type} [Group G] [Group Q] [Fintype Q] [Group A] [Fintype I]
        (K : Subgroup G) (ι : A →* G) (π : A →* Q) (s : Q → A), (∀ x, π (s x) = x) →
        (∀ a, π a = 1 ↔ ι a ∈ K) → (∀ a, ∀ u ∈ K, (ι a)⁻¹ * u * ι a ∈ K) →
        ∀ (χ : I → Q →* ℂˣ), Function.Injective χ → ∀ (c : Q → ℤ),
        (∀ x, (c x : ℂ) = ∑ t, (((χ t x)⁻¹ : ℂˣ) : ℂ)) → ∀ (R W : Type) [CommRing R] [AddCommGroup W] [Module R W] (ρ : Representation R G W) (v : W), v ∈ fixd ρ K →
        opE ρ (∑ x, Finsupp.single (ι (s x)) (c x)) (opE ρ (∑ x, Finsupp.single (ι (s x)) (c x)) v) =
          Fintype.card Q • opE ρ (∑ x, Finsupp.single (ι (s x)) (c x)) v := by
  intro G Q A I _ _ _ _ _ K ι π s hs hker _ χ hχ c hc R W _ _ _ ρ v hv
  have hv' : ∀ u ∈ K, ρ u v = v := hv
  have hT : ∀ y x, ρ (ι (s y)) (ρ (ι (s x)) v) = ρ (ι (s (y * x))) v := by
    intro y x
    have hk : ι ((s (y * x))⁻¹ * (s y * s x)) ∈ K := by
      rw [← hker]
      simp [map_mul, map_inv, hs]
    calc ρ (ι (s y)) (ρ (ι (s x)) v) = ρ (ι (s y * s x)) v := by
          simp only [map_mul, Module.End.mul_apply]
      _ = ρ (ι (s (y * x) * ((s (y * x))⁻¹ * (s y * s x)))) v := by rw [mul_inv_cancel_left]
      _ = ρ (ι (s (y * x))) v := by
          rw [map_mul ι, map_mul ρ, Module.End.mul_apply, hv' _ hk]
  have hE : opE ρ (∑ x, Finsupp.single (ι (s x)) (c x)) = ∑ x, c x • ρ (ι (s x)) :=
    opE_sum ρ (fun x => ι (s x)) c
  rw [hE]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_zsmul, Finset.smul_sum, smul_smul, hT]
  calc ∑ a, ∑ b, (c a * c b) • ρ (ι (s (b * a))) v
      = ∑ b, ∑ a, (c a * c b) • ρ (ι (s (b * a))) v := Finset.sum_comm
    _ = ∑ b, ∑ z, (c b * c (b⁻¹ * z)) • ρ (ι (s z)) v := by
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [← Equiv.sum_comp (Equiv.mulLeft b⁻¹)]
        refine Finset.sum_congr rfl fun z _ => ?_
        simp only [Equiv.coe_mulLeft, mul_inv_cancel_left]
        rw [mul_comm (c (b⁻¹ * z))]
    _ = ∑ z, (∑ b, c b * c (b⁻¹ * z)) • ρ (ι (s z)) v := by
        rw [Finset.sum_comm]
        simp only [Finset.sum_smul]
    _ = ∑ z, Fintype.card Q • c z • ρ (ι (s z)) v := by
        refine Finset.sum_congr rfl fun z _ => ?_
        rw [c_conv χ hχ c hc z, mul_smul, natCast_zsmul]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.MemHeckeLevelOfLocalComponentsMem
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

theorem UpperTheory.mem_heckeLevel_of_local_components_mem :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n → ∀ (V : s.Lev) (Q : QData V) (c : Coef l) (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O) (K : (hset Q τ₀).Lev) (u : Ub n s), (∀ w : Plc L, w.under (𝓞 (Lp L)) ∉ V.S' → cmp n w (u : Ga l L n) ∈ KO (w.adicCompletion L) (Fin n)) → (∀ q : Q.Q, cmp n (Q.wq q) (u : Ga l L n) ∈ K.1 q) → u ∈ (hset Q τ₀).lev K := by
  intro l _ L Ω _ _ _ _ _ _ s n hn V Q c m τ₀ K
  classical
  have hS : ∀ q : Q.Q, (Q.wq q).under (𝓞 (Lp L)) ∈ V.S' := fun q => by
    rw [Q.range]
    exact Or.inr ⟨q, rfl⟩
  have hsec := fun q : Q.Q => (secU l L Ω s n hn (Q.wq q)
    (UpperTheory.isSplitAt_of_decomposition_le_restriction_range L Ω _ _ (s.hA _) (V.split _ (hS q)) _ rfl)).2 (Q.notS q)
  have h1 : ∀ (q : Q.Q) (g : GLw n (Q.wq q)) (w : Plc L), w.under (𝓞 (Lp L)) ≠ (Q.wq q).under (𝓞 (Lp L)) →
      CaseU.cmp n w ((sec n s (Q.wq q) g : Ub n s) : Ga l L n) = 1 := fun q g w hw =>
    MonoidHom.mem_ker.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 ((hsec q).2.2 g) w) hw)
  have key : ∀ (T : Finset Q.Q) (u : Ub n s),
      (∀ w : Plc L, w.under (𝓞 (Lp L)) ∉ V.S' → CaseU.cmp n w (u : Ga l L n) ∈ KO (w.adicCompletion L) (Fin n)) →
      (∀ q : Q.Q, CaseU.cmp n (Q.wq q) (u : Ga l L n) ∈ K.1 q) →
      (∀ q ∉ T, CaseU.cmp n (Q.wq q) (u : Ga l L n) = 1) → u ∈ (hset Q τ₀).lev K := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      intro u hu _ h0
      refine Subgroup.mem_sup_left (S := UQ n Q) ?_
      exact Subgroup.mem_inf.2 ⟨Subgroup.mem_iInf.2 fun w => Subgroup.mem_iInf.2 fun hw => hu w hw,
        Subgroup.mem_iInf.2 fun q => MonoidHom.mem_ker.2 (h0 q (Finset.notMem_empty q))⟩
    | insert q T _ ih =>
      intro u hu hK h0
      let x : Ub n s := sec n s (Q.wq q) (CaseU.cmp n (Q.wq q) (u : Ga l L n))
      have hx : x ∈ (hset Q τ₀).lev K :=
        Subgroup.mem_sup_right (Subgroup.mem_iSup_of_mem q ⟨_, hK q, rfl⟩)
      have e1 : ∀ w : Plc L, w.under (𝓞 (Lp L)) ≠ (Q.wq q).under (𝓞 (Lp L)) →
          CaseU.cmp n w ((x⁻¹ * u : Ub n s) : Ga l L n) = CaseU.cmp n w (u : Ga l L n) := fun w hw => by
        rw [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, h1 q _ w hw, inv_one, one_mul]
      have e2 : CaseU.cmp n (Q.wq q) ((x⁻¹ * u : Ub n s) : Ga l L n) = 1 := by
        rw [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, (hsec q).2.1, inv_mul_cancel]
      have hy : x⁻¹ * u ∈ (hset Q τ₀).lev K := by
        refine ih _ (fun w hw => ?_) (fun q' => ?_) fun q' hq' => ?_
        · rw [e1 w fun h => hw (h ▸ hS q)]
          exact hu w hw
        · by_cases h : q' = q
          · subst h
            rw [e2]
            exact one_mem _
          · rw [e1 _ fun h' => h (Q.inj h')]
            exact hK q'
        · by_cases h : q' = q
          · subst h
            exact e2
          · rw [e1 _ fun h' => h (Q.inj h')]
            exact h0 q' fun h' => (Finset.mem_insert.1 h').elim h hq'
      have e : u = x * (x⁻¹ * u) := (mul_inv_cancel_left x u).symm
      rw [e]
      exact Subgroup.mul_mem _ hx hy
  exact fun u hu hK => key Finset.univ u hu hK fun q hq => (hq (Finset.mem_univ q)).elim
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.PlaceEmbeddingsBijectiveInfinitePlaces
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

private theorem mem_iff {l : ℕ} [Fact l.Prime] {L : Type} [Field L] [NumberField L] {w : Plc L} (j : W.Emb l w) (x : 𝓞 L) :
    x ∈ w.asIdeal ↔ ‖j.1 (algebraMap L _ (x : L))‖ < 1 := by
  have h : w.asIdeal ≤ (GlobalTheory.EvExtend.placeOf (j.1.comp (algebraMap L _))).asIdeal := fun y hy => by
    rw [GlobalTheory.EvExtend.mem_placeOf]
    have h1 : Valued.v (algebraMap L (w.adicCompletion L) (y : L)) < 1 := by
      rw [ReciprocityTheory.Aut.adic_valued_algebraMap]
      exact (w.valuation_lt_one_iff_mem (K := L) y).2 hy
    have h2 := (j.2.tendsto 0).comp (Valued.tendsto_zero_pow_of_v_lt_one h1)
    rw [map_zero] at h2
    refine tendsto_pow_atTop_nhds_zero_iff_norm_lt_one.1 (h2.congr fun n => ?_)
    exact map_pow j.1 _ n
  rw [w.isMaximal.eq_of_le (GlobalTheory.EvExtend.placeOf _).isPrime.ne_top h, GlobalTheory.EvExtend.mem_placeOf]
  rfl

private theorem cc {L : Type} [Field L] [NumberField L] [IsCMField L] (x : 𝓞 L) :
    IsCMField.ringOfIntegersComplexConj L (IsCMField.ringOfIntegersComplexConj L x) = x :=
  RingOfIntegers.ext (IsCMField.complexConj_apply_apply L x)

private theorem norm_mem {L : Type} [Field L] [NumberField L] [IsCMField L] {u w : Plc L}
    (hu : u.under (𝓞 (Lp L)) = w.under (𝓞 (Lp L))) {x : 𝓞 L} (hx : x ∈ u.asIdeal) :
    x ∈ w.asIdeal ∨ IsCMField.ringOfIntegersComplexConj L x ∈ w.asIdeal := by
  obtain ⟨y, hy⟩ := (IsCMField.ringOfIntegersComplexConj_eq_self_iff L (x * IsCMField.ringOfIntegersComplexConj L x)).1 (by
    rw [map_mul, mul_comm, cc])
  have h1 : y ∈ (u.under (𝓞 (Lp L))).asIdeal := by
    change algebraMap _ (𝓞 L) y ∈ u.asIdeal
    rw [hy]
    exact Ideal.mul_mem_right _ _ hx
  rw [hu] at h1
  change algebraMap _ (𝓞 L) y ∈ w.asIdeal at h1
  rw [hy] at h1
  exact w.isPrime.mem_or_mem h1

private theorem not_stable {L : Type} [Field L] [NumberField L] [IsCMField L] {w : Plc L} (hw : IsSplitAt w)
    (h : ∀ x, IsCMField.ringOfIntegersComplexConj L x ∈ w.asIdeal → x ∈ w.asIdeal) : False := by
  obtain ⟨u, hu, hu'⟩ := hw
  exact hu (HeightOneSpectrum.ext (u.isMaximal.eq_of_le w.isPrime.ne_top fun x hx => (norm_mem hu' hx).elim id (h x)))

private theorem two {L : Type} [Field L] [NumberField L] [IsCMField L] {u w : Plc L}
    (hu : u.under (𝓞 (Lp L)) = w.under (𝓞 (Lp L))) :
    u = w ∨ ∀ x, x ∈ u.asIdeal ↔ IsCMField.ringOfIntegersComplexConj L x ∈ w.asIdeal := by
  haveI := w.isPrime
  have h : (u.asIdeal : Set (𝓞 L)) ⊆ w.asIdeal ∪ w.asIdeal.comap (IsCMField.ringOfIntegersComplexConj L) :=
    fun x hx => norm_mem hu hx
  rcases Ideal.subset_union.1 h with h | h
  · exact Or.inl (HeightOneSpectrum.ext (u.isMaximal.eq_of_le w.isPrime.ne_top h))
  · refine Or.inr fun x => ?_
    rw [u.isMaximal.eq_of_le (Ideal.comap_ne_top _ w.isPrime.ne_top) h, Ideal.mem_comap]

private theorem ex_emb {l : ℕ} [Fact l.Prime] {L : Type} [Field L] [NumberField L] {w : Plc L} (τ : L →+* Qbar l)
    (h : ∀ x : 𝓞 L, x ∈ w.asIdeal ↔ ‖τ x‖ < 1) : ∃ j : W.Emb l w, j.1.comp (algebraMap L _) = τ := by
  have e : w = GlobalTheory.EvExtend.placeOf τ := HeightOneSpectrum.ext (Ideal.ext fun x => by
    rw [GlobalTheory.EvExtend.mem_placeOf, h])
  subst e
  obtain ⟨j, hc, hx, -⟩ := GlobalTheory.EvExtend.exists_ext τ
  exact ⟨⟨j, hc⟩, RingHom.ext hx⟩

theorem UpperTheory.placeEmbeddings_bijective_infinitePlaces :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (V : s.Lev) (ι : Qbar l ≃+* ℂ), Finite (Emb l (fun v : V.frame.Vl => s.w v.1)) ∧ Function.Bijective (fun x : Emb l (fun v : V.frame.Vl => s.w v.1) => InfinitePlace.mk (ι.toRingHom.comp x.res)) := by
  intro l _ L Ω _ _ _ _ _ _ s V ι
  obtain ⟨hun, hsp⟩ := UpperTheory.under_chosen_place_and_isSplitAt_of_decomp_le l L Ω s
  have hinj : Function.Injective
      (fun x : Emb l (fun v : V.frame.Vl => s.w v.1) => InfinitePlace.mk (ι.toRingHom.comp x.res)) := by
    rintro ⟨v, j⟩ ⟨v', j'⟩ h
    rcases InfinitePlace.mk_eq_iff.1 h with h | h
    · have h1 : ∀ x : L, j.1 (algebraMap L _ x) = j'.1 (algebraMap L _ x) := fun x =>
        ι.injective (RingHom.congr_fun h x)
      have h2 : s.w v.1 = s.w v'.1 := HeightOneSpectrum.ext (Ideal.ext fun x => by
        rw [mem_iff j, mem_iff j', h1])
      have h3 : v = v' := Subtype.ext (by rw [← hun v.1, h2, hun])
      subst h3
      refine congrArg (Sigma.mk v) (Subtype.ext (DFunLike.coe_injective ?_))
      exact (HeightOneSpectrum.denseRange_algebraMap L (s.w v.1)).equalizer j.2 j'.2 (funext h1)
    · have h1 : ∀ x : L, j.1 (algebraMap L _ (IsCMField.complexConj L x)) = j'.1 (algebraMap L _ x) := fun x =>
        ι.injective ((IsCMField.complexEmbedding_complexConj L _ x).trans (RingHom.congr_fun h x))
      have h2 : ∀ x, IsCMField.ringOfIntegersComplexConj L x ∈ (s.w v.1).asIdeal ↔ x ∈ (s.w v'.1).asIdeal := fun x => by
        rw [mem_iff j, mem_iff j', ← h1]
        rfl
      have h3 : v = v' := Subtype.ext (by
        rw [← hun v.1, ← hun v'.1]
        refine HeightOneSpectrum.ext (Ideal.ext fun y => ?_)
        change algebraMap _ (𝓞 L) y ∈ (s.w v.1).asIdeal ↔ algebraMap _ (𝓞 L) y ∈ (s.w v'.1).asIdeal
        rw [← h2, (IsCMField.ringOfIntegersComplexConj_eq_self_iff L _).2 ⟨y, rfl⟩])
      subst h3
      refine (not_stable (hsp (s.w v.1) ?_) fun x hx => (h2 x).1 hx).elim
      rw [hun]
      exact s.split _ (Or.inl v.2)
  refine ⟨Finite.of_injective _ hinj, hinj, fun p => ?_⟩
  obtain ⟨φ, rfl⟩ : ∃ φ, InfinitePlace.mk φ = p := ⟨_, p.mk_embedding⟩
  let τ : L →+* Qbar l := ι.symm.toRingHom.comp φ
  have hl : ((l : ℕ) : 𝓞 (Lp L)) ∈ ((GlobalTheory.EvExtend.placeOf τ).under (𝓞 (Lp L))).asIdeal := by
    change algebraMap _ (𝓞 L) ((l : ℕ) : 𝓞 (Lp L)) ∈ (GlobalTheory.EvExtend.placeOf τ).asIdeal
    rw [map_natCast, GlobalTheory.EvExtend.mem_placeOf]
    simpa using GlobalTheory.EvExtend.norm_natCast_lt_one (l := l)
  rcases two (hun ((GlobalTheory.EvExtend.placeOf τ).under (𝓞 (Lp L)))).symm with h | h
  · obtain ⟨j, hj⟩ := ex_emb (w := s.w ((GlobalTheory.EvExtend.placeOf τ).under (𝓞 (Lp L)))) τ fun x => by
      rw [← h, GlobalTheory.EvExtend.mem_placeOf]
    refine ⟨⟨⟨_, hl⟩, j⟩, congrArg InfinitePlace.mk (RingHom.ext fun x => ?_)⟩
    exact (congrArg ι (RingHom.congr_fun hj x)).trans (ι.apply_symm_apply _)
  · obtain ⟨j, hj⟩ := ex_emb (w := s.w ((GlobalTheory.EvExtend.placeOf τ).under (𝓞 (Lp L))))
      (τ.comp (IsCMField.complexConj L).toRingEquiv.toRingHom) fun x => by
        have h1 := h (IsCMField.ringOfIntegersComplexConj L x)
        rw [cc, GlobalTheory.EvExtend.mem_placeOf] at h1
        exact h1.symm
    refine ⟨⟨⟨_, hl⟩, j⟩, InfinitePlace.mk_eq_iff.2 (Or.inr (RingHom.ext fun x => ?_))⟩
    have h1 : ι (j.1 (algebraMap L _ x)) = φ (IsCMField.complexConj L x) :=
      (congrArg ι (RingHom.congr_fun hj x)).trans (ι.apply_symm_apply _)
    change starRingEnd ℂ (ι (j.1 (algebraMap L _ x))) = φ x
    rw [h1, IsCMField.complexEmbedding_complexConj, Complex.conj_conj]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.UnipotentUpperMapSurjective
section
open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.Z.Desc.V0

theorem UpperTheory.unipotent_upper_map_surjective :
    ∀ {S R : Type} [CommRing S] [CommRing R] (f : S →+* R), Function.Surjective f → ∀ (n : ℕ) (x : GL (Fin n) R), x ∈ unipB R (Fin n) →
        ∃ y ∈ unipB S (Fin n), GeneralLinearGroup.map (n := Fin n) f y = x := by
  intro S R _ _ f hf n x hx
  obtain ⟨hlow, hdiag⟩ := (mem_unipB R).1 hx
  let A : Matrix (Fin n) (Fin n) S := fun i j =>
    if i < j then Function.surjInv hf ((x : Matrix (Fin n) (Fin n) R) i j) else if i = j then 1 else 0
  have hA : A.BlockTriangular id := by
    intro i j hij
    have h1 : ¬ i < j := not_lt.2 (le_of_lt hij)
    have h2 : i ≠ j := ne_of_gt hij
    simp [A, h1, h2]
  have hdet : A.det = 1 := by
    rw [Matrix.det_of_upperTriangular hA]
    exact Finset.prod_eq_one fun i _ => by simp [A]
  have hunit : IsUnit A.det := by simp [hdet, isUnit_one]
  have hcoe : ((GeneralLinearGroup.mk'' A hunit : GL (Fin n) S) : Matrix (Fin n) (Fin n) S) = A := rfl
  refine ⟨GeneralLinearGroup.mk'' A hunit, (mem_unipB S).2 ⟨fun i j hji => ?_, fun i => ?_⟩, ?_⟩
  · rw [hcoe]
    exact hA hji
  · rw [hcoe]
    simp [A]
  · apply Units.ext
    ext i j
    have hmap : ((GeneralLinearGroup.map (n := Fin n) f (GeneralLinearGroup.mk'' A hunit) : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) i j = f (A i j) := rfl
    rw [hmap]
    rcases lt_trichotomy i j with h | h | h
    · simp only [A, if_pos h]
      exact Function.surjInv_eq hf _
    · subst h
      simp [A, hdiag]
    · have h1 : ¬ i < j := not_lt.2 (le_of_lt h)
      have h2 : i ≠ j := ne_of_gt h
      simp [A, h1, h2, hlow i j h]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.UnitaryAdelicLocalComponentsContinuousLevelsOpen
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

section SlopeTestRemainingChoices

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

private theorem nh_loc : IsLocalRing 𝒪[k] := (inferInstance : IsDiscreteValuationRing 𝒪[k]).toIsLocalRing
attribute [local instance] nh_loc

private theorem nh_unif : valuation k (unif k : k) = uniformizer k := by
  obtain ⟨x, hx⟩ := valuation_surjective (uniformizer k)
  have h0 : x ≠ 0 := by
    rintro rfl
    exact uniformizer_pos.ne (by simpa using hx)
  exact Classical.epsilon_spec (p := fun x : kˣ => valuation k (x : k) = uniformizer k) ⟨Units.mk0 x h0, hx⟩

private theorem nh_pow (c : ℕ) (x : 𝒪[k]) :
    x ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ c ↔ valuation k (x : k) ≤ uniformizer k ^ c := by
  have hI := Valuation.integer.integers (valuation k)
  let p : 𝒪[k] := ⟨unif k, (nh_unif.trans_lt uniformizer_lt_one).le⟩
  have hp : valuation k (algebraMap 𝒪[k] k p) = uniformizer k := nh_unif
  have e : IsLocalRing.maximalIdeal 𝒪[k] = Ideal.span {p} := by
    ext y
    rw [← IsLocalRing.residue_eq_zero_iff, GlobalTheory.StepData.residue_eq_zero_iff_lt, Ideal.mem_span_singleton,
      hI.dvd_iff_le, hp, le_uniformizer_iff]
    rfl
  rw [e, Ideal.span_singleton_pow, Ideal.mem_span_singleton, hI.dvd_iff_le, map_pow, map_pow, hp]
  rfl

private theorem nh_memKc {c : ℕ} {g : GL (Fin n) k} :
    g ∈ Kc k n c ↔ g ∈ KO k (Fin n) ∧ ∀ i j, valuation k ((g.val - 1) i j) ≤ uniformizer k ^ c := by
  have key : ∀ u : GL (Fin n) 𝒪[k],
      u ∈ (Matrix.GeneralLinearGroup.map (n := Fin n) (Ideal.Quotient.mk (IsLocalRing.maximalIdeal 𝒪[k] ^ c))).ker ↔
      ∀ i j, valuation k (((Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) u).val - 1) i j) ≤ uniformizer k ^ c := by
    intro u
    rw [MonoidHom.mem_ker, Units.ext_iff, ← Matrix.ext_iff]
    refine forall₂_congr fun i j => ?_
    have e : ((1 : GL (Fin n) (𝒪[k] ⧸ IsLocalRing.maximalIdeal 𝒪[k] ^ c)).val) i j =
        Ideal.Quotient.mk _ ((1 : Matrix (Fin n) (Fin n) 𝒪[k]) i j) := by
      simp only [Units.val_one, Matrix.one_apply]; split_ifs <;> simp
    rw [e]
    refine (Ideal.Quotient.eq.trans (nh_pow c _)).trans (iff_of_eq ?_)
    congr 2
    simp only [Matrix.sub_apply, Matrix.one_apply]; split_ifs <;> simp <;> rfl
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨⟨u, rfl⟩, (key u).1 hu⟩
  · rintro ⟨⟨u, rfl⟩, hu⟩
    exact ⟨u, (key u).2 hu, rfl⟩

private theorem nh_Kc_open (c : ℕ) : IsOpen (Kc k n c : Set (GL (Fin n) k)) := by
  have e : (Kc k n c : Set (GL (Fin n) k)) = (KO k (Fin n) : Set (GL (Fin n) k)) ∩
      ⋂ i, ⋂ j, (fun g : GL (Fin n) k => (g.val - 1) i j) ⁻¹' {x | valuation k x ≤ uniformizer k ^ c} := by
    ext g; simp only [SetLike.mem_coe, nh_memKc, Set.mem_iInter, Set.mem_inter_iff]; rfl
  rw [e]
  refine GlobalTheory.SplitFlip.isOpen_KO.inter <|
    isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => IsOpen.preimage ?_ ?_
  · have := Units.continuous_val (M := Matrix (Fin n) (Fin n) k)
    fun_prop
  · have h0 : (valuation k).restrict ((unif k : k) ^ c) ≠ 0 := by simp
    simpa only [Valuation.restrict_le_iff, map_pow (valuation k), nh_unif] using Valuation.isOpen_closedBall h0

end SlopeTestRemainingChoices

private theorem nh_open {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} : IsOpen ((⨅ w : Plc L, (KO (w.adicCompletion L) (Fin n)).comap (cLoc w) : Subgroup (UA L n)) : Set (UA L n)) := by
  let p : UA L n →* GL (Fin n) (Af L) := (Matrix.GeneralLinearGroup.map (pFin L)).comp (UA L n).subtype
  have hp : Continuous p := GlobalTheory.DefU.continuous_map_pFin.comp continuous_subtype_val
  have ho : IsOpen (GlobalTheory.GLIntegral.intSubring L : Set (Af L)) := RestrictedProduct.isOpen_forall_mem
    (A := fun v : HeightOneSpectrum (𝓞 L) => (v.adicCompletionIntegers L : Set (v.adicCompletion L)))
    (fun v => Valued.isOpen_valuationSubring _)
  refine Subgroup.isOpen_mono (H₁ := (GlobalTheory.GLIntegral.glSub (GlobalTheory.GLIntegral.intSubring L)).comap p) (fun g hg => ?_)
    ((GlobalTheory.GLIntegral.isOpen_glSub _ ho).preimage hp)
  have hv : ∀ (w : Plc L) (x : w.adicCompletion L), x ∈ w.adicCompletionIntegers L → x ∈ 𝒪[w.adicCompletion L] := fun w x hx => by
    haveI : (Valued.v : Valuation (w.adicCompletion L) (WithZero (Multiplicative ℤ))).Compatible :=
      Valuation.Compatible.ofValuation _
    rw [Valuation.mem_integer_iff, ← map_one (valuation _), ← Valuation.vle_iff_le, Valuation.vle_iff_le Valued.v, map_one]
    exact hx
  exact Subgroup.mem_iInf.2 fun w => (GlobalTheory.SplitFlip.mem_KO_iff _).2 ⟨fun i j => hv w _ (hg.1 i j w), fun i j => hv w _ (hg.2 i j w)⟩

theorem UpperTheory.unitaryAdelic_localComponents_continuous_levels_open :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ), (∀ w : Plc L, Continuous (cLoc (E := L) (n := n) w)) ∧ (∀ (w : Plc L) (b : ℕ), IsOpen (Kc (w.adicCompletion L) n b : Set (GLw n w))) ∧ ∀ᶠ k : finU (E := L) (n := n) in nhds 1, ∀ w : Plc L, cLoc w (k : UA L n) ∈ KO (w.adicCompletion L) (Fin n) := by
  intro L _ _ _ n
  refine ⟨fun w => GlobalTheory.DefU.Inert.continuous_cLoc w, fun w b => nh_Kc_open b, ?_⟩
  have h := ((nh_open (L := L) (n := n)).preimage (continuous_subtype_val (p := fun x => x ∈ finU (E := L) (n := n)))).mem_nhds
    (x := (1 : finU (E := L) (n := n))) (one_mem (⨅ w : Plc L, (KO (w.adicCompletion L) (Fin n)).comap (cLoc w) : Subgroup (UA L n)))
  filter_upwards [h] with k hk w
  exact Subgroup.mem_iInf.1 hk w
end

