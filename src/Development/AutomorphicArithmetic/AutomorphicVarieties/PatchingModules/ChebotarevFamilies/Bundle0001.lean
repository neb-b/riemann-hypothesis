module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.TaylorWilesObstructionBound
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0317

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ChebotarevFamilies.ChebOne
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem UpperTheory.V.Pa.chebOne_split {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
    [IsAlgClosure L Ω] {w : Plc L} {B : ValuationSubring Ω} (hB : IsPlaceOver B w)
    (hp : (Ideal.absNorm w.asIdeal).Prime) (x : 𝓞 L)
    (hx : IsCMField.ringOfIntegersComplexConj L x - x ∉ w.asIdeal) :
    Dec (F := Lp L) B ≤ (resP L Ω).range := by
  intro σ hσ
  let ρ : L ≃ₐ[Lp L] L := σ.restrictNormal L
  have hρ : ∀ a : L, algebraMap L Ω (ρ a) = σ (algebraMap L Ω a) := fun a =>
    σ.restrictNormal_commutes L a
  have h2 : ρ = 1 ∨ ρ = IsCMField.complexConj L := by
    have hm : ρ ∈ Submonoid.powers (IsCMField.complexConj L) := by
      rw [mem_powers_iff_mem_zpowers, IsCMField.zpowers_complexConj_eq_top]
      trivial
    obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff _ _).mp hm
    rw [← hk, ← pow_mod_orderOf, IsCMField.orderOf_complexConj]
    rcases Nat.mod_two_eq_zero_or_one k with h | h <;> rw [h] <;> simp
  have key : ρ = 1 := by
    refine h2.resolve_right fun hc => ?_
    haveI : Fact (Ideal.absNorm w.asIdeal).Prime := ⟨hp⟩
    haveI : Nontrivial (𝓞 L ⧸ w.asIdeal) := Ideal.Quotient.nontrivial_iff.mpr w.isPrime.ne_top
    have hQ : Nat.card (𝓞 L ⧸ w.asIdeal) = Ideal.absNorm w.asIdeal := by
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    obtain ⟨n, hn⟩ := (AddSubmonoid.mem_multiples_iff _ _).mp
      (mem_multiples_of_prime_card hQ (one_ne_zero (α := 𝓞 L ⧸ w.asIdeal))
        (g' := Ideal.Quotient.mk w.asIdeal x))
    have hxn : x - (n : 𝓞 L) ∈ w.asIdeal :=
      Ideal.Quotient.eq.mp (by rw [map_natCast, ← hn, nsmul_one])
    have e1 : ((IsCMField.ringOfIntegersComplexConj L x : 𝓞 L) : L) = ρ (x : L) := by
      rw [hc]; rfl
    have hs : ∀ y : 𝓞 L, ((y - (n : 𝓞 L) : 𝓞 L) : L) = (y : L) - n := fun y => by simp
    have e : algebraMap L Ω ((IsCMField.ringOfIntegersComplexConj L x - (n : 𝓞 L) : 𝓞 L) : L) =
        σ (algebraMap L Ω ((x - (n : 𝓞 L) : 𝓞 L) : L)) := by
      rw [hs, hs, e1]
      simp only [map_sub, map_natCast, hρ]
    have hcn : IsCMField.ringOfIntegersComplexConj L x - (n : 𝓞 L) ∈ w.asIdeal := by
      refine (hB _).mp ?_
      rw [e, valuation_apply_lt_one_iff hσ]
      exact (hB _).mpr hxn
    apply hx
    have := w.asIdeal.sub_mem hcn hxn
    simpa using this
  refine ⟨AlgEquiv.ofRingEquiv (f := σ.toRingEquiv) (fun a => ?_), ?_⟩
  · show σ (algebraMap L Ω a) = algebraMap L Ω a
    rw [← hρ, key]
    rfl
  · ext y
    rfl

theorem UpperTheory.V.Pa.chebOne :
    ∀ (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (U : Subgroup (G L Ω)) (g : G L Ω) (A : Set (Plc (Lp L))), IsOpen (U : Set (G L Ω)) → A.Finite → ∃ (v : Plc (Lp L)) (w : Plc L) (B : ValuationSubring Ω) (σ : G L Ω), v ∉ A ∧ IsPlaceOver B w ∧ IsPlaceOver B v ∧ Dec (F := Lp L) B ≤ (resP L Ω).range ∧ IsFrob (F := L) B (normV w) σ ∧ σ * g⁻¹ ∈ U := by
  intro L Ω _ _ _ _ _ _ U g A hU hA
  let φ : Plc L → Plc (Lp L) := fun w =>
    { asIdeal := w.asIdeal.comap (algebraMap (𝓞 (Lp L)) (𝓞 L))
      isPrime := by haveI := w.isPrime; infer_instance
      ne_bot := by
        obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot w.ne_bot
        exact Ideal.comap_ne_bot_of_integral_mem hy0 hy (Algebra.IsIntegral.isIntegral y) }
  have hφ : ∀ (w : Plc L) (B : ValuationSubring Ω), IsPlaceOver B w → IsPlaceOver B (φ w) := by
    intro w B hB y
    show _ ↔ algebraMap (𝓞 (Lp L)) (𝓞 L) y ∈ w.asIdeal
    rw [← hB]
    rfl
  obtain ⟨x0, hx0⟩ : ∃ x0 : 𝓞 L, IsCMField.ringOfIntegersComplexConj L x0 ≠ x0 := by
    by_contra! h
    apply IsCMField.complexConj_ne_one L
    ext y
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (𝓞 L) y
    have h' : ∀ a : 𝓞 L, IsCMField.complexConj L (algebraMap (𝓞 L) L a) = algebraMap (𝓞 L) L a :=
      fun a => by
        rw [show algebraMap (𝓞 L) L a = (a : L) from rfl,
          ← IsCMField.coe_ringOfIntegersComplexConj, h a]
    rw [map_div₀, h', h', AlgEquiv.one_apply]
  set d := IsCMField.ringOfIntegersComplexConj L x0 - x0 with hd_def
  have hd : d ≠ 0 := sub_ne_zero.mpr hx0
  have hfin : ∀ y : 𝓞 L, y ≠ 0 → {w : Plc L | y ∈ w.asIdeal}.Finite := fun y hy => by
    have := Ideal.finite_factors (I := Ideal.span {y})
      (by rw [Ne, Submodule.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hy)
    simpa [Ideal.dvd_span_singleton] using this
  have hfib : ∀ v : Plc (Lp L), {w : Plc L | φ w = v}.Finite := by
    intro v
    obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
    refine (hfin (algebraMap (𝓞 (Lp L)) (𝓞 L) a) ?_).subset ?_
    · intro h0
      apply ha0
      exact FaithfulSMul.algebraMap_injective _ _ (h0.trans (map_zero _).symm)
    · intro w hw
      have hw' : φ w = v := hw
      have : a ∈ (φ w).asIdeal := by rw [hw']; exact ha
      exact this
  let S : Set (Plc L) := {w | d ∈ w.asIdeal} ∪ ⋃ v ∈ A, {w | φ w = v}
  have hS : S.Finite := (hfin d hd).union (hA.biUnion fun v _ => hfib v)
  have hden := GlobalTheory.Published.ChebotarevDegreeOne.dense (Ω := Ω) GlobalTheory.Published.chebotarevDegreeOne' hS
  have hO : IsOpen ((fun τ : G L Ω => τ * g⁻¹) ⁻¹' (U : Set (G L Ω))) :=
    hU.preimage (continuous_mul_const _)
  obtain ⟨σ, hσU, w, hwS, hin, B, hB, hF⟩ :=
    hden.inter_open_nonempty _ hO ⟨g, by simp [U.one_mem]⟩
  have hp : (Ideal.absNorm w.asIdeal).Prime :=
    ((GlobalTheory.absNorm_prime_iff_inertiaDeg_eq_one_and_finite_ramified L).1 w).mpr hin
  refine ⟨φ w, w, B, σ, ?_, hB, hφ w B hB, UpperTheory.V.Pa.chebOne_split hB hp x0 ?_, hF, hσU⟩
  · intro hv
    exact hwS (Or.inr (Set.mem_biUnion hv rfl))
  · intro h
    exact hwS (Or.inl h)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ChebotarevFamilies.FrSNormal
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

namespace UpperTheory.V.Pa.FrattiniSubgroup

private theorem exists_hom (l : ℕ) [hl : Fact l.Prime] (Q : Type) [Group Q] [Finite Q] [Nontrivial Q]
    (hQ : IsPGroup l Q) : ∃ φ : Q →* Multiplicative (ZMod l), φ.ker ≠ ⊤ := by
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hQ
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero, Nat.card_eq_one_iff_unique] at hk
    exact not_nontrivial_iff_subsingleton.mpr hk.1 ‹_›
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime l (n := k - 1)
    (hk ▸ pow_dvd_pow l (Nat.sub_le k 1))
  have hidx : K.index = l := by
    have h := K.card_mul_index
    rw [hK, hk] at h
    have e : l ^ k = l ^ (k - 1) * l := by
      rw [← pow_succ, Nat.sub_add_cancel (Nat.pos_of_ne_zero hk0)]
    rw [e] at h
    exact Nat.eq_of_mul_eq_mul_left (pow_pos hl.out.pos _) h
  haveI : K.Normal := Subgroup.normal_of_index_eq_minFac_card
    (by rw [hidx, hk, Nat.Prime.pow_minFac hl.out hk0])
  have hcard : Nat.card (Q ⧸ K) = l := by rw [← Subgroup.index_eq_card, hidx]
  let e := mulEquivOfPrimeCardEq hcard (G' := Multiplicative (ZMod l)) (by simp)
  refine ⟨e.toMonoidHom.comp (QuotientGroup.mk' K), fun htop => ?_⟩
  have hKtop : K = ⊤ := by
    rw [eq_top_iff]
    intro q _
    have hq : q ∈ (e.toMonoidHom.comp (QuotientGroup.mk' K)).ker := htop ▸ Subgroup.mem_top q
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hq
    exact hq
  rw [hKtop, Subgroup.index_top] at hidx
  exact hl.out.one_lt.ne hidx

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]

private def frS (l : ℕ) (K : Subgroup Γ) : Subgroup Γ :=
  (⨅ φ : {φ : K →* Multiplicative (ZMod l) // IsOpen (φ.ker : Set K)}, φ.1.ker).map K.subtype

private theorem frS_normal (l : ℕ) (K : Subgroup Γ) [hK : K.Normal] : (frS l K).Normal := by
  constructor
  intro x hx g
  obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hx
  let c : K →* K := (MulAut.conjNormal g).toMonoidHom
  have hc : ∀ y : K, (c y : Γ) = g * y * g⁻¹ := fun y => MulAut.conjNormal_apply g y
  have hcc : Continuous c := by
    have h1 : Continuous fun y : K => g * (y : Γ) * g⁻¹ :=
      (continuous_const.mul continuous_subtype_val).mul continuous_const
    have h2 := h1.subtype_mk (fun y => hK.conj_mem y y.2 g)
    convert h2 using 1
    funext y
    exact Subtype.ext (hc y)
  refine Subgroup.mem_map.mpr ⟨c k, ?_, hc k⟩
  rw [Subgroup.mem_iInf] at hk ⊢
  intro ψ
  have hφ : IsOpen ((ψ.1.comp c).ker : Set K) := by
    show IsOpen (c ⁻¹' (ψ.1.ker : Set K))
    exact ψ.2.preimage hcc
  exact hk ⟨ψ.1.comp c, hφ⟩

private theorem frS_open (l : ℕ) (h : PhiCond Γ l) (K : Subgroup Γ) (hK : IsOpen (K : Set Γ)) :
    IsOpen (frS l K : Set Γ) := by
  haveI := h K hK
  unfold frS
  rw [Subgroup.coe_map, Subgroup.coe_iInf]
  exact hK.isOpenMap_subtype_val _ (isOpen_iInter_of_finite fun φ => φ.2)

private def fr (l : ℕ) (h : PhiCond Γ l) (K : OpenNormalSubgroup Γ) : OpenNormalSubgroup Γ where
  toSubgroup := frS l K.toSubgroup
  isOpen' := frS_open l h _ K.isOpen
  isNormal' := frS_normal l _

private theorem fr_le (l : ℕ) (h : PhiCond Γ l) (K : OpenNormalSubgroup Γ) :
    (fr l h K).toSubgroup ≤ K.toSubgroup := Subgroup.map_subtype_le _

private theorem fr_lt (l : ℕ) [Fact l.Prime] [CompactSpace Γ] (h : PhiCond Γ l) (K V : OpenNormalSubgroup Γ)
    (hp : ∀ k ∈ K.toSubgroup, ∃ e : ℕ, k ^ l ^ e ∈ V.toSubgroup) (hn : ¬ K.toSubgroup ≤ V.toSubgroup) :
    (fr l h K).toSubgroup.map (QuotientGroup.mk' V.toSubgroup) <
      K.toSubgroup.map (QuotientGroup.mk' V.toSubgroup) := by
  let π := (QuotientGroup.mk' V.toSubgroup).subgroupMap K.toSubgroup
  haveI : Finite (Γ ⧸ V.toSubgroup) := (inferInstance : Finite (Γ ⧸ (V.toOpenSubgroup : Subgroup Γ)))
  have hπk : ∀ k : K.toSubgroup, ((π k : K.toSubgroup.map (QuotientGroup.mk' V.toSubgroup)) :
      Γ ⧸ V.toSubgroup) = QuotientGroup.mk' V.toSubgroup k :=
    fun k => MonoidHom.subgroupMap_apply_coe _ _ k
  haveI : Nontrivial (K.toSubgroup.map (QuotientGroup.mk' V.toSubgroup)) := by
    obtain ⟨k, hkK, hkV⟩ := Set.not_subset.mp hn
    refine ⟨⟨π ⟨k, hkK⟩, 1, fun h => hkV ?_⟩⟩
    have := congrArg Subtype.val h
    rw [hπk] at this
    exact (QuotientGroup.eq_one_iff k).mp this
  have hQ : IsPGroup l (K.toSubgroup.map (QuotientGroup.mk' V.toSubgroup)) := by
    intro q
    obtain ⟨k, rfl⟩ := MonoidHom.subgroupMap_surjective _ _ q
    obtain ⟨e, he⟩ := hp k k.2
    refine ⟨e, ?_⟩
    show (π k) ^ l ^ e = 1
    rw [← map_pow]
    apply Subtype.ext
    rw [hπk]
    exact (QuotientGroup.eq_one_iff _).mpr (by simpa using he)
  obtain ⟨φ, hφ⟩ := exists_hom l _ hQ
  let ψ : K.toSubgroup →* Multiplicative (ZMod l) := φ.comp π
  have hψopen : IsOpen (ψ.ker : Set K.toSubgroup) := by
    refine Subgroup.isOpen_mono (H₁ := V.toSubgroup.comap K.toSubgroup.subtype) ?_ ?_
    · intro y hy
      rw [MonoidHom.mem_ker]
      have : π y = 1 := by
        apply Subtype.ext
        rw [hπk]
        exact (QuotientGroup.eq_one_iff _).mpr hy
      show φ (π y) = 1
      rw [this, map_one]
    · exact V.toOpenSubgroup.isOpen.preimage continuous_subtype_val
  refine lt_of_le_of_ne (Subgroup.map_mono (fr_le l h K)) fun heq => hφ ?_
  rw [eq_top_iff]
  intro q _
  obtain ⟨k, rfl⟩ := MonoidHom.subgroupMap_surjective _ _ q
  have hk : QuotientGroup.mk' V.toSubgroup (k : Γ) ∈
      (fr l h K).toSubgroup.map (QuotientGroup.mk' V.toSubgroup) := by
    rw [heq]
    exact Subgroup.mem_map_of_mem _ k.2
  obtain ⟨f, hf, hfk⟩ := Subgroup.mem_map.mp hk
  obtain ⟨f', hf', rfl⟩ := Subgroup.mem_map.mp hf
  have hf'ψ : f' ∈ ψ.ker := (Subgroup.mem_iInf.mp hf') ⟨ψ, hψopen⟩
  have hπeq : π k = π f' := by
    apply Subtype.ext
    rw [hπk, hπk]
    exact hfk.symm
  rw [MonoidHom.mem_ker] at hf'ψ ⊢
  show φ (π k) = 1
  rw [hπeq]
  exact hf'ψ

private theorem pow_mem (l : ℕ) [CompactSpace Γ] (H : Subgroup Γ) (V : OpenNormalSubgroup Γ)
    (hV : PL l H ≤ V.toSubgroup) : ∀ k ∈ H, ∃ e : ℕ, k ^ l ^ e ∈ V.toSubgroup := by
  intro k hk
  let ι := {U : OpenNormalSubgroup Γ // ∀ h ∈ H, ∃ e : ℕ, h ^ l ^ e ∈ U.toSubgroup}
  haveI : Nonempty ι := ⟨⟨{ toSubgroup := ⊤, isOpen' := isOpen_univ, isNormal' := inferInstance },
    fun h _ => ⟨0, Subgroup.mem_top _⟩⟩⟩
  let t : ι → Set Γ := fun i => (i.1.toSubgroup : Set Γ)
  have hdir : Directed (· ⊇ ·) t := by
    intro i j
    have hopen : IsOpen ((i.1.toSubgroup ⊓ j.1.toSubgroup : Subgroup Γ) : Set Γ) := by
      rw [Subgroup.coe_inf]
      exact i.1.toOpenSubgroup.isOpen.inter j.1.toOpenSubgroup.isOpen
    let U : OpenNormalSubgroup Γ :=
      { toSubgroup := i.1.toSubgroup ⊓ j.1.toSubgroup, isOpen' := hopen, isNormal' := inferInstance }
    have hU : ∀ h ∈ H, ∃ e : ℕ, h ^ l ^ e ∈ U.toSubgroup := by
      intro h hh
      obtain ⟨e1, h1⟩ := i.2 h hh
      obtain ⟨e2, h2⟩ := j.2 h hh
      refine ⟨e1 + e2, Subgroup.mem_inf.mpr ⟨?_, ?_⟩⟩
      · rw [pow_add, pow_mul]
        exact Subgroup.pow_mem _ h1 _
      · rw [pow_add, mul_comm, pow_mul]
        exact Subgroup.pow_mem _ h2 _
    exact ⟨⟨U, hU⟩, fun x hx => (Subgroup.mem_inf.mp hx).1, fun x hx => (Subgroup.mem_inf.mp hx).2⟩
  have hclosed : ∀ i : ι, IsClosed (t i) := fun i => i.1.toOpenSubgroup.isClosed
  have hVc : IsCompact ((V.toSubgroup : Set Γ)ᶜ) :=
    V.toOpenSubgroup.isOpen.isClosed_compl.isCompact
  have hempty : (V.toSubgroup : Set Γ)ᶜ ∩ ⋂ i : ι, t i = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro x ⟨hxV, hx⟩
    apply hxV
    apply hV
    simp only [UpperTheory.V.Pa.PL, Subgroup.mem_iInf]
    intro U hU
    exact Set.mem_iInter.mp hx ⟨U, hU⟩
  obtain ⟨i, hi⟩ := (hVc.elim_directed_family_closed t hclosed (Set.disjoint_iff_inter_eq_empty.2 hempty) hdir).imp (fun _ => Disjoint.inter_eq)
  obtain ⟨e, he⟩ := i.2 k hk
  refine ⟨e, ?_⟩
  by_contra hne
  have hmem : k ^ l ^ e ∈ (V.toSubgroup : Set Γ)ᶜ ∩ t i := ⟨hne, he⟩
  rw [hi] at hmem
  exact hmem

end UpperTheory.V.Pa.FrattiniSubgroup

open UpperTheory.V.Pa.FrattiniSubgroup in
theorem UpperTheory.V.Pa.frat :
    ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ] (H : OpenNormalSubgroup Γ), PhiCond Γ l → ∃ W : ℕ → OpenNormalSubgroup Γ, (∀ N, (W N).toSubgroup ≤ H.toSubgroup) ∧ ∀ V : OpenNormalSubgroup Γ, PL l H.toSubgroup ≤ V.toSubgroup → ∀ᶠ N in atTop, (W N).toSubgroup ≤ V.toSubgroup := by
  intro l _ Γ _ _ _ _ _ H hΦ
  let W : ℕ → OpenNormalSubgroup Γ := fun N =>
    Nat.rec (motive := fun _ => OpenNormalSubgroup Γ) H (fun _ K => fr l hΦ K) N
  have hWs : ∀ N, W (N + 1) = fr l hΦ (W N) := fun N => rfl
  have hanti : ∀ N, (W (N + 1)).toSubgroup ≤ (W N).toSubgroup := fun N => by
    rw [hWs]
    exact fr_le l hΦ (W N)
  have hmono : Antitone fun N => (W N).toSubgroup := antitone_nat_of_succ_le hanti
  refine ⟨W, fun N => hmono (Nat.zero_le N), fun V hV => ?_⟩
  have hpow := pow_mem l H.toSubgroup V hV
  haveI : Finite (Γ ⧸ V.toSubgroup) :=
    (inferInstance : Finite (Γ ⧸ (V.toOpenSubgroup : Subgroup Γ)))
  obtain ⟨m, ⟨N, rfl⟩, hmin⟩ :=
    (wellFounded_lt : WellFounded (α := Subgroup (Γ ⧸ V.toSubgroup)) (· < ·)).has_min
      (Set.range fun N => (W N).toSubgroup.map (QuotientGroup.mk' V.toSubgroup)) ⟨_, ⟨0, rfl⟩⟩
  have hN : (W N).toSubgroup ≤ V.toSubgroup := by
    by_contra hn
    refine hmin _ ⟨N + 1, rfl⟩ ?_
    show (W (N + 1)).toSubgroup.map (QuotientGroup.mk' V.toSubgroup) <
      (W N).toSubgroup.map (QuotientGroup.mk' V.toSubgroup)
    rw [hWs]
    exact fr_lt l hΦ (W N) V (fun k hk => hpow k (hmono (Nat.zero_le N) hk)) hn
  exact Filter.eventually_atTop.mpr ⟨N, fun M hM => (hmono hM).trans hN⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ChebotarevFamilies.HomBound
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem closure_normal_frattini_le_kernel (l : ℕ) {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
    (H : Subgroup Γ) [hN : H.Normal] (hH : IsOpen (H : Set Γ)) (S : Set Γ) (χ : H →* Multiplicative (ZMod l))
    (hχ : IsOpen (χ.ker : Set H))
    (hS : ∀ t ∈ S, ∀ g : Γ, g * t * g⁻¹ ∈ χ.ker.map H.subtype) :
    (Subgroup.normalClosure S ⊔ PL l H).topologicalClosure ≤ χ.ker.map H.subtype := by
  have hl : ∀ z : Multiplicative (ZMod l), z ^ l = 1 := by
    intro z
    apply Multiplicative.toAdd.injective
    simp [toAdd_pow]
  have hKo : IsOpen ((χ.ker.map H.subtype : Subgroup Γ) : Set Γ) := by
    rw [Subgroup.coe_map]
    exact hH.isOpenMap_subtype_val _ hχ
  refine Subgroup.topologicalClosure_minimal _ ?_ (Subgroup.isClosed_of_isOpen _ hKo)
  refine sup_le ?_ ?_
  · rw [Subgroup.normalClosure, Subgroup.closure_le]
    intro x hx
    obtain ⟨a, ha, hc⟩ := Group.mem_conjugatesOfSet_iff.1 hx
    obtain ⟨c, rfl⟩ := isConj_iff.1 hc
    exact hS a ha c
  · let K : OpenSubgroup Γ := ⟨χ.ker.map H.subtype, hKo⟩
    have : Finite (Γ ⧸ K.toSubgroup) := Subgroup.quotient_finite_of_isOpen _ hKo
    have : Subgroup.FiniteIndex K.toSubgroup := Subgroup.finiteIndex_of_finite_quotient
    let U : OpenNormalSubgroup Γ :=
      { toSubgroup := Subgroup.normalCore K.toSubgroup
        isOpen' := Subgroup.isOpen_of_isClosed_of_finiteIndex _
          (K.toSubgroup.normalCore_isClosed K.isClosed) }
    have hU : ∀ h ∈ H, ∃ e, h ^ l ^ e ∈ U := by
      intro h hh
      refine ⟨1, ?_⟩
      intro b
      have hb : b * h * b⁻¹ ∈ H := hN.conj_mem h hh b
      refine ⟨⟨b * h * b⁻¹, hb⟩ ^ l, MonoidHom.mem_ker.2 (by rw [map_pow, hl]), ?_⟩
      simp [conj_pow]
    unfold PL
    exact iInf_le_of_le U (iInf_le_of_le hU (Subgroup.normalCore_le K.toSubgroup))

private theorem twisted_kernel_forms_nonvanishing (l : ℕ) {Γ' Γ : Type} [Group Γ'] [TopologicalSpace Γ'] [IsTopologicalGroup Γ'] [CompactSpace Γ']
    [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [T2Space Γ] (p : Γ' →* Γ) (hp : Continuous p)
    (hs : Function.Surjective p) (H : Subgroup Γ) (hH : IsOpen (H : Set Γ))
    (χ : H.comap p →* Multiplicative (ZMod l)) (hχ : IsOpen (χ.ker : Set (H.comap p)))
    (hk : p.ker ≤ χ.ker.map (H.comap p).subtype) :
    ∃ ψ : HomL l H, ∀ x, ψ.1 (p.subgroupComap H x) = χ x := by
  set q := p.subgroupComap H with hqdef
  have hq : Function.Surjective q := by
    rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := hs y
    exact ⟨⟨x, hy⟩, rfl⟩
  have hker : q.ker ≤ χ.ker := by
    intro x hx
    have h1 : p x.1 = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 hx)
    obtain ⟨y, hy, hyx⟩ := hk (MonoidHom.mem_ker.2 h1 : x.1 ∈ p.ker)
    have : y = x := Subtype.ext hyx
    exact this ▸ hy
  let φ : H →* Multiplicative (ZMod l) :=
    (q.liftOfRightInverse (Function.surjInv hq) (Function.rightInverse_surjInv hq)) ⟨χ, hker⟩
  have hφ : ∀ x, φ (q x) = χ x := fun x =>
    q.liftOfRightInverse_comp_apply _ _ ⟨χ, hker⟩ x
  have hcont : Continuous q := (hp.comp continuous_subtype_val).subtype_mk _
  have hNc : IsClosed ((H.comap p : Subgroup Γ') : Set Γ') :=
    (Subgroup.isClosed_of_isOpen H hH).preimage hp
  haveI : CompactSpace (H.comap p) := isCompact_iff_compactSpace.1 hNc.isCompact
  have hc : IsClosed ((χ.ker : Set (H.comap p))ᶜ) := hχ.isClosed_compl
  have himg : IsClosed (q '' (χ.ker : Set (H.comap p))ᶜ) := (hc.isCompact.image hcont).isClosed
  have hopen : IsOpen (φ.ker : Set H) := by
    convert himg.isOpen_compl using 1
    ext y
    obtain ⟨x, rfl⟩ := hq y
    simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_compl_iff, Set.mem_image, not_exists, not_and]
    constructor
    · intro h x' hx' hxx
      apply hx'
      rw [← hφ x', hxx, h]
    · intro h
      by_contra hne
      exact h x (by rw [← hφ]; exact hne) rfl
  exact ⟨⟨φ, hopen⟩, hφ⟩

theorem UpperTheory.V.Pa.homBound :
    ∀ (l : ℕ) [Fact l.Prime] (Γ' : Type) [Group Γ'] [TopologicalSpace Γ'] [IsTopologicalGroup Γ'] [CompactSpace Γ'] [TotallyDisconnectedSpace Γ'] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ] (p : Γ' →* Γ) (H : OpenNormalSubgroup Γ) (q : ℕ) (ta : Fin q → Γ'), Continuous p → Function.Surjective p → (∀ j, p (ta j) = 1) → p.ker ≤ (Subgroup.normalClosure (Set.range ta) ⊔ PL l (H.toSubgroup.comap p)).topologicalClosure → Finite (HomL l H.toSubgroup) → Finite (HomL l (H.toSubgroup.comap p)) ∧ Nat.card (HomL l (H.toSubgroup.comap p)) ≤ Nat.card (HomL l H.toSubgroup) * l ^ (q * H.toSubgroup.index) := by
  intro l _ Γ' _ _ _ _ _ Γ _ _ _ _ _ p H q ta hp hs hta hker hfin
  set N : Subgroup Γ' := H.toSubgroup.comap p with hN
  haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  have hNo : IsOpen (N : Set Γ') := H.isOpen.preimage hp
  haveI : Finite (Γ' ⧸ N) := Subgroup.quotient_finite_of_isOpen _ hNo
  have hHn : H.toSubgroup.Normal := inferInstance
  have hmem : ∀ (g : Γ') (j : Fin q), g * ta j * g⁻¹ ∈ N := by
    intro g j
    show p (g * ta j * g⁻¹) ∈ H.toSubgroup
    simp [hta]
  let f : HomL l N → (Fin q × (Γ' ⧸ N) → Multiplicative (ZMod l)) :=
    fun χ jc => χ.1 ⟨jc.2.out * ta jc.1 * jc.2.out⁻¹, hmem _ _⟩
  haveI : Nonempty (HomL l N) := ⟨⟨1, by simp⟩⟩
  let g : (Fin q × (Γ' ⧸ N) → Multiplicative (ZMod l)) → HomL l N := Function.invFun f
  have hg : ∀ χ, f (g (f χ)) = f χ := fun χ => Function.invFun_eq ⟨χ, rfl⟩
  have key : ∀ χ : HomL l N, ∃ ψ : HomL l H.toSubgroup,
      ∀ x, ψ.1 (p.subgroupComap H.toSubgroup x) = (χ.1 * (g (f χ)).1⁻¹) x := by
    intro χ
    have hopenδ : IsOpen (((χ.1 * (g (f χ)).1⁻¹).ker : Subgroup N) : Set N) := by
      refine Subgroup.isOpen_mono (H₁ := χ.1.ker ⊓ (g (f χ)).1.ker) ?_ ?_
      · intro x hx
        simp only [Subgroup.mem_inf, MonoidHom.mem_ker] at hx
        simp [MonoidHom.mem_ker, hx.1, hx.2]
      · exact χ.2.inter (g (f χ)).2
    have hS : ∀ t ∈ Set.range ta, ∀ g' : Γ',
        g' * t * g'⁻¹ ∈ (χ.1 * (g (f χ)).1⁻¹).ker.map N.subtype := by
      rintro t ⟨j, rfl⟩ g'
      obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul N g'
      set c : Γ' ⧸ N := (QuotientGroup.mk g' : Γ' ⧸ N)
      have hb : c.out * (h : Γ')⁻¹ * c.out⁻¹ ∈ N := by
        show p (c.out * (h : Γ')⁻¹ * c.out⁻¹) ∈ H.toSubgroup
        rw [map_mul, map_mul, map_inv, map_inv]
        exact hHn.conj_mem _ (H.toSubgroup.inv_mem h.2) _
      have ha := congrFun (hg χ) (j, c)
      refine ⟨⟨c.out * (h : Γ')⁻¹ * c.out⁻¹, hb⟩ * ⟨c.out * ta j * c.out⁻¹, hmem _ _⟩ *
        ⟨c.out * (h : Γ')⁻¹ * c.out⁻¹, hb⟩⁻¹, ?_, ?_⟩
      · rw [SetLike.mem_coe, MonoidHom.mem_ker, map_mul, map_mul, map_inv]
        have : (χ.1 * (g (f χ)).1⁻¹) ⟨c.out * ta j * c.out⁻¹, hmem _ _⟩ = 1 := by
          simp only [MonoidHom.mul_apply, MonoidHom.inv_apply]
          exact mul_inv_eq_one.2 ha.symm
        rw [this, mul_one, mul_inv_cancel]
      · simp only [Subgroup.subtype_apply, Subgroup.coe_mul, Subgroup.coe_inv]
        rw [hh]
        group
    have hk' : p.ker ≤ (χ.1 * (g (f χ)).1⁻¹).ker.map N.subtype :=
      hker.trans (closure_normal_frattini_le_kernel l N hNo (Set.range ta) _ hopenδ hS)
    exact twisted_kernel_forms_nonvanishing l p hp hs H.toSubgroup H.isOpen _ hopenδ hk'
  choose D hD using key
  let F : HomL l N → (Fin q × (Γ' ⧸ N) → Multiplicative (ZMod l)) × HomL l H.toSubgroup :=
    fun χ => (f χ, D χ)
  have hF : Function.Injective F := by
    intro χ χ' h
    simp only [F, Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    have e : ∀ x, (χ.1 * (g (f χ)).1⁻¹) x = (χ'.1 * (g (f χ')).1⁻¹) x := by
      intro x
      rw [← hD, ← hD, h2]
    rw [h1] at e
    apply Subtype.ext
    ext x
    have e' := e x
    rw [MonoidHom.mul_apply, MonoidHom.mul_apply] at e'
    exact mul_right_cancel (G := Multiplicative (ZMod l)) e'
  haveI : Finite (HomL l N) := Finite.of_injective F hF
  refine ⟨inferInstance, ?_⟩
  have hidx : Nat.card (Γ' ⧸ N) = H.toSubgroup.index :=
    Subgroup.index_comap_of_surjective _ hs
  have hZ : Nat.card (Multiplicative (ZMod l)) = l :=
    (Nat.card_congr Multiplicative.toAdd).trans (Nat.card_zmod l)
  calc Nat.card (HomL l N)
      ≤ Nat.card ((Fin q × (Γ' ⧸ N) → Multiplicative (ZMod l)) × HomL l H.toSubgroup) :=
        Nat.card_le_card_of_injective F hF
    _ = Nat.card (HomL l H.toSubgroup) * l ^ (q * H.toSubgroup.index) := by
        rw [Nat.card_prod, mul_comm, Nat.card_fun, Nat.card_prod, Nat.card_fin, hidx, hZ]
end

