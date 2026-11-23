module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.SplitLineAlt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1221
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalSatakeAlmostAll

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.HintTranslate
section
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.BCT Formalism.UG
open PositivityTheory.Rg.BcB.G8 (K2)
open scoped Classical

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm

section Generic

variable {G : Type} [Group G]

private theorem hint_of_rinv (K : Subgroup G) (u : G → ℂ) (hu : ∀ k ∈ K, ∀ x, u (x * k) = u x) :
    hint K u = ∑ᶠ q : G ⧸ K, u q.out := by
  have h : rStab u ⊓ K = K := inf_eq_right.2 fun k hk => hu k hk
  unfold hint
  rw [h, Subgroup.relIndex_self]
  simp

private theorem out_mk_eq (K : Subgroup G) (u : G → ℂ) (hu : ∀ k ∈ K, ∀ x, u (x * k) = u x) (x : G) :
    u ((x : G ⧸ K).out) = u x := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul K x
  rw [hh]
  exact hu h h.2 x

private theorem hint_translate (K : Subgroup G) (u : G → ℂ) (hu : ∀ k ∈ K, ∀ x, u (x * k) = u x) (k : G) :
    hint K (fun z => u (k * z)) = hint K u := by
  rw [hint_of_rinv K u hu, hint_of_rinv K _ fun c hc x => by
    show u (k * (x * c)) = u (k * x)
    rw [← mul_assoc]
    exact hu c hc _]
  calc ∑ᶠ q : G ⧸ K, u (k * q.out)
      = ∑ᶠ q : G ⧸ K, (fun q' : G ⧸ K => u q'.out) ((MulAction.toPerm k : Equiv.Perm (G ⧸ K)) q) := by
        refine finsum_congr fun q => ?_
        have hq : (MulAction.toPerm k : Equiv.Perm (G ⧸ K)) q = ((k * q.out : G) : G ⧸ K) := by
          conv_lhs => rw [← QuotientGroup.out_eq' q]
          rfl
        show _ = u (((MulAction.toPerm k : Equiv.Perm (G ⧸ K)) q).out)
        rw [hq, out_mk_eq K u hu]
    _ = ∑ᶠ q : G ⧸ K, u q.out := finsum_comp_equiv (f := fun q' : G ⧸ K => u q'.out) (MulAction.toPerm k : Equiv.Perm (G ⧸ K))

variable [TopologicalSpace G] [IsTopologicalGroup G]

private theorem isHecke_conv (K : Subgroup G) {A B : G → ℂ} (hA : IsHecke K A) (hB : IsHecke K B) :
    IsHecke K fun y => hint K fun z => A z * B (z⁻¹ * y) := by
  refine ⟨?_, fun k hk x => ⟨?_, ?_⟩⟩
  · refine HasCompactSupport.of_support_subset_isCompact (hA.1.isCompact.mul hB.1.isCompact) fun y hy => ?_
    have hy' : hint K (fun z => A z * B (z⁻¹ * y)) ≠ 0 := hy
    obtain ⟨z, hz⟩ : ∃ z, A z * B (z⁻¹ * y) ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact hy' (by simp [hint, hc])
    exact Set.mem_mul.2 ⟨z, subset_tsupport _ (left_ne_zero_of_mul hz), z⁻¹ * y,
      subset_tsupport _ (right_ne_zero_of_mul hz), by group⟩
  · have hu : ∀ c ∈ K, ∀ z, (fun z => A z * B (z⁻¹ * x)) (z * c) = (fun z => A z * B (z⁻¹ * x)) z := by
      intro c hc z
      show A (z * c) * B ((z * c)⁻¹ * x) = A z * B (z⁻¹ * x)
      rw [(hA.2 c hc z).2, _root_.mul_inv_rev, mul_assoc, (hB.2 c⁻¹ (K.inv_mem hc) _).1]
    show hint K (fun z => A z * B (z⁻¹ * (k * x))) = hint K (fun z => A z * B (z⁻¹ * x))
    rw [← hint_translate K (fun z => A z * B (z⁻¹ * x)) hu k⁻¹]
    congr 1
    funext z
    show A z * B (z⁻¹ * (k * x)) = A (k⁻¹ * z) * B ((k⁻¹ * z)⁻¹ * x)
    rw [(hA.2 k⁻¹ (K.inv_mem hk) z).1]
    congr 2
    group
  · have h : (fun z => A z * B (z⁻¹ * (x * k))) = fun z => A z * B (z⁻¹ * x) := by
      funext z
      rw [← mul_assoc, (hB.2 k hk _).2]
    show hint K (fun z => A z * B (z⁻¹ * (x * k))) = hint K (fun z => A z * B (z⁻¹ * x))
    rw [h]

private theorem isHecke_ind (K : Subgroup G) (hK : IsCompact (K : Set G)) (S : Set G)
    (hl : ∀ k ∈ K, ∀ x ∈ S, k * x ∈ S) (hr : ∀ k ∈ K, ∀ x ∈ S, x * k ∈ S)
    (ht : ∀ x ∈ S, ∀ y ∈ S, ∃ a ∈ K, ∃ b ∈ K, y = a * x * b) :
    IsHecke K (S.indicator (1 : G → ℂ)) := by
  refine ⟨?_, fun k hk x => ⟨?_, ?_⟩⟩
  · rcases S.eq_empty_or_nonempty with rfl | ⟨d, hd⟩
    · exact HasCompactSupport.of_support_subset_isCompact isCompact_empty (by simp)
    · refine HasCompactSupport.of_support_subset_isCompact
        (IsCompact.mul (IsCompact.mul hK (isCompact_singleton (x := d))) hK) fun y hy => ?_
      have hyS : y ∈ S := by
        by_contra h
        exact hy (Set.indicator_of_notMem h _)
      obtain ⟨a, ha, b, hb, rfl⟩ := ht d hd y hyS
      exact Set.mul_mem_mul (Set.mul_mem_mul ha rfl) hb
  · have : k * x ∈ S ↔ x ∈ S := ⟨fun h => by simpa using hl k⁻¹ (K.inv_mem hk) _ h, hl k hk x⟩
    by_cases hx : x ∈ S
    · simp [hx, this]
    · simp [hx, this]
  · have : x * k ∈ S ↔ x ∈ S := ⟨fun h => by simpa using hr k⁻¹ (K.inv_mem hk) _ h, hr k hk x⟩
    by_cases hx : x ∈ S
    · simp [hx, this]
    · simp [hx, this]

private theorem isHecke_fn {ι : Type} (K : Subgroup G) (hK : IsCompact (K : Set G)) (g : ι → G → ℂ)
    (hg : ∀ i, IsHecke K (g i)) (e : Ex ι) : IsHecke K (e.fn K g) := by
  induction e with
  | one =>
    exact isHecke_ind K hK _ (fun k hk x hx => K.mul_mem hk hx) (fun k hk x hx => K.mul_mem hx hk)
      fun x hx y hy => ⟨y * x⁻¹, K.mul_mem hy (K.inv_mem hx), 1, K.one_mem, by group⟩
  | gen i => exact hg i
  | smul c a ih =>
    refine ⟨HasCompactSupport.of_support_subset_isCompact ih.1.isCompact fun y hy => ?_, fun k hk x => ?_⟩
    · exact subset_tsupport _ (right_ne_zero_of_mul hy)
    · show c * a.fn K g (k * x) = c * a.fn K g x ∧ c * a.fn K g (x * k) = c * a.fn K g x
      rw [(ih.2 k hk x).1, (ih.2 k hk x).2]
      exact ⟨rfl, rfl⟩
  | add a b iha ihb =>
    refine ⟨iha.1.add ihb.1, fun k hk x => ?_⟩
    show a.fn K g (k * x) + b.fn K g (k * x) = a.fn K g x + b.fn K g x ∧
      a.fn K g (x * k) + b.fn K g (x * k) = a.fn K g x + b.fn K g x
    rw [(iha.2 k hk x).1, (iha.2 k hk x).2, (ihb.2 k hk x).1, (ihb.2 k hk x).2]
    exact ⟨rfl, rfl⟩
  | mul a b iha ihb => exact isHecke_conv K iha ihb

end Generic

private theorem isHecke_pair {G H : Type} [Group G] [Group H] [TopologicalSpace G] [TopologicalSpace H]
    [IsTopologicalGroup G] [IsTopologicalGroup H] (K₁ : Subgroup G) (K₂ : Subgroup H) {f : G → ℂ} {g : H → ℂ}
    (hf : IsHecke K₁ f) (hg : IsHecke K₂ g) : IsHecke (K₁.prod K₂) fun y : G × H => f y.1 * g y.2 := by
  refine ⟨HasCompactSupport.of_support_subset_isCompact (hf.1.isCompact.prod hg.1.isCompact) fun y hy =>
    ⟨subset_tsupport _ (left_ne_zero_of_mul hy), subset_tsupport _ (right_ne_zero_of_mul hy)⟩, fun k hk x => ?_⟩
  obtain ⟨h1, h2⟩ := Subgroup.mem_prod.1 hk
  show f (k.1 * x.1) * g (k.2 * x.2) = _ ∧ f (x.1 * k.1) * g (x.2 * k.2) = _
  rw [(hf.2 _ h1 _).1, (hf.2 _ h1 _).2, (hg.2 _ h2 _).1, (hg.2 _ h2 _).2]
  exact ⟨rfl, rfl⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

private theorem isHecke_Tj (n : ℕ) (w : Pl E) (ϖ : w.adicCompletion E) (j : ℕ) :
    IsHecke (GlobalTheory.LFun.KGL w (n := n)) (Tj ℂ n (Ov E w) ϖ j) := by
  have hKe : GlobalTheory.LFun.KGL w (n := n) = GLint (Fin n) (Ov E w) := rfl
  have hc := (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL (E := E) w n).2
  unfold Tj
  refine isHecke_ind _ hc _ ?_ ?_ ?_
  · rintro k hk x ⟨a, ha, b, hb, hx⟩
    refine ⟨k * a, (GLint (Fin n) (Ov E w)).mul_mem (hKe ▸ hk) ha, b, hb, ?_⟩
    rw [Units.val_mul, Units.val_mul, hx]
    simp only [mul_assoc]
  · rintro k hk x ⟨a, ha, b, hb, hx⟩
    refine ⟨a, ha, b * k, (GLint (Fin n) (Ov E w)).mul_mem hb (hKe ▸ hk), ?_⟩
    rw [Units.val_mul, Units.val_mul, hx]
    simp only [mul_assoc]
  · rintro x ⟨a, ha, b, hb, hx⟩ y ⟨c, hc', d, hd, hy⟩
    refine ⟨c * a⁻¹, hKe ▸ (GLint (Fin n) (Ov E w)).mul_mem hc' ((GLint (Fin n) (Ov E w)).inv_mem ha),
      b⁻¹ * d, hKe ▸ (GLint (Fin n) (Ov E w)).mul_mem ((GLint (Fin n) (Ov E w)).inv_mem hb) hd, ?_⟩
    apply Units.ext
    have h1 : (a⁻¹).val * a.val = 1 := Units.inv_mul a
    have h2 : b.val * (b⁻¹).val = 1 := Units.mul_inv b
    simp only [Units.val_mul]
    rw [hx, hy]
    calc c.val * diagJ n ϖ j * d.val
        = c.val * 1 * diagJ n ϖ j * 1 * d.val := by simp
      _ = c.val * ((a⁻¹).val * a.val) * diagJ n ϖ j * (b.val * (b⁻¹).val) * d.val := by rw [h1, h2]
      _ = _ := by simp only [mul_assoc]

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm

open UpperTheory.V.Z.Tf.GlobalTraceComparison in
theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.exHecke2 :
    UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.ExHecke2 := by
  intro E _ _ _ a b w e
  exact UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.isHecke_fn (K2 a b w)
    ((GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w a).2.prod (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w b).2) _
    (fun p => UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.isHecke_pair _ _ (UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.isHecke_Tj a w _ _)
      (UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.isHecke_Tj b w _ _)) e
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.LevelFn
section
noncomputable section

open GlobalTheory.BCT GlobalTheory.PRep Matrix
open UpperTheory.V.Z.Tf.GlobalTraceComparison

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm

section Generic

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

private theorem rStab_ind (K' : Subgroup G) :
    rStab ((K' : Set G).indicator (1 : G → ℂ)) = K' := by
  classical
  ext k
  constructor
  · intro hk
    have h := hk 1
    simp only [one_mul] at h
    by_contra hn
    rw [Set.indicator_of_notMem (by simpa using hn), Set.indicator_of_mem (by simp [K'.one_mem])] at h
    simp at h
  · intro hk x
    by_cases hx : x ∈ K'
    · rw [Set.indicator_of_mem (show x * k ∈ (K' : Set G) from K'.mul_mem hx hk),
        Set.indicator_of_mem (show x ∈ (K' : Set G) from hx)]
      rfl
    · have hxk : x * k ∉ K' := fun h => hx (by simpa using K'.mul_mem h (K'.inv_mem hk))
      rw [Set.indicator_of_notMem (show x * k ∉ (K' : Set G) from hxk),
        Set.indicator_of_notMem (show x ∉ (K' : Set G) from hx)]

private theorem ind_inv (K' : Subgroup G) :
    (fun y : G => (K' : Set G).indicator (1 : G → ℂ) y⁻¹) = (K' : Set G).indicator (1 : G → ℂ) := by
  classical
  funext y
  by_cases hy : y ∈ K'
  · rw [Set.indicator_of_mem (show y⁻¹ ∈ (K' : Set G) from K'.inv_mem hy),
      Set.indicator_of_mem (show y ∈ (K' : Set G) from hy)]
    rfl
  · have : y⁻¹ ∉ K' := fun h => hy (by simpa using K'.inv_mem h)
    rw [Set.indicator_of_notMem (show y⁻¹ ∉ (K' : Set G) from this),
      Set.indicator_of_notMem (show y ∉ (K' : Set G) from hy)]

private theorem levOp_ind (ρ : Representation ℂ G V) (K K' : Subgroup G) (x : V) (hx : x ∈ fixed ρ K') :
    levOp ρ K K' ((K' : Set G).indicator (1 : G → ℂ)) LinearMap.id x = ((K'.relIndex K : ℕ) : ℂ)⁻¹ • x := by
  classical
  have hfx : ∀ h ∈ K', ρ h x = x := fun h hh => by simpa using hx ⟨h, hh⟩
  have hout : ∀ q : G ⧸ K', q.out ∈ K' ↔ q = (QuotientGroup.mk 1 : G ⧸ K') := by
    intro q
    constructor
    · intro h
      have h2 : ((q.out : G) : G ⧸ K') = QuotientGroup.mk 1 :=
        QuotientGroup.eq.2 (by simpa using K'.inv_mem h)
      rwa [QuotientGroup.out_eq'] at h2
    · rintro rfl
      have := QuotientGroup.mk_out_eq_mul K' (1 : G)
      obtain ⟨h, hh⟩ := this
      rw [hh]
      simpa using h.2
  unfold levOp
  rw [finsum_eq_single _ (QuotientGroup.mk 1 : G ⧸ K')]
  · rw [Set.indicator_of_mem (show (QuotientGroup.mk 1 : G ⧸ K').out ∈ (K' : Set G) from (hout _).2 rfl)]
    simp [hfx _ ((hout _).2 rfl)]
  · intro q hq
    rw [Set.indicator_of_notMem (show q.out ∉ (K' : Set G) from fun h => hq ((hout q).1 h))]
    simp

private theorem trc_ind_ne (ρ : Representation ℂ G V) (K K' : Subgroup G) (hle : K' ≤ K) (hi : K'.relIndex K ≠ 0)
    (hfd : FiniteDimensional ℂ (fixed ρ K')) (hne : fixed ρ K' ≠ ⊥) :
    trc ρ K ((K' : Set G).indicator (1 : G → ℂ)) ≠ 0 := by
  have hlev : K ⊓ rStab ((K' : Set G).indicator (1 : G → ℂ)) ⊓
      rStab (fun y : G => (K' : Set G).indicator (1 : G → ℂ) y⁻¹) = K' := by
    rw [ind_inv, rStab_ind, inf_assoc, inf_idem]
    exact inf_eq_right.2 hle
  unfold trc
  rw [hlev]
  have hc : ∀ v ∈ fixed ρ K', levOp ρ K K' ((K' : Set G).indicator (1 : G → ℂ)) LinearMap.id v ∈ fixed ρ K' := by
    intro v hv
    rw [levOp_ind ρ K K' v hv]
    exact Submodule.smul_mem _ _ hv
  have hr : (levOp ρ K K' ((K' : Set G).indicator (1 : G → ℂ)) LinearMap.id).restrict hc =
      ((K'.relIndex K : ℕ) : ℂ)⁻¹ • LinearMap.id := by
    ext v
    simp [LinearMap.restrict_apply, levOp_ind ρ K K' v v.2]
  unfold twTr
  rw [dite_eq_left hc, hr, map_smul, LinearMap.trace_id, smul_eq_mul]
  have hpos : Module.finrank ℂ (fixed ρ K') ≠ 0 := by
    intro h0
    exact hne (Submodule.finrank_eq_zero.1 h0)
  exact mul_ne_zero (inv_ne_zero (by exact_mod_cast hi)) (by exact_mod_cast hpos)

end Generic

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.levelFn :
    UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.LevelFn := by
  intro E _ _ _ n w τ
  obtain ⟨ho, hc⟩ := GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL (E := E) w n
  have hnt : Nontrivial τ.V := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    have hs : Subsingleton (Subrepresentation τ.ρ) :=
      ⟨fun a b => by
        apply Subrepresentation.toSubmodule_injective
        exact Subsingleton.elim _ _⟩
    haveI := τ.irred
    exact not_subsingleton (Subrepresentation τ.ρ) hs
  obtain ⟨v, hv⟩ := exists_ne (0 : τ.V)
  let U : Subgroup (GLw n w) :=
    { carrier := {g | τ.ρ g v = v}
      one_mem' := by simp
      mul_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq, map_mul, Module.End.mul_apply] at *
        rw [hb, ha]
      inv_mem' := by
        intro a ha
        simp only [Set.mem_setOf_eq] at *
        conv_lhs => rw [← ha]
        rw [← Module.End.mul_apply, ← map_mul]
        simp }
  have hU : IsOpen (U : Set (GLw n w)) := τ.smooth v
  let K' : Subgroup (GLw n w) := U ⊓ GlobalTheory.LFun.KGL w (n := n)
  have hKo : IsOpen (K' : Set (GLw n w)) := hU.inter ho
  have hKc : IsCompact (K' : Set (GLw n w)) := hc.inter_left (U.isClosed_of_isOpen hU)
  have hle : K' ≤ GlobalTheory.LFun.KGL w (n := n) := inf_le_right
  have hfd : FiniteDimensional ℂ (fixed τ.ρ K') := finiteDimensional_fixed_openSubgroup_GLw E n w τ K' hKo
  have hne : fixed τ.ρ K' ≠ ⊥ := by
    intro hb
    have hm : v ∈ fixed τ.ρ K' := fun h => by
      have h1 : τ.ρ h v = v := h.2.1
      simpa using h1
    rw [hb] at hm
    exact hv ((Submodule.mem_bot ℂ).1 hm)
  have hi : K'.relIndex (GlobalTheory.LFun.KGL w (n := n)) ≠ 0 := by
    haveI : CompactSpace (GlobalTheory.LFun.KGL w (n := n)) := isCompact_iff_compactSpace.1 hc
    haveI : Finite ((GlobalTheory.LFun.KGL w (n := n)) ⧸ K'.subgroupOf (GlobalTheory.LFun.KGL w (n := n))) :=
      Subgroup.quotient_finite_of_isOpen _ (hKo.preimage continuous_subtype_val)
    exact (Subgroup.finiteIndex_of_finite_quotient (H := K'.subgroupOf (GlobalTheory.LFun.KGL w (n := n)))).index_ne_zero
  refine ⟨(K' : Set (GLw n w)).indicator 1, ⟨K', hKo, hle, ?_, ?_⟩, UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.trc_ind_ne τ.ρ _ K' hle hi hfd hne⟩
  · exact HasCompactSupport.intro' hKc (K'.isClosed_of_isOpen hKo) fun x hx => Set.indicator_of_notMem hx _
  · classical
    intro k hk x
    have h1 : (k * x ∈ (K' : Set (GLw n w))) ↔ x ∈ (K' : Set (GLw n w)) := K'.mul_mem_cancel_left hk
    have h2 : (x * k ∈ (K' : Set (GLw n w))) ↔ x ∈ (K' : Set (GLw n w)) := K'.mul_mem_cancel_right hk
    show (K' : Set (GLw n w)).indicator 1 (k * x) = _ ∧ (K' : Set (GLw n w)).indicator 1 (x * k) = _
    rw [Set.indicator_apply, Set.indicator_apply, Set.indicator_apply]
    simp only [h1, h2, Pi.one_apply, and_self]
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.SplitLine
section
open NumberField IsDedekindDomain Matrix Formalism.L2.Host GlobalTheory.CuspRep
open Formalism.UG GlobalTheory.PRep GlobalTheory.LFun GlobalTheory.LGrp GlobalTheory.LFun.SatCompare

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm

section

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

private theorem eq_bot_or_top {ρ : Representation ℂ G V} (hi : ρ.IsIrreducible) (S : Submodule ℂ V)
    (hS : ∀ g, ∀ x ∈ S, ρ g x ∈ S) : S = ⊥ ∨ S = ⊤ := by
  let P : Subrepresentation ρ := ⟨S, fun g x hx => hS g x hx⟩
  exact (hi.eq_bot_or_eq_top P).imp (fun e => congrArg Subrepresentation.toSubmodule e)
    fun e => congrArg Subrepresentation.toSubmodule e

variable [TopologicalSpace G] [IsTopologicalGroup G]

private theorem rank_le [SecondCountableTopology G] {ρ : Representation ℂ G V} (hs : IsSmooth ρ)
    (hi : ρ.IsIrreducible) {v : V} (hv : v ≠ 0) : Module.rank ℂ V ≤ Cardinal.aleph0 := by
  rw [← rank_top]
  refine GlobalTheory.CompanionTheory.SatAe.rank_le_of_simple (⊤ : Submodule ℂ V) (fun g : G => ρ g)
    ((Submodule.ne_bot_iff _).2 ⟨v, trivial, hv⟩) (fun W _ hW => eq_bot_or_top hi W hW) fun x _ => ?_
  exact ⟨_, GlobalTheory.CompanionTheory.SatAe.countable_orbit ρ x (hs x), fun _ _ => trivial, fun g => Submodule.subset_span ⟨g, rfl⟩⟩

private theorem fixed_eq_span [SecondCountableTopology G] {ρ : Representation ℂ G V} {K : Subgroup G}
    (hs : IsSmooth ρ) (hi : ρ.IsIrreducible) (hc : IsCompact (K : Set G)) (hK : IsCommensurated K)
    (hcomm : ∀ f₁ ∈ Hecke ℂ K, ∀ f₂ ∈ Hecke ℂ K, conv K f₁ f₂ = conv K f₂ f₁)
    {v : V} (hv : v ∈ fixed ρ K) (hv0 : v ≠ 0) : fixed ρ K = Submodule.span ℂ {v} := by
  have hr := rank_le hs hi hv0
  have hb : GlobalTheory.CompanionTheory.SatAe.IsBiSimple ρ := fun S h1 _ => eq_bot_or_top hi S h1
  have hle : Submodule.span ℂ {v} ≤ fixed ρ K := (Submodule.span_singleton_le_iff_mem _ _).2 hv
  have hH : ∀ f ∈ Hecke ℂ K, ∀ x ∈ Submodule.span ℂ {v}, heckeVec ρ K f x ∈ Submodule.span ℂ {v} := by
    intro f hf x hx
    obtain ⟨c, hc'⟩ := GlobalTheory.CompanionTheory.SatAe.exists_scalar hs hc hK hcomm hb hr f hf
    rw [hc' x (hle hx)]
    exact Submodule.smul_mem _ _ hx
  have hB : ∀ b : Module.End ℂ V, (∀ g, b * ρ g = ρ g * b) → ∀ x ∈ Submodule.span ℂ {v},
      b x ∈ Submodule.span ℂ {v} := by
    intro b hbc x hx
    obtain ⟨c, hc'⟩ := GlobalTheory.CompanionTheory.SatAe.scalar_of_simple hr (Set.range fun g => ρ g)
      (fun W hW => eq_bot_or_top hi W fun g => hW _ ⟨g, rfl⟩) b (by
        rintro _ ⟨g, rfl⟩
        exact (hbc g).symm)
    rw [hc' x]
    exact Submodule.smul_mem _ _ hx
  refine ((GlobalTheory.CompanionTheory.SatAe.fixed_simple hs hc hK hb _ hle hH hB).resolve_left fun h => hv0 ?_).symm
  have : v ∈ Submodule.span ℂ {v} := Submodule.mem_span_singleton_self v
  rw [h] at this
  exact (Submodule.mem_bot ℂ).1 this

end

theorem splitLine : SplitLine := by
  intro E _ _ _ n w τ hne
  rcases τ with @⟨V, _, _, ρ, hs, hi⟩
  change fixed ρ (KGL w (n := n)) ≠ ⊥ at hne
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 hne
  have hc := (isOpen_isCompact_KGL w n).2
  have hK := Final.GLintComm E w n
  have hcomm := Final.HeckeCommGL E w n ℂ
  have hline := fixed_eq_span hs hi hc hK hcomm hv hv0
  refine ⟨?_, GlobalTheory.CompanionTheory.SatAe.exists_hasSatGL_of_scalar (fun h hh => ?_) hne⟩
  · change Module.finrank ℂ (fixed ρ (KGL w (n := n))) = 1
    rw [hline]
    exact finrank_span_singleton hv0
  · exact GlobalTheory.CompanionTheory.SatAe.exists_scalar hs hc hK hcomm (fun S h1 _ => eq_bot_or_top hi S h1)
      (rank_le hs hi hv0) h hh

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm
end

