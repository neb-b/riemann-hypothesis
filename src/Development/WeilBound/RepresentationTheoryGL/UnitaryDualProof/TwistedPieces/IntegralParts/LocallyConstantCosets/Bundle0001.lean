module

public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.IntegralParts.LocallyConstantCosets.PsiBiUnion
public import GroundTheory.AutomorphicForms.WhittakerDistribution

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.IntegralParts.LocallyConstantCosets.LcIndicator
section
noncomputable section

open Matrix GroundTheory.Automorphic.Whittaker GlobalTheory.SplitWeil
open scoped Pointwise

namespace PositivityTheory.RgUd.TP.Nil.Fib2

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Nil PositivityTheory.RgUd.TP.Nil.Fib1

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
  {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)}

theorem lc_indicator {X : Type*} [TopologicalSpace X] {S : Set X} (hS : IsClopen S) (c : ℂ) :
    IsLocallyConstant (S.indicator fun _ => c) := by
  intro s
  by_cases h1 : c ∈ s <;> by_cases h0 : (0 : ℂ) ∈ s
  · convert isOpen_univ using 1
    ext x; by_cases hx : x ∈ S <;> simp [Set.indicator, hx, h1, h0]
  · convert hS.isOpen using 1
    ext x; by_cases hx : x ∈ S <;> simp [Set.indicator, hx, h1, h0]
  · convert hS.isClosed.isOpen_compl using 1
    ext x; by_cases hx : x ∈ S <;> simp [Set.indicator, hx, h1, h0]
  · convert isOpen_empty using 1
    ext x; by_cases hx : x ∈ S <;> simp [Set.indicator, hx, h1, h0]

theorem psi_lift (hZ : CR Z) {A : Set (Matrix (Fin n) (Fin n) k)} (hAZ : A ⊆ Z) (hAc : IsCompact A)
    (hAo : ∀ a ∈ A, ∃ U : Set (Matrix (Fin n) (Fin n) k), IsOpen U ∧ a ∈ U ∧ U ∩ Z ⊆ A)
    {h : Sp k n → ℂ} (hh : h ∈ supportedIn (UU : Set (Sp k n))) :
    ∃ f ∈ supportedIn (UU : Set (Sp k n)), ∀ p ∈ OO Z, f p = psi Z A h p := by
  classical
  haveI : TotallyDisconnectedSpace k := totallyDisconnectedSpace_localField
  haveI : T2Space k := GlobalTheory.SplitWeil.t2Space k
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) k) := inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → k))
  haveI : TotallyDisconnectedSpace (Matrix (Fin n) (Fin n) k) :=
    inferInstanceAs (TotallyDisconnectedSpace (Fin n → Fin n → k))
  haveI : T2Space (Matrix (Fin n) (Fin n) k) := inferInstanceAs (T2Space (Fin n → Fin n → k))
  have hUU : IsOpen (UU : Set (Sp k n)) := isOpen_ne_fun continuous_snd continuous_const
  have hOU : OO Z ⊆ UU := fun p hp => hp.2
  have hhl : IsLocallyConstant h := (GroundTheory.Automorphic.mem_locallyConstantCompactSupport.1 hh.1).1
  have hhc : HasCompactSupport h := (GroundTheory.Automorphic.mem_locallyConstantCompactSupport.1 hh.1).2

  have hg1 : Continuous (fun p : OO Z => zpart Z (p : Sp k n).1) :=
    (continuousOn_zpart hZ).comp_continuous (continuous_fst.comp continuous_subtype_val) fun p => p.2.1
  have hg2 : Continuous (fun p : OO Z => (((p : Sp k n).1 - zpart Z (p : Sp k n).1, (p : Sp k n).2) : Sp k n)) :=
    ((continuous_fst.comp continuous_subtype_val).sub hg1).prodMk (continuous_snd.comp continuous_subtype_val)

  set S : Set (OO Z) := {p | zpart Z (p : Sp k n).1 ∈ A} with hSdef
  have hSc : IsClosed S := hAc.isClosed.preimage hg1
  have hSo : IsOpen S := by
    rw [isOpen_iff_forall_mem_open]
    intro p hp
    obtain ⟨U, hU, hpU, hUA⟩ := hAo _ hp
    refine ⟨(fun q : OO Z => zpart Z (q : Sp k n).1) ⁻¹' U, fun q hq => hUA ⟨hq, (zpart_spec q.2.1).1⟩,
      hU.preimage hg1, hpU⟩
  have hphi : (fun p : OO Z => psi Z A h p) =
      fun p => S.indicator (fun _ => (1 : ℂ)) p * h (((p : Sp k n).1 - zpart Z (p : Sp k n).1, (p : Sp k n).2)) := by
    funext p
    rw [psi_of_mem p.2.1]
    by_cases hp : p ∈ S
    · rw [Set.indicator_of_mem hp, Set.indicator_of_mem (show zpart Z (p : Sp k n).1 ∈ A from hp)]; rfl
    · rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem (show zpart Z (p : Sp k n).1 ∉ A from hp)]

  have hsupp_cl : IsClosed (Function.support h) := by
    have : Function.support h = (h ⁻¹' {0})ᶜ := by ext x; simp [Function.mem_support]
    rw [this]
    exact (hhl.isOpen_fiber 0).isClosed_compl
  have hts : tsupport h ⊆ UU := by
    rw [tsupport, hsupp_cl.closure_eq]; exact hh.2

  set K : Set (Matrix (Fin n) (Fin n) k × Sp k n) := A ×ˢ (tsupport h ∩ (NB Z ×ˢ Set.univ)) with hK
  have hKc : IsCompact K := hAc.prod (hhc.inter_right ((isClosed_NB Z).prod isClosed_univ))
  set Φ : Matrix (Fin n) (Fin n) k × Sp k n → Sp k n := fun aq => (aq.1 + aq.2.1, aq.2.2) with hΦ
  have hΦc : Continuous Φ := (continuous_fst.add (continuous_fst.comp continuous_snd)).prodMk
    (continuous_snd.comp continuous_snd)
  have hΦO : Φ '' K ⊆ OO Z := by
    rintro _ ⟨⟨a, q⟩, ⟨ha, hq, hqN⟩, rfl⟩
    have h2 : q.2 ≠ 0 := hts hq
    exact ⟨(cc_of_NB hZ (hAZ ha) hqN.1).1, h2⟩
  set Kc : Set (OO Z) := (Subtype.val : OO Z → Sp k n) ⁻¹' (Φ '' K) with hKcdef
  have hKcc : IsCompact Kc := by
    rw [Subtype.isCompact_iff, Set.image_preimage_eq_inter_range, Subtype.range_coe,
      Set.inter_eq_left.2 hΦO]
    exact hKc.image hΦc
  have hsub : Function.support (fun p : OO Z => psi Z A h p) ⊆ Kc := by
    intro p hp
    rw [hphi, Function.mem_support] at hp
    have hpS : p ∈ S := by
      by_contra hn; rw [Set.indicator_of_notMem hn, zero_mul] at hp; exact hp rfl
    have hq : h (((p : Sp k n).1 - zpart Z (p : Sp k n).1, (p : Sp k n).2)) ≠ 0 := by
      rw [Set.indicator_of_mem hpS, one_mul] at hp; exact hp
    refine ⟨(zpart Z (p : Sp k n).1, (((p : Sp k n).1 - zpart Z (p : Sp k n).1, (p : Sp k n).2))),
      ⟨hpS, subset_tsupport _ hq, sub_mem_NB hZ p.2.1, Set.mem_univ _⟩, ?_⟩
    simp only [hΦ, add_sub_cancel]
  obtain ⟨f, hf, hfe⟩ := GroundTheory.Automorphic.Whittaker.exists_lift hUU hOU (φ := fun p : OO Z => psi Z A h p) (by
    rw [GroundTheory.Automorphic.mem_locallyConstantCompactSupport]
    refine ⟨?_, ?_⟩
    · rw [hphi]
      exact IsLocallyConstant.comp₂ (lc_indicator ⟨hSc, hSo⟩ 1) (hhl.comp_continuous hg2) (· * ·)
    · exact IsCompact.of_isClosed_subset hKcc isClosed_closure (closure_minimal hsub hKcc.isClosed))
  exact ⟨f, hf, fun p hp => hfe ⟨p, hp⟩⟩

end PositivityTheory.RgUd.TP.Nil.Fib2

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.IntegralParts.LocallyConstantCosets.PsiCosets
section
noncomputable section

open Matrix GroundTheory.Automorphic.Whittaker GlobalTheory.SplitWeil
open scoped Pointwise

namespace PositivityTheory.RgUd.TP.Nil.Fib2

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Nil PositivityTheory.RgUd.TP.Nil.Fib1

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
  {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)}

theorem psi_cosets {L M : AddSubgroup (Matrix (Fin n) (Fin n) k)} (hL : IsLat Z L) (hM : IsLat Z M) (hML : M ≤ L) :
    ∃ D : Finset (Matrix (Fin n) (Fin n) k), D.card = M.relIndex L ∧ (∀ d ∈ D, d ∈ L) ∧
      ∀ h : Sp k n → ℂ, psi Z (L : Set (Matrix (Fin n) (Fin n) k)) h =
        ∑ d ∈ D, psi Z ((fun a => a + d) '' (M : Set (Matrix (Fin n) (Fin n) k))) h := by
  classical
  have hfi : (M.addSubgroupOf L).FiniteIndex := ⟨lat_index_pos hL hM hML⟩
  haveI : Fintype (L ⧸ M.addSubgroupOf L) := Fintype.ofFinite _
  let f : (L ⧸ M.addSubgroupOf L) → Matrix (Fin n) (Fin n) k := fun q => ((Quotient.out q : L) : Matrix (Fin n) (Fin n) k)
  have hf : Function.Injective f := fun a b hab => Quotient.out_inj.1 (Subtype.ext hab)
  have hmem : ∀ z q, z ∈ (fun a => a + f q) '' (M : Set (Matrix (Fin n) (Fin n) k)) ↔ z - f q ∈ M := by
    intro z q
    constructor
    · rintro ⟨m, hm, rfl⟩
      simpa using hm
    · intro hz
      exact ⟨z - f q, hz, by simp⟩
  have key : ∀ z, (L : Set (Matrix (Fin n) (Fin n) k)).indicator (1 : Matrix (Fin n) (Fin n) k → ℂ) z =
      ∑ d ∈ Finset.univ.image f, ((fun a => a + d) '' (M : Set (Matrix (Fin n) (Fin n) k))).indicator 1 z := by
    intro z
    rw [Finset.sum_image (fun a _ b _ hab => hf hab)]
    by_cases hz : z ∈ L
    · rw [Set.indicator_of_mem (show z ∈ (L : Set (Matrix (Fin n) (Fin n) k)) from hz)]
      have hq : ∀ q, ((fun a => a + f q) '' (M : Set (Matrix (Fin n) (Fin n) k))).indicator
          (1 : Matrix (Fin n) (Fin n) k → ℂ) z =
          if (QuotientAddGroup.mk ⟨z, hz⟩ : L ⧸ M.addSubgroupOf L) = q then 1 else 0 := by
        intro q
        have e : z - f q ∈ M ↔ (QuotientAddGroup.mk ⟨z, hz⟩ : L ⧸ M.addSubgroupOf L) =
            QuotientAddGroup.mk (Quotient.out q) := by
          rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
          show z - f q ∈ M ↔ -z + f q ∈ M
          rw [show -z + f q = -(z - f q) by abel, neg_mem_iff]
        rw [QuotientAddGroup.out_eq'] at e
        by_cases h : (QuotientAddGroup.mk ⟨z, hz⟩ : L ⧸ M.addSubgroupOf L) = q
        · rw [if_pos h, Set.indicator_of_mem ((hmem z q).2 (e.2 h))]
          rfl
        · rw [if_neg h, Set.indicator_of_notMem (fun h' => h (e.1 ((hmem z q).1 h')))]
      simp only [hq, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      rfl
    · rw [Set.indicator_of_notMem (show z ∉ (L : Set (Matrix (Fin n) (Fin n) k)) from hz)]
      symm
      apply Finset.sum_eq_zero
      intro q _
      apply Set.indicator_of_notMem
      intro h'
      apply hz
      have h2 : z = (z - f q) + f q := by abel
      rw [h2]
      exact L.add_mem (hML ((hmem z q).1 h')) (Quotient.out q).2
  refine ⟨Finset.univ.image f, ?_, ?_, fun h => funext fun p => ?_⟩
  · rw [Finset.card_image_of_injective _ hf, Finset.card_univ, ← Nat.card_eq_fintype_card]
    rfl
  · intro d hd
    obtain ⟨q, _, rfl⟩ := Finset.mem_image.1 hd
    exact (Quotient.out q).2
  · rw [Finset.sum_apply]
    by_cases hp : p.1 ∈ CC Z
    · simp only [psi, Set.indicator_of_mem (show p ∈ {q : Sp k n | q.1 ∈ CC Z} from hp)]
      rw [key, Finset.sum_mul]
    · simp only [psi, Set.indicator_of_notMem (show p ∉ {q : Sp k n | q.1 ∈ CC Z} from hp), Finset.sum_const_zero]

end PositivityTheory.RgUd.TP.Nil.Fib2

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.IntegralParts.LocallyConstantCosets.UnifLC
section
noncomputable section

open Matrix GroundTheory.Automorphic GroundTheory.Automorphic.Whittaker Set

namespace PositivityTheory.RgUd.TP.Nil.Fib2

open PositivityTheory.RgUd.T

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

theorem unifLC {F : Sp k n → ℂ} (hF : F ∈ locallyConstantCompactSupport (Sp k n) ℂ ℂ) :
    ∃ W ∈ nhds (0 : Matrix (Fin n) (Fin n) k), ∀ w ∈ W, ∀ p : Sp k n, F (p.1 + w, p.2) = F p := by
  obtain ⟨hlc, hcs⟩ := hF
  have hK : IsCompact (tsupport F) := hcs
  have hc1 : Continuous fun z : Matrix (Fin n) (Fin n) k × Sp k n => ((z.2.1 + z.1, z.2.2) : Sp k n) := by
    fun_prop
  have hc2 : Continuous fun z : Matrix (Fin n) (Fin n) k × Sp k n => ((z.2.1 - z.1, z.2.2) : Sp k n) := by
    fun_prop
  have hev : ∀ᶠ w in nhds (0 : Matrix (Fin n) (Fin n) k), ∀ q ∈ tsupport F,
      F (q.1 + w, q.2) = F q ∧ F (q.1 - w, q.2) = F q := by
    refine hK.eventually_forall_of_forall_eventually ?_
    intro q _
    have e1 := (hlc.comp_continuous hc1).eventually_eq ((0 : Matrix (Fin n) (Fin n) k), q)
    have e2 := (hlc.comp_continuous hc2).eventually_eq ((0 : Matrix (Fin n) (Fin n) k), q)
    have e3 := (hlc.comp_continuous continuous_snd).eventually_eq ((0 : Matrix (Fin n) (Fin n) k), q)
    filter_upwards [e1, e2, e3] with z h1 h2 h3
    simp only [Function.comp_apply, add_zero, sub_zero] at h1 h2 h3
    exact ⟨by rw [h1, h3], by rw [h2, h3]⟩
  refine ⟨_, hev, ?_⟩
  intro w hw p
  by_cases hp : p ∈ tsupport F
  · exact (hw p hp).1
  · have h0 : F p = 0 := image_eq_zero_of_notMem_tsupport hp
    by_cases hp' : ((p.1 + w, p.2) : Sp k n) ∈ tsupport F
    · have := (hw _ hp').2
      simp only [add_sub_cancel_right] at this
      rw [h0] at this ⊢
      exact this.symm
    · rw [h0]
      exact image_eq_zero_of_notMem_tsupport hp'

end PositivityTheory.RgUd.TP.Nil.Fib2

end
end

