module

public import Formalism.ThetaLogCoordinates.TraceIsometryWeights.SchurTraceProofs.OrthogonalIsomorphismHolds
public import Formalism.ThetaLogCoordinates.TraceIsometryWeights.SchurTraceProofs.Bundle0002
public import Formalism.ThetaLogCoordinates.TraceIsometryWeights.SchurTraceProofs.Bundle0003
public import Formalism.ThetaLogCoordinates.TraceIsometryWeights.Bundle0001
public import Formalism.ThetaLogCoordinates.TraceIsometryWeights.StatementC

@[expose] public section

-- bundled from Formalism.ThetaLogCoordinates.TraceIsometryWeights.SchurTraceProofs.CompEqZeroOfNotDle
section
namespace Formalism.InvariantFactorPaths.PW

open Formalism.GM.M Formalism.GM.DimensionMonotonicity MvPolynomial Finset

section abstract

variable {K V : Type} [Field K] [CharZero K] [AddCommGroup V] [Module K V] {n : ℕ} (G : GlW K V n)

theorem gSall_le_iSup (μ : Fin n → ℤ) :
    G.gS {v | G.IsHW μ v} ≤ ⨆ v : {v // G.IsHW μ v}, G.gS {v.1} := by
  have hgs : ∀ s : Set V, G.Stable (G.gS s) := fun s a b x hx => by
    rw [GlW.gS, Submodule.mem_sInf] at hx ⊢
    exact fun U hU => hU.2 a b x (hx U hU)
  have hstab : G.Stable (⨆ v : {v // G.IsHW μ v}, G.gS {v.1}) := by
    intro a b x hx
    induction hx using Submodule.iSup_induction' with
    | mem i y hy => exact Submodule.mem_iSup_of_mem i (hgs _ a b y hy)
    | zero =>
      rw [map_zero]
      exact Submodule.zero_mem _
    | add y z _ _ hy hz =>
      rw [map_add (f := _)]
      exact Submodule.add_mem _ hy hz
  show sInf {U : Submodule K V | {v | G.IsHW μ v} ⊆ (U : Set V) ∧ G.Stable U} ≤ _
  refine sInf_le ⟨fun v hv => ?_, hstab⟩
  have hv' : v ∈ G.gS {v} := by
    rw [GlW.gS, Submodule.mem_sInf]
    exact fun U hU => hU.1 (Set.mem_singleton v)
  exact Submodule.mem_iSup_of_mem (⟨v, hv⟩ : {v // G.IsHW μ v}) hv'

theorem comp_eq_zero_of_not_dle {μ ν : Fin n → ℤ} (hν : ¬ Dle ν μ) {x : V} (hx : x ∈ G.gS {v | G.IsHW μ v}) :
    G.comp ν x = 0 := by
  have hk : ⨆ v : {v // G.IsHW μ v}, G.gS {v.1} ≤ LinearMap.ker (G.comp ν) :=
    iSup_le fun v y hy => by
      rw [LinearMap.mem_ker]
      by_contra h
      exact hν (GlW.wt_le_of_mem G v.2 hy h)
  exact hk (gSall_le_iSup G μ hx)

theorem isHW_of_mem_gSall {μ : Fin n → ℤ} {x : V} (hx : x ∈ G.gS {v | G.IsHW μ v}) (hw : G.IsWt μ x) :
    G.IsHW μ x := by
  refine ⟨hw, fun a b hab => ?_⟩
  have h1 : G.IsWt (μ + dl a b) (G.E a b x) := G.isWt_E hw a b
  have h2 : ¬ Dle (μ + dl a b) μ := by
    intro h
    have e := Dle_antisymm h (Dle_raise μ hab)
    exact dl_ne_zero (ne_of_lt hab) (by simpa using e)
  rw [← h1]
  exact comp_eq_zero_of_not_dle G h2 (G.gS_stable _ a b x hx)

def lowIm : Submodule K V := ⨆ (a : Fin n) (b : Fin n) (_ : b < a), Submodule.map (G.E a b) ⊤

theorem comp_mem_lowIm {μ ν : Fin n → ℤ} (hne : μ ≠ ν) {x : V} (hx : x ∈ G.gS {v | G.IsHW ν v}) :
    G.comp μ x ∈ lowIm G := by
  have hle : G.gS {v | G.IsHW ν v} ≤ (lowIm G).comap (G.comp μ) := by
    refine (gSall_le_iSup G ν).trans (iSup_le fun v => ?_)
    refine (G.gS_le_Lw v.2).trans (G.Lw_le v.1 ?_ ?_)
    · rw [Submodule.mem_comap, G.comp_of_isWt v.2.1, if_neg hne]
      exact Submodule.zero_mem _
    · intro a b hab y _
      rw [Submodule.mem_comap, G.shift]
      exact (le_iSup_of_le a (le_iSup_of_le b (le_iSup_of_le hab le_rfl)) :
        Submodule.map (G.E a b) ⊤ ≤ lowIm G) (Submodule.mem_map_of_mem Submodule.mem_top)
  exact hle hx

end abstract

variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

theorem isoC_congr (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r)) {la la' : Fin r → ℤ}
    (h : ∀ c ∈ Cs, la c = la' c) : IsoC p LL j Cs la = IsoC p LL j Cs la' := by
  have hc : la ∘ enumC Cs = la' ∘ enumC Cs := by
    funext i
    exact h _ (Finset.orderEmbOfFin_mem Cs rfl i)
  rw [isoC_eq, isoC_eq, hc]

theorem iSup_isoC_eq (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r)) (la : Fin r → ℤ) :
    (⨆ (la' : Fin r → ℤ) (_ : la' ∈ {la' : Fin r → ℤ | ∀ c ∈ Cs, la' c = la c}), IsoC p LL j Cs la') =
      IsoC p LL j Cs la := by
  refine le_antisymm (iSup₂_le fun la' h => (isoC_congr LL j Cs h).le) ?_
  exact le_iSup₂_of_le la (fun c _ => rfl) le_rfl

theorem isoC_diag (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r)) (c : Fin r) (la : Fin r → ℤ) :
    ∀ x ∈ IsoC p LL j Cs la, glAct p LL j c c x ∈ IsoC p LL j Cs la := by
  intro x hx
  by_cases hc : c ∈ Cs
  · exact isoC_stable LL j Cs la c hc c hc x hx
  · refine isoC_map_of_comm LL j Cs (glAct p LL j c c) (fun c' hc' d' hd' y => ?_) la x hx
    have h := glAct_comm (p := p) LL j c c c' d' y
    have h1 : ¬ c = c' := fun h => hc (h ▸ hc')
    have h2 : ¬ d' = c := fun h => hc (h ▸ hd')
    rw [if_neg h1, if_neg h2, sub_zero, sub_eq_zero] at h
    exact h

theorem wtSpC_mono (LL : Letters N) (j : ℕ) {Cs Cs' : Finset (Fin r)} (h : Cs ⊆ Cs') (la : Fin r → ℤ) :
    WtSpC p LL j Cs' la ≤ WtSpC p LL j Cs la := by
  intro x hx
  rw [WtSpC, MvPolynomial.mem_restrictSupport_iff] at hx ⊢
  exact fun m hm c hc => hx hm c (h hc)

noncomputable def lowC (p : ℕ) [Fact p.Prime] (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r)) :
    Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]) :=
  ⨆ (c : Fin r) (d : Fin r) (_ : c ∈ Cs ∧ d ∈ Cs ∧ d < c), Submodule.map (glAct p LL j c d) ⊤

theorem lowIm_le_lowC (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r)) :
    lowIm (GAe p LL j (enumC Cs)) ≤ lowC p LL j Cs := by
  unfold lowIm lowC
  refine iSup₂_le fun a b => iSup_le fun hab => ?_
  exact le_iSup₂_of_le (enumC Cs a) (enumC Cs b)
    (le_iSup_of_le ⟨Finset.orderEmbOfFin_mem Cs rfl a, Finset.orderEmbOfFin_mem Cs rfl b,
      (enumC Cs).strictMono hab⟩ le_rfl)

theorem lowC_le_perpV (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r)) (la : Fin r → ℤ)
    {h : MvPolynomial (Fin N × Fin r) ℚ_[p]} (hh : h ∈ HWC p LL j Cs la) : lowC p LL j Cs ≤ perpV h := by
  refine iSup_le fun c => iSup_le fun d => iSup_le fun hcd => ?_
  rintro _ ⟨z, -, rfl⟩
  rw [HWC, Submodule.mem_inf] at hh
  have h2 := hh.2
  simp only [Submodule.mem_iInf, LinearMap.mem_ker] at h2
  rw [mem_perpV, fischerAdjointness_holds, h2 d c ⟨hcd.2.1, hcd.1, hcd.2.2⟩, fock_zero_right']

theorem fock_comp_right {n : ℕ} (LL : Letters N) (j : ℕ) (e : Fin n ↪o Fin r) {μ : Fin n → ℤ}
    {x : MvPolynomial (Fin N × Fin r) ℚ_[p]} (hx : (GAe p LL j e).IsWt μ x)
    (z : MvPolynomial (Fin N × Fin r) ℚ_[p]) : fock p x z = fock p x ((GAe p LL j e).comp μ z) := by
  classical
  obtain ⟨S, hS⟩ := (GAe p LL j e).dec z
  have hz := (GAe p LL j e).sum_comp z (insert μ S) (fun ν hν => hS ν (fun h => hν (Finset.mem_insert_of_mem h)))
  conv_lhs => rw [← hz]
  rw [fock_sum_right', Finset.sum_eq_single μ]
  · intro ν _ hν
    exact fock_wt_ne LL j e (Ne.symm hν) hx ((GAe p LL j e).isWt_comp ν z)
  · intro h
    exact absurd (Finset.mem_insert_self μ S) h

theorem extP_of (hI : IntP) : ExtP := by
  intro p _ N r LL ρ j _ la
  set Cs : Finset (Fin r) := univ.erase ρ with hCs
  have hcard : Cs.card = r - 1 := by
    rw [hCs, Finset.card_erase_of_mem (Finset.mem_univ ρ), Finset.card_univ, Fintype.card_fin]
  set T : Set (Fin r → ℤ) := {la' : Fin r → ℤ | ∀ c ∈ Cs, la' c = la c} with hT
  have hsat : CsSaturated Cs T := by
    intro a b hab
    constructor
    · intro h c hc; rw [← hab c hc]; exact h c hc
    · intro h c hc; rw [hab c hc]; exact h c hc
  obtain ⟨PT, hPT, hadj⟩ := projection_lattice_holds p N r LL j Cs T hsat
  have hidem : ∀ x, PT (PT x) = PT x := fun x => congrArg (fun f => f x) hPT.1
  have hrange : LinearMap.range PT = IsoC p LL j Cs la := by
    rw [hPT.2.1]; exact iSup_isoC_eq LL j Cs la
  have hker := hPT.2.2
  set Gu := GAe p LL j (enumC (univ : Finset (Fin r))) with hGu
  set lu : Fin (univ : Finset (Fin r)).card → ℤ := la ∘ enumC univ with hlu
  set G := GAe p LL j (enumC Cs) with hG
  have hwt : ∀ x, x ∈ WtSpC p LL j univ la ↔ Gu.IsWt lu x := fun x => wtSpC_iff LL j univ la x

  have hcomm : ∀ x, PT (Gu.comp lu x) = Gu.comp lu (PT x) := by
    intro x
    refine Formalism.CountingSumsFrames.GlX.comp_comm_of Gu (W := ⊤) (fun _ _ _ => Submodule.mem_top) PT ?_ x Submodule.mem_top lu
    intro y _ c
    exact congrArg (fun f => f y)
      (typeProj_comm LL j Cs T PT hPT (glAct p LL j (enumC univ c) (enumC univ c)) (isoC_diag LL j Cs _))
  have hfix : ∀ x ∈ IsoC p LL j Cs la, PT x = x := by
    intro x hx
    rw [← hrange] at hx
    obtain ⟨y, rfl⟩ := hx
    exact hidem y
  have hP_wt : ∀ x ∈ WtSpC p LL j univ la, (PT ∘ₗ Gu.comp lu) x = PT x := by
    intro x hx
    rw [LinearMap.comp_apply, (hwt x).mp hx]
  have hmem : ∀ x, (PT ∘ₗ Gu.comp lu) x ∈ HWC p LL j Cs la ⊓ WtSpC p LL j univ la := by
    intro x
    have h1 : (PT ∘ₗ Gu.comp lu) x ∈ IsoC p LL j Cs la := by
      rw [← hrange]; exact LinearMap.mem_range_self _ _
    have h2 : (PT ∘ₗ Gu.comp lu) x ∈ WtSpC p LL j univ la := by
      rw [LinearMap.comp_apply, hcomm, hwt]
      exact Gu.isWt_comp lu _
    refine Submodule.mem_inf.mpr ⟨?_, h2⟩
    rw [hwc_iff]
    rw [isoC_eq] at h1
    exact isHW_of_mem_gSall G h1 ((wtSpC_iff LL j Cs la _).mp (wtSpC_mono LL j (Finset.subset_univ Cs) la h2))
  refine ⟨PT ∘ₗ Gu.comp lu, ?_, ?_, ?_, ?_, ?_⟩
  · refine LinearMap.ext fun x => ?_
    rw [LinearMap.comp_apply, hP_wt _ (hmem x).2]
    exact hfix _ (hwc_le_isoC LL j Cs la (hmem x).1)
  · apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      exact hmem x
    · intro h hh
      refine ⟨h, ?_⟩
      rw [hP_wt h hh.2]
      exact hfix h (hwc_le_isoC LL j Cs la hh.1)
  · show LinearMap.ker (PT ∘ₗ Gu.comp lu) ⊓ WtSpC p LL j univ la = lowC p LL j Cs ⊓ WtSpC p LL j univ la
    apply le_antisymm
    · intro x hx
      obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.mp hx
      refine Submodule.mem_inf.mpr ⟨?_, hx2⟩
      rw [LinearMap.mem_ker, hP_wt x hx2, ← LinearMap.mem_ker, hker] at hx1
      have hle : (⨆ (mu : Fin r → ℤ) (_ : mu ∉ T), IsoC p LL j Cs mu) ≤
          (lowC p LL j Cs).comap (G.comp (la ∘ enumC Cs)) := by
        refine iSup₂_le fun mu hmu => ?_
        intro z hz
        rw [isoC_eq] at hz
        rw [Submodule.mem_comap]
        refine lowIm_le_lowC LL j Cs (comp_mem_lowIm G ?_ hz)
        intro h
        exact hmu ((comp_eq_iff Cs mu la).mp h.symm)
      have h3 := hle hx1
      rw [Submodule.mem_comap] at h3
      have h4 : G.comp (la ∘ enumC Cs) x = x :=
        (wtSpC_iff LL j Cs la x).mp (wtSpC_mono LL j (Finset.subset_univ Cs) la hx2)
      rwa [h4] at h3
    · intro x hx
      obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.mp hx
      refine Submodule.mem_inf.mpr ⟨?_, hx2⟩
      rw [LinearMap.mem_ker, hP_wt x hx2]
      refine fock_nondeg _ fun y => ?_
      rw [hadj, fock_comp_right LL j (enumC univ) ((hwt x).mp hx2) (PT y)]
      have h5 : Gu.comp lu (PT y) ∈ HWC p LL j Cs la := by
        rw [← hcomm]; exact (hmem y).1
      exact lowC_le_perpV LL j Cs la h5 hx1
  · intro F F' hF hF'
    rw [hP_wt F hF, hP_wt F' hF']
    exact hadj F F'
  · intro F hF hFw
    rw [hP_wt F hFw, ← hcard]
    exact hI p N r LL j Cs T PT hsat hPT F hF

end Formalism.InvariantFactorPaths.PW
end

-- bundled from Formalism.ThetaLogCoordinates.TraceIsometryWeights.SchurTraceProofs.PolLeISupIsoW
section
namespace Formalism.InvariantFactorPaths.PW

open Formalism.GM.M Formalism.GM.DimensionMonotonicity MvPolynomial Finset

section gen

variable {K V : Type} [Field K] [CharZero K] [AddCommGroup V] [Module K V] {n : ℕ}

theorem isoW_eq_bot (G : GlW K V n) (W : Submodule K V) {S : Finset (Fin n → ℤ)}
    (hS : ∀ x ∈ W, ∀ μ ∉ S, G.comp μ x = 0) {μ : Fin n → ℤ} (hμ : μ ∉ S) : IsoW G W μ = ⊥ := by
  refine eq_bot_iff.mpr (sInf_le ⟨?_, ?_⟩)
  · rintro v ⟨hv, hvW⟩
    have h1 : G.comp μ v = v := hv.1
    rw [SetLike.mem_coe, Submodule.mem_bot, ← h1]
    exact hS v hvW μ hμ
  · intro a b x hx
    rw [Submodule.mem_bot] at hx ⊢
    rw [hx, map_zero]

end gen

variable {p : ℕ} [Fact p.Prime] {N r n : ℕ}

theorem pol_le_iSup_isoW (LL L2 : Letters N) (j : ℕ) (e : Fin n ↪o Fin r) :
    Pol p r L2 ≤ ⨆ μ, IsoW (GAe p LL j e) (Pol p r L2) μ := by
  classical
  obtain ⟨S, hS⟩ := GAe_pol_finW (p := p) LL L2 j e
  have key := Formalism.CountingSumsFrames.GlX.span_hw (GAe p LL j e) (GAe_pol_stable LL L2 j e) hS
    (ι := {v : MvPolynomial (Fin N × Fin r) ℚ_[p] // v ∈ Pol p r L2 ∧ v ≠ 0 ∧
      ∃ μ, (GAe p LL j e).IsHW μ v})
    (fun i => i.1) (fun i => i.2.2.2.choose) (fun i => i.2.2.2.choose_spec) (fun i => i.2.1) (fun i => i.2.2.1)
    (by
      intro μ v hv hw
      by_cases h0 : v = 0
      · rw [h0]; exact Submodule.zero_mem _
      · exact Submodule.subset_span ⟨⟨v, hv, h0, μ, hw⟩, rfl⟩)
  refine key.trans (iSup_le fun i => ?_)
  refine le_trans ?_ (le_iSup _ i.2.2.2.choose)
  refine GlW.gS_le _ ?_ (GlW.gS_stable _ _)
  intro v hv
  rw [Set.mem_singleton_iff] at hv
  subst hv
  exact GlW.subset_gS _ _ ⟨i.2.2.2.choose_spec, i.2.1⟩

theorem isoW_le_isoC (LL L2 : Letters N) (j : ℕ) (Cs : Finset (Fin r)) (la : Fin r → ℤ) :
    IsoW (GAe p LL j (enumC Cs)) (Pol p r L2) (la ∘ enumC Cs) ≤ IsoC p LL j Cs la := by
  rw [isoC_eq]
  unfold IsoW GlW.gS
  exact sInf_le_sInf fun U hU => ⟨fun v hv => hU.1 hv.1, hU.2⟩

theorem intP_of (hT : TypeInt) (hB : LatBasisPol) : IntP := by
  classical
  intro p _ N r LL j Cs T P hsat hP F hF
  obtain ⟨hPP, hran, hker⟩ := hP
  have D := polLatData_of hB (p := p) (r := r) LL LL j (enumC Cs)
  obtain ⟨S, hS⟩ := D.finW
  choose Q hQ1 hQ2 hQ3 using hT p _ Cs.card (GAe p LL j (enumC Cs)) (Pol p r LL) _ LL.total D
  have key : ∀ x ∈ Pol p r LL,
      P x = ∑ μ ∈ S.filter (fun μ => ∃ la ∈ T, la ∘ enumC Cs = μ), Q μ x := by
    intro x hx
    refine Submodule.iSup_induction _
      (motive := fun x => P x = ∑ μ ∈ S.filter (fun μ => ∃ la ∈ T, la ∘ enumC Cs = μ), Q μ x)
      (pol_le_iSup_isoW LL LL j (enumC Cs) hx) ?_ ?_ ?_
    · intro ν x hx
      by_cases hν : ν ∈ S
      · obtain ⟨la, hla⟩ := exists_ext Cs ν
        have hxC : x ∈ IsoC p LL j Cs la := isoW_le_isoC LL LL j Cs la (by rw [hla]; exact hx)
        by_cases hf : ∃ la' ∈ T, la' ∘ enumC Cs = ν
        · obtain ⟨la', hla'T, hla'⟩ := hf
          have hlaT : la ∈ T := (hsat la la' ((comp_eq_iff Cs la la').mp (hla.trans hla'.symm))).mpr hla'T
          have hxr : x ∈ LinearMap.range P := by
            rw [hran]; exact Submodule.mem_iSup_of_mem la (Submodule.mem_iSup_of_mem hlaT hxC)
          have hPx : P x = x := by
            obtain ⟨y, rfl⟩ := hxr
            exact LinearMap.congr_fun hPP y
          rw [hPx, Finset.sum_eq_single ν]
          · exact (hQ1 ν x hx).symm
          · intro μ _ hne
            exact hQ2 μ ν hne.symm x hx
          · intro hn
            exact absurd (Finset.mem_filter.mpr ⟨hν, la', hla'T, hla'⟩) hn
        · have hlaT : la ∉ T := fun h => hf ⟨la, h, hla⟩
          have hxk : x ∈ LinearMap.ker P := by
            rw [hker]; exact Submodule.mem_iSup_of_mem la (Submodule.mem_iSup_of_mem hlaT hxC)
          rw [LinearMap.mem_ker.mp hxk]
          symm
          refine Finset.sum_eq_zero fun μ hμ => ?_
          refine hQ2 μ ν ?_ x hx
          rintro rfl
          exact hf (Finset.mem_filter.mp hμ).2
      · rw [isoW_eq_bot _ _ hS hν, Submodule.mem_bot] at hx
        subst hx
        simp
    · simp
    · intro x y hx hy
      rw [map_add (f := _), hx, hy, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun μ _ => (map_add _ _ _).symm
  have hFp : F ∈ Pol p r LL := hF.1
  have hFi : F ∈ (IntPol p (Fin N × Fin r)).toAddSubgroup := hF.2
  rw [key F hFp, Finset.smul_sum, ← Submodule.mem_toAddSubgroup]
  exact AddSubgroup.sum_mem _ fun μ _ => hQ3 μ F hFi hFp

end Formalism.InvariantFactorPaths.PW
end

-- bundled from Formalism.ThetaLogCoordinates.TraceIsometryWeights.SchurTraceProofs.ZpClosedToAddSubgroup
section
namespace Formalism.InvariantFactorPaths.PW

open Formalism.GM.M Formalism.GM.DimensionMonotonicity MvPolynomial Finset

variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

noncomputable def polProj (p : ℕ) [Fact p.Prime] (r : ℕ) (L2 : Letters N) :
    MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p] :=
  weightedHomogeneousComponent (wL N r) (fun i => (L2.deg i : ℤ))

theorem polProj_mem (L2 : Letters N) (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    polProj p r L2 x ∈ Pol p r L2 := by
  rw [pol_iff]; exact weightedHomogeneousComponent_isWeightedHomogeneous _ _

theorem polProj_id (L2 : Letters N) {x : MvPolynomial (Fin N × Fin r) ℚ_[p]} (hx : x ∈ Pol p r L2) :
    polProj p r L2 x = x := by
  rw [pol_iff] at hx
  rw [polProj, weightedHomogeneousComponent_of_mem hx, if_pos rfl]

theorem polProj_glAct (LL L2 : Letters N) (j : ℕ) (c d : Fin r) (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    polProj p r L2 (glAct p LL j c d x) = glAct p LL j c d (polProj p r L2 x) :=
  Formalism.CountingSumsFrames.whc_comm _ _ (fun _ _ hx => glAct_wL LL j c d hx) _ x

theorem isoC_inf_pol_le (LL L2 : Letters N) (j : ℕ) (Cs : Finset (Fin r)) (la : Fin r → ℤ) :
    IsoC p LL j Cs la ⊓ Pol p r L2 ≤ IsoW (GAe p LL j (enumC Cs)) (Pol p r L2) (la ∘ enumC Cs) := by
  have hle : IsoC p LL j Cs la ≤
      (IsoW (GAe p LL j (enumC Cs)) (Pol p r L2) (la ∘ enumC Cs)).comap (polProj p r L2) := by
    rw [IsoC]
    refine sInf_le ⟨?_, ?_⟩
    · intro x hx
      rw [Submodule.mem_comap]
      refine (GAe p LL j (enumC Cs)).subset_gS _ ⟨?_, polProj_mem L2 x⟩
      exact (hwc_iff LL j Cs la _).mp
        (hwc_map_of_comm LL j Cs _ (fun c _ d _ y => polProj_glAct LL L2 j c d y) la x hx)
    · rw [stableC_iff]
      intro a b x hx
      rw [Submodule.mem_comap] at hx ⊢
      rw [GAe_E, polProj_glAct]
      exact (GAe p LL j (enumC Cs)).gS_stable _ a b _ hx
  intro x hx
  have h := hle hx.1
  rwa [Submodule.mem_comap, polProj_id L2 hx.2] at h

theorem weylLat_self (LL : Letters N) (j : ℕ) (h : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    h ∈ WeylLat p LL j h := by
  rw [WeylLat, Submodule.mem_sInf]
  exact fun L hL => hL.1

theorem weylLat_div (LL : Letters N) (j : ℕ) (h : MvPolynomial (Fin N × Fin r) ℚ_[p]) (c d : Fin r) (hcd : c ≠ d)
    (k : ℕ) (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) (hx : x ∈ WeylLat p LL j h) :
    (((k.factorial : ℚ_[p]))⁻¹) • ((glAct p LL j c d) ^ k) x ∈ WeylLat p LL j h := by
  rw [WeylLat, Submodule.mem_sInf] at hx ⊢
  exact fun L hL => hL.2 c d hcd k x (hx L hL)

theorem zpClosed_toAddSubgroup {W : Type} [AddCommGroup W] [Module ℚ_[p] W] [Module ℤ_[p] W]
    [IsScalarTower ℤ_[p] ℚ_[p] W] (L : Submodule ℤ_[p] W) : ZpClosed p L.toAddSubgroup := by
  intro c hc x hx
  rw [Submodule.mem_toAddSubgroup] at hx ⊢
  obtain ⟨a, ha⟩ : ∃ a : ℤ_[p], (a : ℚ_[p]) = c := ⟨⟨c, hc⟩, rfl⟩
  have e : c • x = a • x := by
    rw [← ha]
    exact algebraMap_smul ℚ_[p] a x
  rw [e]
  exact L.smul_mem _ hx

theorem iSup_weylLat_div (LL : Letters N) (j : ℕ) (Q : MvPolynomial (Fin N × Fin r) ℚ_[p] → Prop)
    (c d : Fin r) (hcd : c ≠ d) (k : ℕ) (x : MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hx : x ∈ ⨆ (h : MvPolynomial (Fin N × Fin r) ℚ_[p]) (_ : Q h), WeylLat p LL j h) :
    (((k.factorial : ℚ_[p]))⁻¹) • ((glAct p LL j c d) ^ k) x ∈
      ⨆ (h : MvPolynomial (Fin N × Fin r) ℚ_[p]) (_ : Q h), WeylLat p LL j h := by
  have hle : (⨆ (h : MvPolynomial (Fin N × Fin r) ℚ_[p]) (_ : Q h), WeylLat p LL j h) ≤
      (⨆ (h : MvPolynomial (Fin N × Fin r) ℚ_[p]) (_ : Q h), WeylLat p LL j h).comap
        (((((k.factorial : ℚ_[p]))⁻¹) • ((glAct p LL j c d) ^ k) :
          MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p]).restrictScalars ℤ_[p]) := by
    refine iSup_le fun h => iSup_le fun hh => ?_
    intro y hy
    rw [Submodule.mem_comap]
    exact (le_iSup_of_le h (le_iSup_of_le hh le_rfl) :
      WeylLat p LL j h ≤ ⨆ (h : MvPolynomial (Fin N × Fin r) ℚ_[p]) (_ : Q h), WeylLat p LL j h)
      (weylLat_div LL j h c d hcd k y hy)
  exact hle hx

theorem weylP_of (hW : WeylInt) (hB : LatBasisPol) : WeylP := by
  intro p _ N r LL j _ la x hx hxi
  have he : kapC p r LL.total = (univ : Finset (Fin r)).card.choose 2 *
      Nat.log p (LL.total + (univ : Finset (Fin r)).card - 1) := by
    rw [kapC, Finset.card_univ, Fintype.card_fin]
  rw [he]
  have h1 := hW p _ _ (GAe p LL j (enumC (univ : Finset (Fin r)))) (Pol p r LL)
    (IntPol p (Fin N × Fin r)).toAddSubgroup LL.total (polLatData_of hB LL LL j _) (la ∘ enumC univ) x
    (isoC_inf_pol_le LL LL j univ la hx) hxi
  have hle : DeltaLat p (GAe p LL j (enumC (univ : Finset (Fin r))))
      {h | (GAe p LL j (enumC (univ : Finset (Fin r)))).IsHW (la ∘ enumC univ) h ∧ h ∈ Pol p r LL ∧
        h ∈ (IntPol p (Fin N × Fin r)).toAddSubgroup} ≤
      (⨆ (h : MvPolynomial (Fin N × Fin r) ℚ_[p])
        (_ : h ∈ HWC p LL j univ la ⊓ Pol p r LL ∧ h ∈ IntPol p (Fin N × Fin r)),
        WeylLat p LL j h).toAddSubgroup := by
    refine sInf_le ⟨?_, zpClosed_toAddSubgroup _, ?_⟩
    · rintro h ⟨h1, h2, h3⟩
      exact (le_iSup_of_le h (le_iSup_of_le ⟨⟨(hwc_iff LL j univ la h).mpr h1, h2⟩, h3⟩ le_rfl) :
        WeylLat p LL j h ≤ ⨆ (h : MvPolynomial (Fin N × Fin r) ℚ_[p])
          (_ : h ∈ HWC p LL j univ la ⊓ Pol p r LL ∧ h ∈ IntPol p (Fin N × Fin r)), WeylLat p LL j h)
        (weylLat_self LL j h)
    · intro a b hab k y hy
      exact iSup_weylLat_div LL j _ _ _ (fun h => hab ((enumC univ).injective h)) k y hy
  exact hle h1

end Formalism.InvariantFactorPaths.PW
end

