module

public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle0023
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.UniversalLiftFrame
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle0022
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle0019
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle0009

@[expose] public section

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ModelLPfJ
section
noncomputable section

namespace Formalism.MainNotions.N.Ln34.MLJ

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop)
    (π' Eπ : LetA O n) (h' : ℕ) (c : ZMod n)

theorem local_form (hwd : MLF.WD W T Pt π' c) {u₀ : LetA O n} (hu₀ : u₀ ∈ W.AΔ)
    (hΛ : u₀ * W.γA W.gamK (Eπ ^ h') = Eπ ^ h') (hlet : W.γA W.gamK (letE c : LetA O n) = letE c)
    (u : LL) (hu : u ≠ 0) (hu1 : ∀ i : ℤ, i ≠ 0 → u ^ i ≠ 1)
    (hlev : ∀ τ ζ, Pt c ζ τ → ∀ a, W.lev c ζ (W.γA W.gamK a) = PowerSeries.rescale u (W.lev c ζ a))
    (hsimp : ∀ τ ζ, Pt c ζ τ → ∃ U : PowerSeries LL, W.lev c ζ (Eπ ^ h') = PowerSeries.X ^ h' * U ∧
      PowerSeries.constantCoeff U ≠ 0)
    {x : LA W T π' c} (hx : x ∈ LamLA W T π' Eπ h' c ⊤)
    (hγ : γLA W T π' c x - x ∈ NL W T Pt π' Eπ h' c) :
    ∀ τ ζ, Pt c ζ τ → ∀ f, ExpL W T π' Eπ h' c ζ x f → ∀ i : ℤ, i ≠ 0 →
      f i ∈ Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ (-i) := by
  intro τ ζ hpt f hf i hi
  obtain ⟨⟨m₀, hf0⟩, m, a, y, hr, hfe⟩ := hf
  have hfb : MLG.Bdd f m₀ := hf0

  have hrγ := MLH.rep_γ W T π' Eπ h' c hu₀ hΛ hlet hr
  have hrn := MLE.rep_smul W T π' Eπ h' c hr (W.AΔ.algebraMap_mem (-1 : O))
  rw [← MLE.smul_eq_smulLA, neg_one_smul] at hrn
  have hra := MLE.rep_append W T π' Eπ h' c hrγ hrn
  rw [← sub_eq_add_neg] at hra
  have hgood := MLF.good_all W T Pt π' Eπ h' c hwd hγ hra τ ζ hpt
  rw [MLE.expS_append] at hgood
  set e := expS W T c ζ (fun j => (a j : LetA O n)) y with he
  have heb : MLG.Bdd e 0 := fun j hj => MLI.expS_neg W T c ζ _ y hj

  have hneg : expS W T c ζ (fun j => ((⟨algebraMap O (LetA O n) (-1) * a j,
      W.AΔ.mul_mem (W.AΔ.algebraMap_mem _) (a j).2⟩ : ↥W.AΔ) : LetA O n)) y = -e := by
    show expS W T c ζ (fun j => algebraMap O (LetA O n) (-1) * (a j : LetA O n)) y = -e
    rw [MLF.expS_alg_mul, map_neg, map_one, neg_one_smul]
  obtain ⟨U, hU, hU0⟩ := hsimp τ ζ hpt
  have hfu : MLG.Bdd (fun s => u ^ s • f s) m₀ := fun s hs => by simp only [hfb s hs, smul_zero]
  have hγpart : ∀ j, expS W T c ζ (fun k => ((⟨u₀ * W.γA W.gamK (a k), W.AΔ.mul_mem hu₀
      (MLH.γA_mem_AΔ W (a k).2)⟩ : ↥W.AΔ) : LetA O n)) y j =
      serMul (W.lev c ζ (Eπ ^ h')) (fun s => u ^ s • f s) j := by
    intro j
    show expS W T c ζ (fun k => u₀ * W.γA W.gamK (a k)) y j = _
    have hLdec : W.lev c ζ (Eπ ^ h') = W.lev c ζ u₀ * PowerSeries.rescale u (W.lev c ζ (Eπ ^ h')) := by
      rw [← hlev τ ζ hpt, ← map_mul, hΛ]
    rw [MLB.expS_mul, hLdec, ← MLG.serMul_serMul _ _ hfu]
    have hin : serMul (PowerSeries.rescale u (W.lev c ζ (Eπ ^ h'))) (fun s => u ^ s • f s) =
        fun s => u ^ s • e s := by
      funext s
      rw [← MLG.serMul_rescale u hu, hfe s]
    rw [hin, MLG.serMul_eq_sum (m₀ := 0) _ (fun s hs => by simp only [heb s hs, smul_zero]) j (j.toNat + 1) (by omega)]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [MLH.expS_γ W T c ζ u (hlev τ ζ hpt)]
    congr 1
    by_cases hjk : 0 ≤ j - (k : ℤ)
    · rw [← zpow_natCast, Int.toNat_of_nonneg hjk]
    · rw [MLI.expS_neg W T c ζ _ y (by omega), heb _ (by omega), smul_zero, smul_zero]

  set g : ℤ → T.V ⊗[Qp] BdR := fun s => u ^ s • f s - f s with hgdef
  have hgb : MLG.Bdd g m₀ := fun s hs => by simp [hgdef, hfb s hs]
  have hGg : ∀ j, serMul (W.lev c ζ (Eπ ^ h')) g j ∈ Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ (h' - j) := by
    intro j
    have h1 := hgood j
    rw [Pi.add_apply, hγpart j, hneg, Pi.neg_apply, ← hfe j, ← sub_eq_add_neg] at h1
    convert h1 using 1
    rw [MLG.serMul_eq_sum _ hgb j _ le_rfl, MLG.serMul_eq_sum _ hfu j _ le_rfl,
      MLG.serMul_eq_sum _ hfb j _ le_rfl, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hgdef, smul_sub]
  have hH : ∀ j, serMul U g j ∈ Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ (-j) := by
    intro j
    have h1 := hGg (j + h')
    rw [hU, ← MLG.serMul_serMul _ _ hgb, MLG.serMul_X_pow, add_sub_cancel_right] at h1
    convert h1 using 2
    ring
  have hgi := MLI.ind_fil T τ U hU0 hgb hH i
  have e1 : g i = (u ^ i - 1) • f i := by rw [hgdef, sub_smul, one_smul]
  rw [e1] at hgi
  exact (Submodule.smul_mem_iff _ (sub_ne_zero.2 (hu1 i hi))).1 hgi

end Generic

end Formalism.MainNotions.N.Ln34.MLJ

end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.U1linkPf
section
noncomputable section

set_option synthInstance.maxHeartbeats 400000

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

set_option maxHeartbeats 1000000 in
theorem u1link_pf : FirstFrameOfModels := by
  intro D HW F Cm hA hdR hDi hML hMF
  intro l _ hl K LL hG π' E hp9 T₁ T₂ Fm S η m h' up b c α β hIF hHyp
  have hc2 := hHyp.2.1
  have hj2 := hHyp.2.2.2.2.1
  have hηb := hHyp.2.2.2.2.2.1
  have hbS := hHyp.2.2.2.2.2.2.1
  have hh' := hHyp.2.2.2.2.2.2.2.1
  have hm := hHyp.2.2.2.2.2.2.2.2.1
  have hjI : ∀ τ, JumpsInV ((D.loc l).PD K) T₂.ρ τ (Set.Icc (-(h' : ℤ)) h') := by
    intro τ a ha
    have hd := hj2 τ a ha
    have hb := hbS τ
    have hη := hηb τ
    rw [Set.mem_Icc]
    rcases hd with hd | hd
    · unfold deep at hd
      split_ifs at hd <;> (rw [Set.mem_Icc] at hd; constructor <;> omega)
    · rw [Set.mem_Icc] at hd
      constructor <;> omega
  have hM := u3upPf_MK_pos hl K LL hG h' hh'
  have hMF2 := hMF l hl K LL hG π' E hp9 h' hh' c α β hIF T₂ hc2 hjI
  have hML2 := hML l hl K LL hG π' E hp9 h' hh' T₂ hc2 hjI c
  have hR := UniversalLiftFrames.universal_lift_ring_membership D HW F Cm hA hl K LL hG π' E hp9
  have hT := UniversalLiftFrames.embeddings_card_le_degree D HW K LL hG c
  have hτs := hT.choose_spec.1
  have hcard := hT.choose_spec.2
  have hB := UniversalLiftFrames.universal_lift_basis D HW F Cm hA hl K LL hG π' E hp9 T₂ hc2 c
  have hrep := hB.choose_spec.choose_spec.choose_spec.choose
  have hbrep := hB.choose_spec.choose_spec.choose_spec.choose_spec
  refine UniversalLiftFrames.universal_lift_frame (W := (HW l).W K 1 LL hG) (PD := (D.loc l).PD K) (GenPf.isDVR (D.loc l) LL)
    (GenPf.isFractionRing LL) Fm (Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG) π'
    (Formalism.MainNotions.DeltaInvariantLattices.Eat E π') h' (MK l K h') (sigA l (sK l K) h') c S η m up b α β hIF hc2 hjI hMF2 hML2 hM
    hR.1 hR.2.1 hR.2.2.1 hR.2.2.2.1 hR.2.2.2.2.1 hR.2.2.2.2.2.1 hR.2.2.2.2.2.2 hT.choose hτs hcard ?_ ?_ hbS ?_ ?_ ?_ hB.choose hB.choose_spec.choose hB.choose_spec.choose_spec.choose hrep hbrep ?_ ?_ ?_ ?_ ?_ ?_ ?_ hHyp
  · exact fun τ ζ hpt => u3upPf_pt_over D HW hG c ζ τ hpt
  · exact fun τ => Nat.lt_of_le_of_lt (Nat.zero_le _) (hηb τ)
  · exact fun τ ζ hpt => ⟨(UniversalLiftFrames.universal_lift_points D HW F Cm hA hl K LL hG π' E hp9 c τ ζ hpt).1,
      (UniversalLiftFrames.universal_lift_points D HW F Cm hA hl K LL hG π' E hp9 c τ ζ hpt).2.1⟩
  · exact fun τ ζ hpt => (UniversalLiftFrames.universal_lift_points D HW F Cm hA hl K LL hG π' E hp9 c τ ζ hpt).2.2.1
  · exact fun τ ζ hpt => (UniversalLiftFrames.universal_lift_points D HW F Cm hA hl K LL hG π' E hp9 c τ ζ hpt).2.2.2
  · exact fun τ ζ hpt => (UniversalLiftFrames.universal_lift_valuation D HW F Cm hA hl K LL hG π' E hp9 T₂ hc2 c τ ζ hpt).1
  · exact fun τ ζ hpt => (UniversalLiftFrames.universal_lift_valuation D HW F Cm hA hl K LL hG π' E hp9 T₂ hc2 c τ ζ hpt).2
  · exact fun τ ζ ζ' hpt hpt' k => UniversalLiftFrames.universal_lift_valuation_points D HW F Cm hA hl K LL hG π' E hp9 T₂ hc2 c τ ζ ζ' hpt hpt'
      (hB.choose_spec.choose_spec.choose k) (hrep k)
  · exact fun τ ζ hpt hup => ((UniversalLiftFrames.universal_lift_filtration D HW F Cm hA hdR hDi hl K LL hG π' E hp9 T₂ hc2 c τ ζ hpt
      hB.choose hB.choose_spec.choose hB.choose_spec.choose_spec.choose hrep hbrep S η m (up τ) (b τ) (hj2 τ) (hηb τ) (hm τ)).1 hup).1
  · exact fun τ ζ hpt hup => ((UniversalLiftFrames.universal_lift_filtration D HW F Cm hA hdR hDi hl K LL hG π' E hp9 T₂ hc2 c τ ζ hpt
      hB.choose hB.choose_spec.choose hB.choose_spec.choose_spec.choose hrep hbrep S η m (up τ) (b τ) (hj2 τ) (hηb τ) (hm τ)).1 hup).2
  · exact fun τ ζ hpt hup => ((UniversalLiftFrames.universal_lift_filtration D HW F Cm hA hdR hDi hl K LL hG π' E hp9 T₂ hc2 c τ ζ hpt
      hB.choose hB.choose_spec.choose hB.choose_spec.choose_spec.choose hrep hbrep S η m (up τ) (b τ) (hj2 τ) (hηb τ) (hm τ)).2 hup).1
  · exact fun τ ζ hpt hup => ((UniversalLiftFrames.universal_lift_filtration D HW F Cm hA hdR hDi hl K LL hG π' E hp9 T₂ hc2 c τ ζ hpt
      hB.choose hB.choose_spec.choose hB.choose_spec.choose_spec.choose hrep hbrep S η m (up τ) (b τ) (hj2 τ) (hηb τ) (hm τ)).2 hup).2

end Formalism.MainNotions.N.Ln34
end
end

