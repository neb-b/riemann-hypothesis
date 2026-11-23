module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0287
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0124
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0107
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0289
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0262
public import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import GroundTheory.LocalFields.Bundle0007
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0005
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0008
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsOfLayers
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0282
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0285
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0224
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0204
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWeakTopologyWittTiltTensor
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZlTowerGen

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UntiltFrobeniusSeriesOntoAndIndependentZeros
section
open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

theorem GlobalTheory.oneVarCount_onto_independentZeros : ∀ (l : ℕ) [Fact l.Prime] (h : ℕ) (μ : Fin h → ℂ_[l]), 1 ≤ h → μ ≠ 0 → ∃ τ : ℝ, (∀ t : ℂ_[l], ‖t‖ ≤ τ → ∃ y : Fl l, ‖sh y‖ ≤ ‖(l : ℂ_[l])‖ ∧ ‖∑ i : Fin h, μ i * lam h i y - t‖ ≤ ‖(l : ℂ_[l])‖ * τ) ∧ ∃ x : Fin h → Fl l, (∀ a, ‖sh (x a)‖ ≤ ‖(l : ℂ_[l])‖) ∧ (∀ a, ‖∑ i : Fin h, μ i * lam h i (x a)‖ ≤ ‖(l : ℂ_[l])‖ * τ) ∧ ∀ n : Fin h → ℕ, ‖sh (∑ a, n a • x a)‖ ≤ ‖(l : ℂ_[l])‖ ^ l ^ h → ∀ a, l ∣ n a := by
  intro l _ h μ hh hμ
  obtain ⟨sh1, sh0, shmul, shpow, shle, shsurj, shadd, shneg⟩ := _root_.GlobalTheory.PSer.Laws.sh_laws l
  have hl0 : 0 < ‖(l : ℂ_[l])‖ := norm_pos_iff.2 GlobalTheory.RingBasics.p_ne_zero
  have hl1 : ‖(l : ℂ_[l])‖ < 1 := GlobalTheory.RingBasics.norm_p_lt
  have hlD : ∀ D : ℕ, l ^ D ≠ 0 := fun D => (pow_pos (Fact.out : l.Prime).pos D).ne'
  obtain ⟨σ, hσ⟩ := shsurj (l : ℂ_[l]) hl1.le
  obtain ⟨t, D, E, M, a, ρ, ht, hME, ha, haN, hρl, hρ1, hρD, haM, hak, hpoly⟩ :=
    _root_.GlobalTheory.PolyRoot.poly_root_mod_l l h μ σ hh hμ hσ
  have hshv : ∀ u : Fl l, ‖sh (σ * u ^ l ^ D)‖ ≤ ‖(l : ℂ_[l])‖ := by
    intro u
    rw [shmul, shpow, hσ, norm_mul, norm_pow]
    calc ‖(l : ℂ_[l])‖ * ‖sh u‖ ^ l ^ D ≤ ‖(l : ℂ_[l])‖ * 1 := by
          gcongr; exact pow_le_one₀ (norm_nonneg _) (shle u)
      _ = _ := mul_one _
  refine ⟨‖t‖, ?_, ?_⟩
  · intro t' ht'
    have hb : ‖t' / t‖ ≤ 1 := by
      rw [norm_div]; exact div_le_one_of_le₀ ht' (norm_nonneg _)
    obtain ⟨W, hW, hPW⟩ := _root_.GlobalTheory.onto_OC_additive_poly l E (M + h) a hME ha haN (t' / t) hb
    obtain ⟨u, hu⟩ := shsurj W hW
    refine ⟨σ * u ^ l ^ D, hshv u, ?_⟩
    have key := hpoly u
    have e : t * (t' / t) = t' := by field_simp
    rw [hu, hPW, e] at key
    exact key
  · have hρ0 : 0 < ρ := lt_of_lt_of_le hl0 hρl
    obtain ⟨Z, hZc, hZ, hsep⟩ := _root_.GlobalTheory.separated_roots_additive_poly l E M h a ρ hME ha haN hρ0 hρ1 haM hak
    choose! u hu using fun (W : ℂ_[l]) (hW : ‖W‖ ≤ 1) => shsurj W hW
    let v : ℂ_[l] → Fl l := fun W => σ * u W ^ l ^ D
    let K' : AddSubgroup (Fl l) :=
      { carrier := {x | ‖sh x‖ ≤ ‖(l : ℂ_[l])‖ ^ l ^ h}
        zero_mem' := by
          show ‖sh (0 : Fl l)‖ ≤ _
          rw [sh0, norm_zero]; positivity
        add_mem' := by
          intro x y hx hy
          exact (_root_.GlobalTheory.PSer.sh_add_le l _ x y hx hy).2
        neg_mem' := by
          intro x hx
          show ‖sh (-x)‖ ≤ _
          rw [shneg]; exact hx }
    have hchar : ∀ x : Fl l, l • x = 0 := fun x => by
      rw [nsmul_eq_mul, CharP.cast_eq_zero, zero_mul]
    have hsepv : ∀ W ∈ Z, ∀ W' ∈ Z, W ≠ W' → v W - v W' ∉ K' := by
      intro W hW W' hW' hne hmem
      have hsepW := hsep W hW W' hW' hne
      have hvd : v W - v W' = σ * (u W - u W') ^ l ^ D := by
        simp only [v]; rw [sub_pow_char_pow, mul_sub]
      have hmem' : ‖sh (v W - v W')‖ ≤ ‖(l : ℂ_[l])‖ ^ l ^ h := hmem
      rw [hvd, shmul, shpow, hσ, norm_mul, norm_pow, ← hρD] at hmem'
      have hd : ‖sh (u W - u W')‖ ≤ ρ := by
        by_contra hcon
        push_neg at hcon
        have h1 : ρ ^ l ^ D < ‖sh (u W - u W')‖ ^ l ^ D := pow_lt_pow_left₀ hcon hρ0.le (hlD D)
        have h2 := mul_lt_mul_of_pos_left h1 hl0
        linarith
      have h2 := shadd (u W - u W') (u W')
      rw [sub_add_cancel, hu W (hZ W hW).1, hu W' (hZ W' hW').1] at h2
      have e3 : W - W' = (W - sh (u W - u W') - W') + sh (u W - u W') := by ring
      have h3 : ‖W - W'‖ ≤ max ‖W - sh (u W - u W') - W'‖ ‖sh (u W - u W')‖ := by
        rw [e3]; exact IsUltrametricDist.norm_add_le_max _ _
      have h4 : ‖W - W'‖ ≤ ρ := h3.trans (max_le (h2.trans hρl) hd)
      linarith
    obtain ⟨x, hxZ, hx⟩ := _root_.GlobalTheory.ph_a_basis l (Fl l) ℂ_[l] K' h Z v hchar hZc hsepv
    refine ⟨fun b => v (x b), fun b => hshv (u (x b)), ?_, fun n hn => hx n hn⟩
    intro b
    have key := hpoly (u (x b))
    rw [hu _ (hZ _ (hxZ b)).1, (hZ _ (hxZ b)).2, mul_zero, sub_zero] at key
    exact key
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UpperRamificationGroupOneEqTopOfExponentPrime
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem ringChar_residue_eq_of_ordIs (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (p e : ℕ) (hp : p.Prime) (he : 0 < e) (h : OrdIs F p e) :
    ringChar 𝓀[F] = p := by
  have hnu : ¬ IsUnit (p : 𝒪[F]) := by
    intro hu
    have := (IsDiscreteValuationRing.addVal_eq_zero_of_unit (hu.unit))
    unfold OrdIs at h
    simp at this
    rw [this] at h
    norm_cast at h
    omega
  have hm : (p : 𝒪[F]) ∈ IsLocalRing.maximalIdeal 𝒪[F] := hnu
  have h0 : ((p : ℕ) : 𝓀[F]) = 0 := by
    rw [← map_natCast (IsLocalRing.residue 𝒪[F]), IsLocalRing.residue_eq_zero_iff]
    exact hm
  have hd : ringChar 𝓀[F] ∣ p := (ringChar.spec 𝓀[F] p).mp h0
  rcases (Nat.dvd_prime hp).mp hd with h1 | h1
  · exact absurd h1 CharP.ringChar_ne_one
  · exact h1

theorem upperRamificationGroup_one_eq_top_of_exponent :
    ∀ (F M : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Field M]
      [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M] [Algebra F M] [ValuativeExtension F M]
      [FiniteDimensional F M] [IsGalois F M] (p e : ℕ), p.Prime → 0 < e → OrdIs F p e →
      upperRamificationGroup F M 0 = ⊤ → (∀ σ : M ≃ₐ[F] M, σ ^ p = 1) → upperRamificationGroup F M 1 = ⊤ := by
  intro F M _ _ _ _ _ _ _ _ _ _ _ _ p e hp he hord h0 hexp
  rw [upperRamificationGroup_zero] at h0
  have hchar := ringChar_residue_eq_of_ordIs F p e hp he hord
  have hcop := coprime_card_lowerRamificationGroup_zero_quotient F M
  rw [hchar] at hcop
  have h1 : lowerRamificationGroup F M 1 = ⊤ := by
    rw [eq_top_iff]
    intro σ _
    have hσ0 : σ ∈ lowerRamificationGroup F M 0 := by rw [h0]; trivial
    set q : lowerRamificationGroup F M 0 ⧸
        (lowerRamificationGroup F M 1).subgroupOf (lowerRamificationGroup F M 0) :=
      QuotientGroup.mk ⟨σ, hσ0⟩ with hq
    have hqp : q ^ p = 1 := by
      rw [hq, ← QuotientGroup.mk_pow]
      have : (⟨σ, hσ0⟩ : lowerRamificationGroup F M 0) ^ p = 1 := Subtype.ext (by simpa using hexp σ)
      rw [this, QuotientGroup.mk_one]
    have hqc : q ^ Nat.card (lowerRamificationGroup F M 0 ⧸
        (lowerRamificationGroup F M 1).subgroupOf (lowerRamificationGroup F M 0)) = 1 := pow_card_eq_one'
    have hg : q ^ Nat.gcd _ p = 1 := pow_gcd_eq_one.mpr ⟨hqc, hqp⟩
    rw [hcop, pow_one, hq, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hg
    exact hg
  have hphi0 : herbrandPhi F M 0 = 0 := by simp [herbrandPhi]
  have hphi1 : herbrandPhi F M 1 = 1 := by
    have := herbrandPhi_of_mem_Icc (K := F) (L := M) 0 (u := 1) (by norm_num)
    have h1' : lowerRamificationGroup F M (((0 : ℕ) : ℤ) + 1) = ⊤ := by simpa using h1
    rw [h1', Subgroup.relIndex_top_left] at this
    simpa [hphi0] using this
  rw [← hphi1, upperRamificationGroup_herbrandPhi, ← Nat.cast_one, lowerRamificationGroupReal_natCast]
  simpa using h1
end GlobalTheory.PMon.Ram
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachHypothesisCrystallineLattices
section
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations

noncomputable section

namespace GlobalTheory.WachHyp

theorem jump_mem (S : LocalSituation.Sit) (T : LocLat S.G S.Qp S.LL S.O) (τ : S.K →ₐ[S.Qp] S.LL) (a : ℤ)
    (h : IsJumpV S.PD T.ρ τ a) : a ∈ LocalSituation.Jset S T := by
  intro e
  apply h
  unfold FildR DdRE
  rw [inf_right_comm, e, inf_right_comm]

theorem jumpsLet_const (S : LocalSituation.Sit) (Y : LocLat S.G S.Qp S.LL S.O) (M0 h0 : ℕ)
    (hj : ∀ a ∈ LocalSituation.Jset S Y, -(M0 : ℤ) ≤ a ∧ a ≤ h0) :
    DeltaInvariantLattices.JumpsLet S.W Y (fun _ => M0) (fun _ => h0) := by
  intro τ i _ a ha
  exact Set.mem_Icc.2 (hj a (jump_mem S Y τ a ha))

theorem nBasis (S : LocalSituation.Sit) (E : S.Comparison₂) (he : DeltaInvariantLattices.WachEtaleComparison S.W E) (Y : LocLat S.G S.Qp S.LL S.O)
    (hY : IsCrys S.PD Y.ρ) : LocalSituation.NBasis S E Y (S.W.N Y) := by
  obtain ⟨⟨⟨r, b, hbN, huniq, hRW⟩, -⟩, -⟩ := he Y hY
  let v : Fin r → ↥(S.W.N Y) := fun j => ⟨b j, hbN j⟩
  have hli : LinearIndependent (LetA S.O S.n) v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have h0 : ((∑ j, g j • v j : ↥(S.W.N Y)) : S.W.DD Y) = 0 := by rw [hg]; rfl
    have h0' : (0 : S.W.DD Y) = ∑ j, g j • b j := by
      rw [← h0]; simp [v]
    obtain ⟨a, -, ha⟩ := huniq 0 (S.W.N Y).zero_mem
    have e1 := ha g h0'
    have e2 := ha (fun _ => 0) (by simp)
    intro j
    rw [e1, ← e2]
  have hsp : ⊤ ≤ Submodule.span (LetA S.O S.n) (Set.range v) := by
    rintro ⟨x, hx⟩ -
    obtain ⟨a, ha, -⟩ := huniq x hx
    have : (⟨x, hx⟩ : ↥(S.W.N Y)) = ∑ j, a j • v j := by
      apply Subtype.ext
      simp [v, ha]
    rw [this]
    exact Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩))
  refine ⟨Fin r, inferInstance, Module.Basis.mk hli hsp, ?_, ?_⟩
  · simp only [Module.Basis.mk_apply, v]
    rw [Fintype.linearIndependent_iff]
    intro c hc
    obtain ⟨a, -, ha⟩ := hRW 0
    have e1 := ha c hc.symm
    have e2 := ha (fun _ => 0) (by simp)
    intro j
    rw [e1, ← e2]
  · simp only [Module.Basis.mk_apply, v]
    rw [eq_top_iff]
    rintro y -
    obtain ⟨c, hc, -⟩ := hRW y
    rw [hc]
    exact Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩))

theorem wClauses (S : LocalSituation.Sit) (E : S.Comparison₂) (h1 : DeltaInvariantLattices.WachLatticeFree S.W) (h5 : DeltaInvariantLattices.P5W S.W)
    (he : DeltaInvariantLattices.WachEtaleComparison S.W E) (Y : LocLat S.G S.Qp S.LL S.O) (M0 h0 : ℕ) (hY : IsCrys S.PD Y.ρ)
    (hj : ∀ a ∈ LocalSituation.Jset S Y, -(M0 : ℤ) ≤ a ∧ a ≤ h0) :
    LocalSituation.WClauses S E Y M0 h0 (S.W.N Y) := by
  have hf := h1 Y hY
  have hp := h5 Y (fun _ => M0) (fun _ => h0) hY (jumpsLet_const S Y M0 h0 hj)
  have hNl : ∀ i, S.W.Nl Y i ≤ S.W.N Y := fun i => by
    rw [hf.1]; exact le_iSup (fun j => S.W.Nl Y j) i
  refine ⟨nBasis S E he Y hY, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    rw [hf.1] at hx
    refine Submodule.iSup_induction (fun j => S.W.Nl Y j)
      (motive := fun x => S.W.Q ^ M0 • S.W.φD Y x ∈ S.W.N Y) hx ?_ ?_ ?_
    · intro j y hy
      exact hp.1 (j + 1) y (by simpa using hy)
    · simp
    · intro y z hy hz
      simp only [map_add (f := _), smul_add]
      exact add_mem hy hz
  · intro y hy
    rw [hf.1] at hy
    refine Submodule.iSup_induction (fun j => S.W.Nl Y j)
      (motive := fun y => S.W.Q ^ h0 • y ∈ LocalSituation.phiSpan S Y (S.W.N Y)) hy ?_ ?_ ?_
    · intro j y hy
      exact Submodule.span_mono (Set.image_mono (hNl (j - 1))) (hp.2.1 j y hy)
    · simp
    · intro y z hy hz
      simp only [smul_add]
      exact add_mem hy hz
  · intro g _ x hx
    exact S.W.N_Γ Y _ x hx
  · intro g _ x hx
    obtain ⟨y, hy, e⟩ := S.W.N_π Y (S.W.resΓ g) x hx
    rw [e]
    exact Submodule.smul_mem_smul (Ideal.subset_span rfl) hy
  · intro f x hx
    exact S.W.map_N f hY hY x hx

theorem hypW_crystalline : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), DeltaInvariantLattices.UsedLocalConclusion D HW F Cm → DeltaInvariantLattices.ConclusionE D HW F → CrysOnCond D HW F → ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), EmbeddingTypeJumps.WachHypothesisLocal (LocalSituation.sit D.loc HW l (D.locA l) K s LL h) ((F l).E K s LL h).tie := by
  intro D HW F Cm hU hE hC l _ K s LL h Y M0 h0 hY hj
  have hT := hU.1 l K s LL h
  exact LocalSituation.HypW_of_rec (hC l K s LL h Y hY) hj
    (wClauses _ _ hT.1 hT.2.2.2.2.1 (hE.1 l K s LL h) Y M0 h0 hY hj)

end GlobalTheory.WachHyp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeFreeOfCrystalline
section
open PowerSeries Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL

namespace GlobalTheory.HWL


open PowerSeries TensorProduct in
theorem _root_.GlobalTheory.HWL.mem_smul_of_projective_comp {D A M : Type} [CommRing D] [IsDomain D] [CommRing A]
    [AddCommGroup M] [Module A M] (f : D⟦X⟧ →+* A)
    (hp : @Module.Projective D⟦X⟧ _ M _ (Module.compHom _ f)) (c : D) (hc : c ≠ 0) {a b : A}
    (ha : f (C c) = a) (hb : f X = b) (x y : M) (h : a • x = b • y) : ∃ z : M, x = b • z := by
  letI : Module D⟦X⟧ M := Module.compHom M f
  obtain ⟨z, hz⟩ := _root_.GlobalTheory.WachFree.mem_X_smul_of_projective c hc x y (by
    change f (C c) • x = f X • y
    rw [ha, hb]
    exact h)
  refine ⟨z, ?_⟩
  rw [hz]
  change f X • z = b • z
  rw [hb]

open PowerSeries TensorProduct in
private theorem isSMulRegular_of_projective_powerSeries_comp_lemma {D A M : Type} [CommRing D]
    [IsDomain D] [CommRing A] [AddCommGroup M] [Module A M] (f : D⟦X⟧ →+* A)
    (hp : @Module.Projective D⟦X⟧ _ M _ (Module.compHom _ f)) {b : A} (hb : f X = b) :
    IsSMulRegular M b := by
  letI : Module D⟦X⟧ M := Module.compHom M f
  have hreg := Module.Flat.isSMulRegular_of_nonZeroDivisors (R := D⟦X⟧) (M := M)
    (mem_nonZeroDivisors_of_ne_zero (X_ne_zero : (X : D⟦X⟧) ≠ 0))
  intro x y h
  apply hreg
  change f X • x = f X • y
  rw [hb]
  exact h


open PowerSeries TensorProduct in
set_option maxHeartbeats 8000000 in
theorem _root_.GlobalTheory.HWL.lattice_free : ∀ (l : ℕ) [Fact l.Prime] (P : _root_.Formalism.BasicNotions.LocPrime l) (AI : _root_.Formalism.BasicNotions.LocAinf l P) (K : _root_.Formalism.BasicNotions.Loc.FinExt l) (s : ℕ) (LL : _root_.Formalism.BasicNotions.Loc.FinExt l), _root_.Formalism.BasicNotions.Loc.Good K s LL → ∀ (Γ : _root_.GlobalTheory.HWL.GamS P K s LL) (R : _root_.GlobalTheory.HWL.WSer Γ) (I : _root_.GlobalTheory.HWL.IoS AI R), _root_.GlobalTheory.HWL.IoW I → ∀ (E : _root_.GlobalTheory.HWL.WEt I) (Mo : _root_.GlobalTheory.HWL.NS E) (T : _root_.Formalism.BasicNotions.LocLat ↥(_root_.Formalism.BasicNotions.Loc.GK K) ℚ_[l] ↥LL.1 ↥(_root_.Formalism.BasicNotions.Loc.OL LL)), _root_.Formalism.WeaklyAdmissibleFiltrations.IsCrys (P.PD K) T.ρ → Nonempty (Module.Basis (Fin (Module.finrank ↥(_root_.Formalism.BasicNotions.Loc.OL LL) ↥T.L.T)) (_root_.Formalism.BasicNotions.LetA ↥(_root_.Formalism.BasicNotions.Loc.OL LL) (Module.finrank ℚ_[l] ↥(_root_.Formalism.BasicNotions.Loc.K0 K))) ↥(Mo.N T)) := by
  set_option synthInstance.maxHeartbeats 400000 in
    intro l _ P AI K s LL _ Γ R I _ E Mo T hc
    obtain ⟨_, -, hl⟩ := _root_.GlobalTheory.FinExtIntegers.dvr_complete LL
    have hfree := E.DD_free T
    haveI := hfree.1
    haveI : FiniteDimensional ℚ_[l] ↥(_root_.Formalism.BasicNotions.Loc.K0 K) := by
      haveI := K.2
      have hle : _root_.Formalism.BasicNotions.Loc.K0 K ≤ ↑K := inf_le_left
      exact Module.Finite.of_injective (IntermediateField.inclusion hle).toLinearMap
        (IntermediateField.inclusion hle).toRingHom.injective
    haveI : NeZero (Module.finrank ℚ_[l] ↥(_root_.Formalism.BasicNotions.Loc.K0 K)) := ⟨Module.finrank_pos.ne'⟩
    haveI : Module.Finite _ (Mo.N T) :=
      Module.Finite.iff_fg.mpr (Mo.N_fg T)
    have hl0 : (l : ℤ_[l]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero
    have hzX : _root_.Formalism.BasicNotions.Loc.zlA LL (Module.finrank ℚ_[l] ↥(_root_.Formalism.BasicNotions.Loc.K0 K)) X = fun _ => X := by
      ext1; simp [_root_.Formalism.BasicNotions.Loc.zlA]
    have hzC : _root_.Formalism.BasicNotions.Loc.zlA LL (Module.finrank ℚ_[l] ↥(_root_.Formalism.BasicNotions.Loc.K0 K)) (C (l : ℤ_[l])) =
        fun _ => C (l : _root_.Formalism.BasicNotions.Loc.OL LL) := by
      ext1; simp [_root_.Formalism.BasicNotions.Loc.zlA]
    have key := _root_.GlobalTheory.WachFree.basis_of_regular
      (ι := ZMod (Module.finrank ℚ_[l] ↥(_root_.Formalism.BasicNotions.Loc.K0 K)))
      (O := ↥(_root_.Formalism.BasicNotions.Loc.OL LL))
      (N := ↥(Mo.N T)) (E := R.EE) (D := E.DD T) R.EE_inj
      (Mo.N T).subtype (Mo.N_base T hc) (l : _root_.Formalism.BasicNotions.Loc.OL LL) ?_ hl ?_ ?_
    · rwa [hfree.2] at key
    · intro h0
      haveI : CharZero ↥LL.1 :=
        charZero_of_injective_algebraMap (algebraMap ℚ_[l] ↥LL.1).injective
      have hcast : ((l : _root_.Formalism.BasicNotions.Loc.OL LL) : ↥LL.1) = 0 := by rw [h0]; rfl
      push_cast at hcast
      exact (Fact.out : l.Prime).ne_zero (by exact_mod_cast hcast)
    · exact isSMulRegular_of_projective_powerSeries_comp_lemma _ (Mo.N_proj T) hzX
    · intro x y h
      exact _root_.GlobalTheory.HWL.mem_smul_of_projective_comp (_root_.Formalism.BasicNotions.Loc.zlA LL _) (Mo.N_proj T)
        (l : ℤ_[l]) hl0 hzC hzX x y h

end GlobalTheory.HWL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLetterRingFrobeniusDecomposition
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

namespace GlobalTheory.NL.PhiDec

theorem phi_dec : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ a : AA K LL, ∃ c : Fin l → AA K LL, a = ∑ j : Fin l, (fun _ => ((1 : PowerSeries ↥(OL LL)) + PowerSeries.X) ^ (j : ℕ) : AA K LL) * W.φA (c j) := by
  intro D HW l _ K s LL h W a
  obtain ⟨χ, -, hφ, -⟩ := GlobalTheory.NL.CycRing.rings_cyclotomic D HW l K s LL h
  obtain ⟨hdvr, hcomp, hl0, hlu, -⟩ := GlobalTheory.Per.integers_completeDVR l LL
  choose z hz using fun i : Let K => (GlobalTheory.Cyc.phi_free l ↥(OL LL) hl0 hlu (a i)).exists
  refine ⟨fun j i => z (i + 1) j, ?_⟩
  funext i
  rw [Finset.sum_apply]
  have hi : a i = a (i - 1 + 1) := by rw [sub_add_cancel]
  rw [hi, hz]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.mul_apply, LocWach.φA, letφ, AlgHom.pi_apply, AlgHom.comp_apply, Pi.evalAlgHom_apply]
  show _ = _ * ((HW l).W K s LL h).φ₀ _
  rw [hφ]

end GlobalTheory.NL.PhiDec
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeaklySmall
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.WeakClosed
open scoped Topology PowerSeries.WithPiTopology
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

noncomputable section

namespace GlobalTheory.WeakClosed

theorem lt_of_mem_span_pow {l : ℕ} [Fact l.Prime] (ϖ : OCb l) (hϖ : ¬ IsUnit ϖ)
    (hdiv : ∀ a : OCb l, a ≠ 0 → ∃ m : ℕ, a ∣ ϖ ^ m) (c : Cb l) (hc : c ≠ 0) :
    ∃ m : ℕ, ∀ x ∈ Ideal.span {ϖ ^ m},
      (cbValued l).v (algebraMap (OCb l) (Cb l) x) < (cbValued l).v c := by
  letI := cbValued l
  have hle : ∀ x y : Cb l, Valued.v x ≤ Valued.v y ↔
      ∃ e : OCb l, algebraMap (OCb l) (Cb l) e * y = x := by
    intro x y
    change (∃ e : OCb l, e • y = x) ↔ _
    simp only [Algebra.smul_def]
  have hinj := IsFractionRing.injective (OCb l) (Cb l)
  obtain ⟨a, d, hd, rfl⟩ := IsFractionRing.div_surjective (OCb l) c
  have hd0 : algebraMap (OCb l) (Cb l) d ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd
  have ha : a ≠ 0 := by
    rintro rfl
    simp at hc
  obtain ⟨m₀, b, hb⟩ := hdiv a ha
  refine ⟨m₀ + 1, fun x hx => ?_⟩
  obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.1 hx
  change Valued.v _ < Valued.v _
  rw [← not_le, hle]
  rintro ⟨e, he⟩
  rw [eq_div_iff hd0] at he
  have he' : e * (t * ϖ ^ (m₀ + 1)) * d = a := hinj (by rw [map_mul, map_mul]; exact he)
  apply hϖ
  have h0 : a * (1 - ϖ * (e * t * d * b)) = 0 := by
    linear_combination (-1 : OCb l) * he' + e * t * d * ϖ * hb
  rcases mul_eq_zero.1 h0 with h | h
  · exact absurd h ha
  · exact isUnit_iff_exists_inv.2 ⟨e * t * d * b, (sub_eq_zero.1 h).symm⟩

theorem weakly_small : ∀ {l : ℕ} [Fact l.Prime] (ϖ : OCb l), ¬ IsUnit ϖ →
    (∀ a : OCb l, a ≠ 0 → ∃ m : ℕ, a ∣ ϖ ^ m) →
      (letI := wTop l
       ∀ U ∈ 𝓝 (0 : WCb l), ∃ N m : ℕ, ∀ w : Ainf l,
         (∀ n < N, w.coeff n ∈ Ideal.span {ϖ ^ m}) → inclW l w ∈ U) := by
  intro l _ ϖ hϖ hdiv
  letI := wTop l
  letI := cbTop l
  intro U hU
  rw [nhds_induced] at hU
  obtain ⟨t, ht, htU⟩ := Filter.mem_comap.1 hU
  rw [nhds_pi, Filter.mem_pi'] at ht
  obtain ⟨I, V, hV, hIV⟩ := ht
  have key : ∀ i, ∃ m : ℕ, ∀ x ∈ Ideal.span {ϖ ^ m}, algebraMap (OCb l) (Cb l) x ∈ V i := by
    intro i
    have h := hV i
    rw [WittVector.zero_coeff] at h
    obtain ⟨c, hc, hcV⟩ := (@GlobalTheory.WeakTop.mem_nhds_iff_lt _ _ _ _ (cbValued l) _ _).1 h
    obtain ⟨m, hm⟩ := lt_of_mem_span_pow ϖ hϖ hdiv c hc
    exact ⟨m, fun x hx => hcV (by simpa using hm x hx)⟩
  choose M hM using key
  refine ⟨I.sup id + 1, I.sup M, fun w hw => htU (hIV ?_)⟩
  intro i hi
  show (inclW l w).coeff i ∈ V i
  simp only [inclW, WittVector.map_coeff]
  apply hM i
  have hlt : i < I.sup id + 1 := Nat.lt_succ_of_le (Finset.le_sup (f := id) hi)
  exact Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow ϖ (Finset.le_sup hi)) (hw i hlt)

end GlobalTheory.WeakClosed
end
end

