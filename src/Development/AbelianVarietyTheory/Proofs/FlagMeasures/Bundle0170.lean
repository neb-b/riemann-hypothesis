module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0008
public import Formalism.LocalToGlobal.HermitianForms.Bundle0002
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DualLatticeLocalCharacterization
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0097
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0095
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairCommonUnipotentStabiliserSummary
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairInnerLatticesUnimodularPrimitive
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0124
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0126
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0125
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarInvVolumeMiddleLayerEichlerLe
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.Bundle0001
public import Formalism.HarderNarasimhan.ShiftInvariance
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0121
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0138
public import Formalism.RealPlaceAnalysis.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SplitPlaceDualQuotientComponentsIff
section
open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

namespace GlobalTheory.St.G.DualComp

section Form

variable {A : Type} [CommRing A] {n : ℕ} (σ : A →+* A) (J : Matrix (Fin n) (Fin n) A)

theorem expand (hσ : ∀ a, σ (σ a) = a) (x y : Fin n → Fin n → A)
    (hd : ∀ i j, hform σ J (x i) (y j) = if i = j then 1 else 0) (w : Fin n → A) :
    w = ∑ i, σ (hform σ J w (y i)) • x i := by
  let X : Matrix (Fin n) (Fin n) A := fun i k => σ (x i k)
  let Y : Matrix (Fin n) (Fin n) A := fun k j => ∑ l, J k l * y j l
  have h1 : X * Y = 1 := by
    ext i j
    rw [Matrix.one_apply, ← hd i j, Matrix.mul_apply]
    simp only [X, Y, hform, Finset.mul_sum, mul_assoc]
  have h2 : Y * X = 1 := mul_eq_one_comm.1 h1
  funext k
  have h3 : σ (w k) = ∑ i, hform σ J w (y i) * σ (x i k) := by
    have h4 : ∀ i, hform σ J w (y i) = ∑ l, σ (w l) * Y l i := by
      intro i
      simp only [Y, hform, Finset.mul_sum, mul_assoc]
    have h5 : ∀ l, ∑ i, σ (w l) * Y l i * σ (x i k) = σ (w l) * (Y * X) l k := by
      intro l
      rw [Matrix.mul_apply, Finset.mul_sum]
      simp only [mul_assoc, X]
    simp only [h4, Finset.sum_mul]
    rw [Finset.sum_comm]
    simp only [h5, h2, Matrix.one_apply]
    simp
  rw [← hσ (w k), h3]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, hσ, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

theorem conj_symm (hσ : ∀ a, σ (σ a) = a) (hJ : ∀ i j, σ (J i j) = J j i) (x y : Fin n → A) :
    hform σ J y x = σ (hform σ J x y) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hform, map_sum, map_mul, hσ, hJ]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

end Form

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
  (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E)

theorem mem_loc_of_pair (hJ : J.det ≠ 0) (L : Submodule (𝓞 E) (Fin n → E)) (hL : IsLat L)
    (v : HeightOneSpectrum (𝓞 F))
    (hσ : ∀ a, sigR σ (v.adicCompletion F) (sigR σ (v.adicCompletion F) a) = a)
    (w : Fin n → E ⊗[F] v.adicCompletion F)
    (hw : ∀ y ∈ loc v (dualL σ J L), hR σ J (v.adicCompletion F) w y ∈ intV E v) : w ∈ loc v L := by
  obtain ⟨x, yb, s, hs, hxL, hdu, -, hyL⟩ := Dual.exists_dual_basis σ J hJ L hL v
  obtain ⟨us, husO, hus⟩ := PI.SelfDualLoc.W.unitLoc F E v s hs
  have husO' : us ∈ intV E v := husO
  have hus' : inclE (F := F) (v.adicCompletion F) (algebraMap F E (s : F)) * us = 1 := hus
  have hy : ∀ j, (fun i => inclE (F := F) (v.adicCompletion F) (yb j i)) ∈ loc v (dualL σ J L) := by
    intro j
    have hg : (fun i => inclE (F := F) (v.adicCompletion F)
        ((algebraMap F E (s : F) • yb j) i)) ∈ loc v (dualL σ J L) :=
      Submodule.subset_span ⟨_, hyL j, rfl⟩
    have hmem := Submodule.smul_mem _ (⟨us, husO'⟩ : intV E v) hg
    rw [Subring.smul_def] at hmem
    convert hmem using 1
    ext i
    simp only [Pi.smul_apply, smul_eq_mul, map_mul]
    linear_combination (-(inclE (F := F) (v.adicCompletion F) (yb j i))) * hus'
  have he := expand (sigR σ (v.adicCompletion F)) (J.map (inclE (F := F) (v.adicCompletion F))) hσ
    (fun j i => inclE (F := F) (v.adicCompletion F) (x j i))
    (fun j i => inclE (F := F) (v.adicCompletion F) (yb j i))
    (fun i j => by
      have h4 := Dual.hR_incl σ J (v.adicCompletion F) (x i) (yb j)
      unfold hR at h4
      rw [h4, hdu]
      split_ifs <;> simp) w
  rw [he]
  refine Submodule.sum_mem _ fun j _ => ?_
  have hg : (fun i => inclE (F := F) (v.adicCompletion F) (x j i)) ∈ loc v L :=
    Submodule.subset_span ⟨_, hxL j, rfl⟩
  exact Submodule.smul_mem _ (⟨_, Dual.sig_int σ _ _ _ (hw _ (hy j))⟩ : intV E v) hg

end GlobalTheory.St.G.DualComp

namespace GlobalTheory.St.G

theorem dual_components_iff : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHerm (cm.sig : E →+* E) J → J.det ≠ 0 → ∀ (T f : ℕ) (L : Submodule (𝓞 E) (Fin n → E)), T.Prime → SplitsIn E T → Module.finrank ℚ E = 2 * f → TLat cm.sig J T f L → ∀ (v : HeightOneSpectrum (𝓞 F)), (T : 𝓞 F) ∈ v.asIdeal → ∀ (sp : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F), (∀ x, sp (sigR cm.sig (v.adicCompletion F) x) = swapR _ (sp x)) → (∀ a : v.adicCompletion F, sp ((1 : E) ⊗ₜ[F] a) = (a, a)) → ((∀ y ∈ loc v (dualL cm.sig J L), ∃ z ∈ loc v L, ∀ b, (sp (z b)).1 = (sp (y b)).1) ↔ (∀ y ∈ loc v (dualL cm.sig J L), ∃ z ∈ loc v L, ∀ b, (sp (z b)).2 = (sp (y b)).2)) := by
  intro F E _ _ _ _ _ _ cm n J hJ hdet T f L _ _ _ hT v _ sp hsig hdiag
  have hint : ∀ x, x ∈ intV E v ↔
      (sp x).1 ∈ v.adicCompletionIntegers F ∧ (sp x).2 ∈ v.adicCompletionIntegers F :=
    split_integral_local F E v sp hdiag
  have hσ : ∀ a, sigR cm.sig (v.adicCompletion F) (sigR cm.sig (v.adicCompletion F) a) = a := by
    intro a
    apply sp.injective
    rw [hsig, hsig]
    rfl
  have hJ' : ∀ i j, sigR cm.sig (v.adicCompletion F) (J.map (inclE (F := F) (v.adicCompletion F)) i j) =
      J.map (inclE (F := F) (v.adicCompletion F)) j i := by
    intro i j
    have h1 : cm.sig (J i j) = J j i := congrFun (congrFun hJ j) i
    rw [Matrix.map_apply, Matrix.map_apply, ← h1]
    exact PI.SelfDualLoc.W.sigR_inclE cm.sig _ _
  have h1 : ∀ x y : Fin n → E ⊗[F] v.adicCompletion F, (sp (hR cm.sig J (v.adicCompletion F) x y)).1 =
      ∑ i, ∑ j, (sp (x i)).2 * (sp (inclE (F := F) (v.adicCompletion F) (J i j))).1 * (sp (y j)).1 := by
    intro x y
    unfold hR hform
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Prod.fst_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Prod.fst_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, map_mul, hsig]
    rfl
  have h2 : ∀ x y : Fin n → E ⊗[F] v.adicCompletion F, (sp (hR cm.sig J (v.adicCompletion F) x y)).2 =
      ∑ i, ∑ j, (sp (x i)).1 * (sp (inclE (F := F) (v.adicCompletion F) (J i j))).2 * (sp (y j)).2 := by
    intro x y
    unfold hR hform
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Prod.snd_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Prod.snd_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, map_mul, hsig]
    rfl
  have hp : ∀ y ∈ loc v (dualL cm.sig J L), ∀ z ∈ loc v L, hR cm.sig J (v.adicCompletion F) y z ∈ intV E v := by
    intro y hy z hz
    have h := Dual.sig_int cm.sig _ _ _ (Dual.fwd cm.sig J _ _ L y hy z hz)
    unfold hR at h ⊢
    rwa [DualComp.conj_symm _ _ hσ hJ' z y]
  constructor
  · intro h y hy
    refine ⟨fun b => sp.symm (0, (sp (y b)).2), ?_, fun b => by rw [sp.apply_symm_apply]⟩
    refine DualComp.mem_loc_of_pair cm.sig J hdet L hT.1 v hσ _ fun w hw => ?_
    obtain ⟨z, hz, e⟩ := h w hw
    have h3 := ((hint _).1 (hp y hy z hz)).1
    rw [hint, h1, h2]
    rw [h1] at h3
    simp only [sp.apply_symm_apply, zero_mul, Finset.sum_const_zero, ← e]
    exact ⟨h3, zero_mem _⟩
  · intro h y hy
    refine ⟨fun b => sp.symm ((sp (y b)).1, 0), ?_, fun b => by rw [sp.apply_symm_apply]⟩
    refine DualComp.mem_loc_of_pair cm.sig J hdet L hT.1 v hσ _ fun w hw => ?_
    obtain ⟨z, hz, e⟩ := h w hw
    have h3 := ((hint _).1 (hp y hy z hz)).2
    rw [hint, h1, h2]
    rw [h2] at h3
    simp only [sp.apply_symm_apply, zero_mul, Finset.sum_const_zero, ← e]
    exact ⟨zero_mem _, h3⟩

end GlobalTheory.St.G
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SplitTermWeightLeNearReferenceLattice
section
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.DegCnt.Weight

theorem invVol_three {G : Type} [Group G] (R M Z A B : Subgroup G) (hM : M ≤ R) (hZ : Z ≤ M) (hA : A ≤ R) (hB : B ≤ R)
    (nM : ∀ s ∈ R, ∀ t ∈ M, s * t * s⁻¹ ∈ M) (nZ : ∀ s ∈ R, ∀ t ∈ Z, s * t * s⁻¹ ∈ Z)
    (h1 : A.relIndex B ≠ 0) (h2 : B.relIndex A ≠ 0)
    (h3 : (A ⊓ M).relIndex (B ⊓ M) ≠ 0) (h4 : (B ⊓ M).relIndex (A ⊓ M) ≠ 0) :
    GlobalTheory.HL.invVol A B = GlobalTheory.HL.invVol (A ⊓ Z) (B ⊓ Z) * GlobalTheory.HL.invVol ((A ⊓ M) ⊔ Z) ((B ⊓ M) ⊔ Z) *
      GlobalTheory.HL.invVol (A ⊔ M) (B ⊔ M) := by
  rw [(GlobalTheory.IndexProd.invVol_eq_inf_mul_sup_and_mono G R M A B hM hA hB nM h1 h2).1,
    (GlobalTheory.IndexProd.invVol_eq_inf_mul_sup_and_mono G M Z (A ⊓ M) (B ⊓ M) hZ inf_le_right inf_le_right
      (fun s hs t ht => nZ s (hM hs) t ht) h3 h4).1,
    inf_assoc, inf_assoc, inf_eq_right.mpr hZ]

theorem invVol_nonneg {G : Type} [Group G] (A B : Subgroup G) : 0 ≤ GlobalTheory.HL.invVol A B := by
  unfold GlobalTheory.HL.invVol
  positivity

theorem om_le : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → ∀ 𝔠 : Ideal (𝓞 K), 𝔠 ≠ ⊥ → (∀ x ∈ 𝔠, ∃ y ∈ 𝔠, (y : K) = star (x : K)) → (∀ x ∈ 𝔠, (N.T : 𝓞 K) ∣ x) → (∀ (l : ℕ) (hl : l ≤ r + 1), l ≤ N.j → Dl N.F N.F' l hl ≠ 0 → ∀ x ∈ 𝔠, ∀ y ∈ ipow N.𝔡 (2 * ∑ a ∈ Finset.range l, ((r : ℤ) - a)), (x : K) * y / Dl N.F N.F' l hl ∈ (1 : Submodule (𝓞 K) K) ∧ (x : K) * y / star (Dl N.F N.F' l hl) ∈ (1 : Submodule (𝓞 K) K)) → ∀ e : ℕ, N.Split Λ → N.Near (𝔠 ^ e) Λ → N.om Λ ≤ (N.bI Λ : ℝ) ^ Module.finrank K N.Wt * N.Del ^ r * (Ideal.absNorm 𝔠 : ℝ) ^ (2 * (3 * e + 11) * (2 * r + 1) ^ 2) := by
  intro K V _ _ _ _ _ _ _ _ H hK r N g Λ hg hT 𝔠 hc hs hTd hD e hSp hNe
  obtain ⟨-, -, nM, nZ, hnil⟩ := GlobalTheory.UnipStab.common_unipotent_stabiliser K V H hK r N
  obtain ⟨-, -, -, -, hRef, -⟩ := _root_.GlobalTheory.DegCnt.InnerLat.main K V H hK r N g Λ hg hT
  obtain ⟨-, hg0, hi0, -, hgi, -⟩ := _root_.GlobalTheory.DegCnt.FixIdx.main K V H hK r N g Λ hg hT
  have hTop := _root_.GlobalTheory.DegCnt.invVol_top_layer_le K V H hK r N g Λ hg hT 𝔠 hc hs hTd hD e hSp hNe
  have hBot := _root_.GlobalTheory.DegCnt.WtSkew.invVol_skew_le K V H hK r N g Λ hg hT 𝔠 hc hs hTd hD e hSp hNe
  have hMid := _root_.GlobalTheory.DegCnt.MidLayer.invVol_mid_layer_le K V H hK r N g Λ hg hT hSp
  have hΛ : Submodule.IsFullLattice K Λ := by
    have h := hT.1.1.1
    unfold IsLatMod at h
    obtain ⟨⟨M, hM, hE⟩, hsp⟩ := h
    have hfg : Λ.FG := by
      rw [hE, rs, Submodule.restrictScalars_bot, sup_bot_eq]
      exact hM
    letI : Submodule.IsLattice K Λ := Submodule.IsLattice.of_fg K hfg
    exact ⟨hsp⟩
  have hRefFull : Submodule.IsFullLattice K (N.Ref (latL N.F N.F' Λ)) := by
    letI := hRef
    obtain ⟨_, _, hC, _, hWn, hUp, _, _, _, _, _, hPi⟩ :=
      GlobalTheory.T.hermFramePairNormalForm_geometry_summary K V H hK r N
    have hspan : Submodule.span K (N.Ref (latL N.F N.F' Λ) : Set V) = ⊤ := by
      apply eq_top_iff.mpr
      rw [← hC.sup_eq_top]
      apply sup_le
      · intro w hw
        obtain ⟨c, hc, hcΛ⟩ := GlobalTheory.DegCnt.InnerLat.exists_mult hΛ.span_eq_top w
        have hwN : w ∈ N.Wn := by rw [hWn]; exact Submodule.mem_sup_left hw
        have hwU : w ∈ uPerp N.F N.F' := by rw [hUp]; exact Submodule.mem_sup_left hwN
        rw [← Submodule.smul_mem_iff _ hc]
        apply Submodule.subset_span
        exact Submodule.mem_sup_right ⟨⟨(uPerp N.F N.F').smul_mem c hwU,
          Submodule.mem_sup_left hcΛ⟩, N.Wn.smul_mem c hwN⟩
      · rw [hPi, ← GlobalTheory.DegCnt.InnerLat.span_hermFramePair_lattice_eq_sup N]
        exact Submodule.span_mono (show (N.P0 : Set V) ⊆ N.Ref (latL N.F N.F' Λ) from
          fun _ hx => Submodule.mem_sup_left hx)
    exact ⟨hspan⟩
  have hR1 : N.R1 ≤ N.R := inf_le_left
  have hZ : N.ZI ≤ N.R1 := inf_le_left
  have key : ∀ L : Submodule (𝓞 K) V, N.Gam L ⊓ N.R1 = N.R1 ⊓ MulAction.stabilizer (V ≃ₗ[K] V) L := by
    intro L
    unfold NF.Gam
    rw [inf_right_comm, inf_eq_right.mpr hR1]
  have hnil1 : ∀ s ∈ N.R1, ((s : V →ₗ[K] V) - 1) ^ (2 * r + 1) = 0 := fun s hs => hnil s (hR1 hs)
  have h3 := (GlobalTheory.DegCnt.Unimod.invVol_smul K V N.R1 _ hnil1 _ _ hRefFull hΛ).1
  have h4 := (GlobalTheory.DegCnt.Unimod.invVol_smul K V N.R1 _ hnil1 _ _ hΛ hRefFull).1
  rw [← key, ← key] at h3 h4
  have hprod := invVol_three N.R N.R1 N.ZI (N.Gam (N.Ref (latL N.F N.F' Λ))) (N.Gam Λ) hR1 hZ inf_le_left inf_le_left
    nM nZ (GlobalTheory.DegCnt.Unimod.invVol_smul K V N.R _ hnil _ _ hRefFull hΛ).1
    (GlobalTheory.DegCnt.Unimod.invVol_smul K V N.R _ hnil _ _ hΛ hRefFull).1 h3 h4
  have h1 : (1 : ℝ) ≤ (N.gI g Λ : ℝ) * N.iI g Λ := by
    have : 1 ≤ N.gI g Λ * N.iI g Λ := Nat.mul_pos hg0 hi0
    exact_mod_cast this
  have hpow : ((N.gI g Λ : ℝ) * N.iI g Λ) ^ (r - N.j) ≤ N.Del ^ r :=
    (pow_le_pow_right₀ h1 (Nat.sub_le _ _)).trans (pow_le_pow_left₀ (by linarith) hgi r)
  have hMid' := hMid.trans (mul_le_mul_of_nonneg_left hpow (by positivity))
  have hDel : (0 : ℝ) ≤ N.Del := by linarith
  unfold NF.om
  rw [hprod]
  calc _ ≤ (Ideal.absNorm 𝔠 : ℝ) ^ ((3 * e + 11) * (2 * r + 1) ^ 2) *
        ((N.bI Λ : ℝ) ^ Module.finrank K N.Wt * N.Del ^ r) *
        (Ideal.absNorm 𝔠 : ℝ) ^ ((3 * e + 11) * (2 * r + 1) ^ 2) :=
        mul_le_mul (mul_le_mul hBot hMid' (invVol_nonneg _ _) (by positivity)) hTop (invVol_nonneg _ _) (by positivity)
    _ = _ := by rw [mul_assoc 2, two_mul ((3 * e + 11) * _), pow_add]; ring

end GlobalTheory.DegCnt.Weight
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SubquotientCoveringRadiusRealPlaces
section
open GlobalTheory.Count GlobalTheory.IndefiniteRowSideFullHecke.CenteredPerpendicularSets Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField Finset

namespace GlobalTheory.Count.SubquotFrame

theorem map_mulVec' {n : ℕ} (σ : ℂ →+* ℂ) (M : Matrix (Fin n) (Fin n) ℂ) (u : Fin n → ℂ) :
    M.map σ *ᵥ (fun i => σ (u i)) = fun i => σ ((M *ᵥ u) i) := by
  funext i
  exact (RingHom.map_mulVec σ M u i).symm

theorem map_inv' {n : ℕ} (σ : ℂ →+* ℂ) (G : Matrix (Fin n) (Fin n) ℂ) (hG : IsUnit G.det) :
    (G.map σ)⁻¹ = G⁻¹.map σ := by
  refine Matrix.inv_eq_left_inv ?_
  rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hG, Matrix.map_one _ (map_zero σ) (map_one σ)]

theorem exists_invol (I : AutInst) (x : I.GA) (w : InfinitePlace I.E) :
    ∃ σ : ℂ →+* ℂ, (∀ z, σ (σ z) = z) ∧ (∀ z, ‖σ z‖ = ‖z‖) ∧
      (∀ a, w.embedding a = σ (I.φ (w.comap (algebraMap I.F I.E)) a)) ∧
      frm I x w = (I.P (w.comap (algebraMap I.F I.E)) * uMat (x.1 (w.comap (algebraMap I.F I.E)))).map σ := by
  have hw : w = InfinitePlace.mk (I.φ (w.comap (algebraMap I.F I.E))) := by
    apply (GlobalTheory.Count.FrameMajorant.comap_bijective I).1
    show w.comap (algebraMap I.F I.E) =
      (InfinitePlace.mk (I.φ (w.comap (algebraMap I.F I.E)))).comap (algebraMap I.F I.E)
    rw [InfinitePlace.comap_mk]
    have hc : (I.φ (w.comap (algebraMap I.F I.E))).comp (algebraMap I.F I.E) =
        (w.comap (algebraMap I.F I.E)).embedding := by
      ext a
      simp [I.φ_over]
    rw [hc, InfinitePlace.mk_embedding]
  by_cases h : w.embedding = I.φ (w.comap (algebraMap I.F I.E))
  · refine ⟨RingHom.id ℂ, fun z => rfl, fun z => rfl, fun a => by rw [h]; rfl, ?_⟩
    unfold frm
    rw [if_pos h]
    ext i j
    simp
  · have h2 : ComplexEmbedding.conjugate w.embedding = I.φ (w.comap (algebraMap I.F I.E)) :=
      (InfinitePlace.mk_eq_iff.mp ((InfinitePlace.mk_embedding w).trans hw)).resolve_left h
    refine ⟨starRingEnd ℂ, fun z => Complex.conj_conj z, fun z => Complex.norm_conj z, fun a => ?_, ?_⟩
    · rw [← h2]
      simp [ComplexEmbedding.conjugate_coe_eq]
    · unfold frm
      rw [if_neg h]

private theorem map_conj_mulVec_map_inv_mulVec {n : ℕ} (σ : ℂ →+* ℂ) (M T : Matrix (Fin n) (Fin n) ℂ) (hM : IsUnit M.det)
    (u : Fin n → ℂ) :
    (M⁻¹ * T * M).map σ *ᵥ (fun i => σ ((M⁻¹ *ᵥ u) i)) = fun i => σ ((M⁻¹ *ᵥ (T *ᵥ u)) i) := by
  rw [map_mulVec', Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc (M⁻¹ * T),
    Matrix.mul_nonsing_inv _ hM, Matrix.mul_one]

private theorem map_mulVec_mem_span_image_of_mem_span {n : ℕ} (σ : ℂ →+* ℂ) (N : Matrix (Fin n) (Fin n) ℂ) (s : Set (Fin n → ℂ))
    (u : Fin n → ℂ) (hu : u ∈ Submodule.span ℂ s) :
    (fun i => σ ((N *ᵥ u) i)) ∈ Submodule.span ℂ ((fun u : Fin n → ℂ => fun i => σ ((N *ᵥ u) i)) '' s) := by
  induction hu using Submodule.span_induction with
  | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
  | zero =>
    convert Submodule.zero_mem _ using 1
    funext i
    simp
  | add y z _ _ hy hz =>
    convert Submodule.add_mem _ hy hz using 1
    funext i
    simp [Matrix.mulVec_add]
  | smul c y _ hy =>
    convert Submodule.smul_mem _ (σ c) hy using 1
    funext i
    simp [Matrix.mulVec_smul]

private theorem isCMExt_apply_apply {n : ℕ} (σ : ℂ →+* ℂ) (hσ : ∀ z, σ (σ z) = z) (D : Matrix (Fin n) (Fin n) ℂ)
    (z r : Fin n → ℂ) (h : D *ᵥ (fun i => σ (z i)) = fun i => σ (r i)) : D.map σ *ᵥ z = r := by
  have key := map_mulVec' σ D (fun i => σ (z i))
  simp only [hσ] at key
  rw [h] at key
  simp only [hσ] at key
  exact key

private theorem inv_mul_inv_mul_conj_mul_mul_eq_self {n : ℕ} (P U Q : Matrix (Fin n) (Fin n) ℂ) (hP : IsUnit P.det)
    (hU : IsUnit U.det) : U⁻¹ * P⁻¹ * (P * U * Q * (P * U)⁻¹) * P * U = Q := by
  have k1 : ∀ B : Matrix (Fin n) (Fin n) ℂ, P⁻¹ * (P * B) = B := fun B => by
    rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hP, Matrix.one_mul]
  have k2 : ∀ B : Matrix (Fin n) (Fin n) ℂ, U⁻¹ * (U * B) = B := fun B => by
    rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hU, Matrix.one_mul]
  rw [Matrix.mul_inv_rev]
  simp only [Matrix.mul_assoc, k1, k2, Matrix.nonsing_inv_mul _ hU, Matrix.mul_one]

private theorem hs_map_of_norm_preserving {n : ℕ} (σ : ℂ →+* ℂ) (hσ : ∀ z, ‖σ z‖ = ‖z‖) (G : Matrix (Fin n) (Fin n) ℂ) :
    Formalism.REAL.hs (G.map σ) = Formalism.REAL.hs G := by
  simp only [Formalism.REAL.hs, Matrix.map_apply, hσ]

theorem subquot_frame : ∀ (I : AutInst) (x : I.GA) (A S R : Submodule (𝓞 I.E) (Fin I.n → I.E)) (lo hi : ℝ), A.FG → IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) A S → R.FG → 0 < lo → 0 < hi → (∀ N, S < N → N ≤ A → lo ≤ sizeQ (bas I) (frm I x) N S) → largestSize (bas I) (frm I x) R ≤ hi → ∀ T : InfinitePlace I.F → Matrix (Fin I.n) (Fin I.n) ℂ, (∀ v, ∀ y ∈ S, T v *ᵥ (fun i => I.φ v (y i)) = 0) → (∀ v, ∀ y ∈ A, T v *ᵥ (fun i => I.φ v (y i)) ∈ spanAt I R v) → ∃ Φ : Matrix (Fin I.n) (Fin I.n) I.E, (∀ y ∈ S, Φ *ᵥ y = 0) ∧ (∀ y ∈ A, Φ *ᵥ y ∈ R) ∧ ∃ D : InfinitePlace I.F → Matrix (Fin I.n) (Fin I.n) ℂ, (∀ v, ∀ u ∈ spanAt I A v, D v *ᵥ u = (T v - Φ.map (I.φ v)) *ᵥ u) ∧ normAt I x D ≤ ((rkK A : ℝ) - rkK S) * rkK R * Real.sqrt I.f * I.rd * hi / (2 * lo) := by
  intro I x A S R lo hi hA hSat hR hlo hhi hsz hlg T hTS hTA
  classical
  have : IsTotallyComplex I.E := I.cm.cmUnram.1
  have hbij := GlobalTheory.Count.FrameMajorant.comap_bijective I
  have hnp : nPl I.E = I.f := by
    rw [nPl, Fintype.card_of_bijective hbij, GlobalTheory.Count.FrameMajorant.card_places]
  choose σ hσi hσn hσe hσf using fun w : InfinitePlace I.E => exists_invol I x w
  have hPu : ∀ v, IsUnit (I.P v).det := fun v => (Matrix.isUnit_iff_isUnit_det _).mp (I.P_unit v)
  have hUu : ∀ v, IsUnit (uMat (x.1 v)).det := fun v =>
    (Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit _)
  have hMu : ∀ v, IsUnit (I.P v * uMat (x.1 v)).det := fun v => by
    rw [Matrix.det_mul]
    exact (hPu v).mul (hUu v)

  have hco : ∀ (w : InfinitePlace I.E) (y : Fin I.n → I.E),
      Formalism.HermitianLatticesTheory.fcoord (bas I) (frm I x) w y = fun i => σ w (((I.P (w.comap (algebraMap I.F I.E)) *
        uMat (x.1 (w.comap (algebraMap I.F I.E))))⁻¹ *ᵥ
          fun j => I.φ (w.comap (algebraMap I.F I.E)) (y j)) i) := by
    intro w y
    have hv : Formalism.HermitianLatticesTheory.vecAt (bas I) w y = fun i => σ w (I.φ (w.comap (algebraMap I.F I.E)) (y i)) := by
      funext i
      simp only [Formalism.HermitianLatticesTheory.vecAt, Pi.basisFun_repr]
      exact hσe w (y i)
    unfold Formalism.HermitianLatticesTheory.fcoord
    rw [hσf w, map_inv' (σ w) _ (hMu _), hv]
    exact map_mulVec' (σ w) _ _
  let T' : InfinitePlace I.E → Matrix (Fin I.n) (Fin I.n) ℂ := fun w =>
    ((I.P (w.comap (algebraMap I.F I.E)) * uMat (x.1 (w.comap (algebraMap I.F I.E))))⁻¹ *
      T (w.comap (algebraMap I.F I.E)) *
      (I.P (w.comap (algebraMap I.F I.E)) * uMat (x.1 (w.comap (algebraMap I.F I.E))))).map (σ w)
  have hT'S : ∀ w, ∀ y ∈ S, T' w *ᵥ Formalism.HermitianLatticesTheory.fcoord (Pi.basisFun I.E (Fin I.n)) (frm I x) w y = 0 := by
    intro w y hy
    show T' w *ᵥ Formalism.HermitianLatticesTheory.fcoord (bas I) (frm I x) w y = 0
    rw [hco w y, map_conj_mulVec_map_inv_mulVec _ _ _ (hMu _), hTS _ y hy]
    funext i
    simp
  have hT'A : ∀ w, ∀ y ∈ A, T' w *ᵥ Formalism.HermitianLatticesTheory.fcoord (Pi.basisFun I.E (Fin I.n)) (frm I x) w y ∈
      Submodule.span ℂ (Formalism.HermitianLatticesTheory.fcoord (Pi.basisFun I.E (Fin I.n)) (frm I x) w '' (R : Set (Fin I.n → I.E))) := by
    intro w y hy
    show T' w *ᵥ Formalism.HermitianLatticesTheory.fcoord (bas I) (frm I x) w y ∈
      Submodule.span ℂ (Formalism.HermitianLatticesTheory.fcoord (bas I) (frm I x) w '' (R : Set (Fin I.n → I.E)))
    rw [hco w y, map_conj_mulVec_map_inv_mulVec _ _ _ (hMu _)]
    refine Submodule.span_mono ?_ (map_mulVec_mem_span_image_of_mem_span (σ w) _ _ _ (hTA _ y hy))
    rintro _ ⟨_, ⟨r, hr, rfl⟩, rfl⟩
    exact ⟨r, hr, hco w r⟩
  obtain ⟨Φ, hΦS, hΦA, D', hD', hnorm⟩ := _root_.GlobalTheory.SubquotCover.subquot_cover I.E I.n (frm I x) A S R lo hi
    (GlobalTheory.Count.FrameMajorant.frm_unit I x) hA hSat hR hlo hhi hsz hlg T' hT'S hT'A
  let wv : InfinitePlace I.F → InfinitePlace I.E := Function.surjInv hbij.2
  have hwv : ∀ w, wv (w.comap (algebraMap I.F I.E)) = w := fun w =>
    hbij.1 (Function.surjInv_eq hbij.2 _)
  refine ⟨Φ, hΦS, hΦA, fun v => (I.P v * uMat (x.1 v)) * (D' (wv v)).map (σ (wv v)) *
    (I.P v * uMat (x.1 v))⁻¹, ?_, ?_⟩
  · intro v
    obtain ⟨w, rfl⟩ := hbij.2 v
    intro u hu
    simp only [hwv]
    unfold spanAt at hu
    induction hu using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨y, hy, rfl⟩ := hz
      have e1 := hD' w y hy
      have hX : (frm I x w)⁻¹ * Φ.map w.embedding * frm I x w =
          ((I.P (w.comap (algebraMap I.F I.E)) * uMat (x.1 (w.comap (algebraMap I.F I.E))))⁻¹ *
            Φ.map (I.φ (w.comap (algebraMap I.F I.E))) *
            (I.P (w.comap (algebraMap I.F I.E)) * uMat (x.1 (w.comap (algebraMap I.F I.E))))).map (σ w) := by
        have hΦ : Φ.map w.embedding = (Φ.map (I.φ (w.comap (algebraMap I.F I.E)))).map (σ w) := by
          ext i j
          simp only [Matrix.map_apply]
          exact hσe w _
        rw [hσf w, map_inv' (σ w) _ (hMu _), hΦ, ← Matrix.map_mul, ← Matrix.map_mul]
      rw [hX] at e1
      change D' w *ᵥ Formalism.HermitianLatticesTheory.fcoord (bas I) (frm I x) w y = _ at e1
      have hsub : T' w - ((I.P (w.comap (algebraMap I.F I.E)) * uMat (x.1 (w.comap (algebraMap I.F I.E))))⁻¹ *
            Φ.map (I.φ (w.comap (algebraMap I.F I.E))) *
            (I.P (w.comap (algebraMap I.F I.E)) * uMat (x.1 (w.comap (algebraMap I.F I.E))))).map (σ w) =
          ((I.P (w.comap (algebraMap I.F I.E)) * uMat (x.1 (w.comap (algebraMap I.F I.E))))⁻¹ *
            (T (w.comap (algebraMap I.F I.E)) - Φ.map (I.φ (w.comap (algebraMap I.F I.E)))) *
            (I.P (w.comap (algebraMap I.F I.E)) * uMat (x.1 (w.comap (algebraMap I.F I.E))))).map (σ w) := by
        rw [Matrix.mul_sub, Matrix.sub_mul]
        ext i j
        simp only [T', Matrix.sub_apply, Matrix.map_apply, map_sub]
      rw [hsub] at e1
      rw [hco w y, map_conj_mulVec_map_inv_mulVec _ _ _ (hMu _)] at e1
      have e2 := isCMExt_apply_apply (σ w) (hσi w) _ _ _ e1
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, e2, Matrix.mulVec_mulVec,
        Matrix.mul_nonsing_inv _ (hMu _), Matrix.one_mulVec]
    | zero => simp
    | add a b _ _ ha hb => rw [Matrix.mulVec_add, Matrix.mulVec_add, ha, hb]
    | smul c a _ ha => rw [Matrix.mulVec_smul, Matrix.mulVec_smul, ha]
  · have hterm : ∀ v, Formalism.REAL.hs (uMat (x.1 v)⁻¹ * (I.P v)⁻¹ * ((I.P v * uMat (x.1 v)) *
        (D' (wv v)).map (σ (wv v)) * (I.P v * uMat (x.1 v))⁻¹) * I.P v * uMat (x.1 v)) =
        Formalism.REAL.hs (D' (wv v)) := by
      intro v
      have hu : uMat (x.1 v)⁻¹ = (uMat (x.1 v))⁻¹ := by
        first
          | rfl
          | simp only [Formalism.MainNotions.S.uMat, Subgroup.coe_inv, Matrix.coe_units_inv]
      rw [hu, inv_mul_inv_mul_conj_mul_mul_eq_self _ _ _ (hPu v) (hUu v), hs_map_of_norm_preserving _ (hσn _)]
    have hsum : ∑ v, Formalism.REAL.hs (D' (wv v)) = ∑ w, Formalism.REAL.hs (D' w) :=
      (Fintype.sum_bijective _ hbij (fun w => Formalism.REAL.hs (D' w)) (fun v => Formalism.REAL.hs (D' (wv v)))
        (fun w => by rw [hwv w])).symm
    unfold normAt
    simp only [hterm]
    rw [hsum]
    rw [hnp] at hnorm
    unfold AutInst.rd
    exact hnorm

end GlobalTheory.Count.SubquotFrame
end

