module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocModel
public import Mathlib
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.TermsAtPtFinite
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermsFiniteAtPoint.Bundle0001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0027
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0021
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0017
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0016
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0027

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DataClose
section
noncomputable section

namespace Formalism.L2.SG.DataCut

theorem densInputAt_of_loc {D : Formalism.BasicNotions.D7} (hL : DensLocBound D) : Formalism.L2.SG.DataInst.DensInputAt D :=
  densInputAt_of hL (Formalism.L2.SG.Pf.alpBound_holds D) (Formalism.L2.SG.Pf.placesOver_holds D)

end Formalism.L2.SG.DataCut
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarLprExistA
section
noncomputable section

open scoped Classical
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc ValuativeRel
  Formalism.L2.SG.Pf.ScalarFramePf

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.LprEx

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Glob

variable {D : D7}

theorem LprExistA_iso_span {s : Set (VS D).V} (h : ∀ x ∈ s, ∀ y ∈ s, (VS D).hT x y = 0) :
    ∀ x ∈ Submodule.span D.host.E s, ∀ y ∈ Submodule.span D.host.E s, (VS D).hT x y = 0 := by
  have h1 : ∀ x ∈ s, ∀ y ∈ Submodule.span D.host.E s, (VS D).hT x y = 0 := by
    intro x hx y hy
    have hle : Submodule.span D.host.E s ≤ LinearMap.ker ((VS D).hT x) := by
      rw [Submodule.span_le]
      intro y' hy'
      exact h x hx y' hy'
    exact hle hy
  intro x hx y hy
  have hle : Submodule.span D.host.E s ≤ LinearMap.ker ((VS D).hT.flip y) := by
    rw [Submodule.span_le]
    intro x' hx'
    show (VS D).hT.flip y x' = 0
    rw [LinearMap.flip_apply]
    exact h1 x' hx' y hy
  have := hle hx
  rw [LinearMap.mem_ker, LinearMap.flip_apply] at this
  exact this

theorem LprExistA_orth_span {s : Set (VS D).V} {x : (VS D).V} (h : ∀ v ∈ s, (VS D).hT v x = 0) :
    ∀ v ∈ Submodule.span D.host.E s, (VS D).hT v x = 0 := by
  intro v hv
  have hle : Submodule.span D.host.E s ≤ LinearMap.ker ((VS D).hT.flip x) := by
    rw [Submodule.span_le]
    intro v' hv'
    show (VS D).hT.flip x v' = 0
    rw [LinearMap.flip_apply]
    exact h v' hv'
  have := hle hv
  rw [LinearMap.mem_ker, LinearMap.flip_apply] at this
  exact this

theorem gfacts_move {Λ : Submodule (𝓞 D.host.E) (VS D).V} {f g1 g2 g2' : Fin (D.R.rS + 1) → (VS D).V}
    {β : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hG : GFacts Λ f g1 g2' β)
    (hX : Submodule.span D.host.E (Set.range fun b : Fin D.R.rS => g2' b.castSucc) =
      Submodule.span D.host.E (Set.range fun b : Fin D.R.rS => g2 b.castSucc))
    (hsp : Submodule.span D.host.E (Set.range g2') = Submodule.span D.host.E (Set.range g2))
    (hz : g2' (Fin.last _) - g2 (Fin.last _) ∈
      Submodule.span D.host.E (Set.range fun b : Fin D.R.rS => g2 b.castSucc))
    (ht : GDl f g2' (D.R.rS + 1) = GDl f g2 (D.R.rS + 1)) (hr : GDl f g2' D.R.rS = GDl f g2 D.R.rS)
    (ho' : Gom' f g2' = Gom' f g2) (ho : Gom f g2' = Gom f g2) : GFacts Λ f g1 g2 β := by
  have hmap : Submodule.span D.host.E (Set.range fun b : Fin D.R.rS => g2' b.castSucc) ≤
      (Submodule.span D.host.E (Set.range fun a : Fin D.R.rS => g1 a.castSucc)).comap
        β.symm.toLinearMap := by
    rw [Submodule.span_le]
    rintro _ ⟨b, rfl⟩
    exact hG.xmap' b
  refine
    { iso := hG.iso
      lam := hG.lam
      lam' := hG.lam'
      xmap := fun a => hX ▸ hG.xmap a
      xmap' := fun a => ?_
      zmap := ?_
      fiso := hG.fiso
      g2iso := fun a b => ?_
      proj := hG.proj
      gram := hG.gram
      theta := fun x1 hx1 => ?_
      ratio := ?_
      omp := ?_
      om := ?_ }
  · have h : g2 a.castSucc ∈ Submodule.span D.host.E (Set.range fun b : Fin D.R.rS => g2' b.castSucc) := by
      rw [hX]; exact Submodule.subset_span ⟨a, rfl⟩
    exact hmap h
  · have h1 := hG.zmap
    rw [hX] at h1
    have h3 := Submodule.add_mem _ h1 hz
    rwa [sub_add_sub_cancel] at h3
  · have hiso : ∀ x ∈ Set.range (fun b : Fin D.R.rS => g2' b.castSucc),
        ∀ y ∈ Set.range (fun b : Fin D.R.rS => g2' b.castSucc), (VS D).hT x y = 0 := by
      rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
      exact hG.g2iso i j
    have ha : g2 a.castSucc ∈ Submodule.span D.host.E (Set.range fun b : Fin D.R.rS => g2' b.castSucc) := by
      rw [hX]; exact Submodule.subset_span ⟨a, rfl⟩
    have hb : g2 b.castSucc ∈ Submodule.span D.host.E (Set.range fun b : Fin D.R.rS => g2' b.castSucc) := by
      rw [hX]; exact Submodule.subset_span ⟨b, rfl⟩
    exact LprExistA_iso_span hiso _ ha _ hb
  · obtain ⟨x2, h1, h2, h3⟩ := hG.theta x1 hx1
    refine ⟨x2, fun i => ?_, h2, hX ▸ h3⟩
    rcases i with a | b
    · exact h1 (Sum.inl a)
    · have horth : ∀ v ∈ Set.range g2', (VS D).hT v x2 = 0 := by
        rintro _ ⟨c, rfl⟩
        exact h1 (Sum.inr c)
      have hb : g2 b ∈ Submodule.span D.host.E (Set.range g2') := by
        rw [hsp]; exact Submodule.subset_span ⟨b, rfl⟩
      exact LprExistA_orth_span horth _ hb
  · rw [← ht, ← hr]; exact hG.ratio
  · rw [← ht, ← ho']; exact hG.omp
  · rw [← ht, ← ho, ← hX]; exact hG.om

theorem gfacts_frameAct {Λ : Submodule (𝓞 D.host.E) (VS D).V} {f g1 h : Fin (D.R.rS + 1) → (VS D).V}
    {β : (VS D).V ≃ₗ[D.host.E] (VS D).V} (ξ : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (𝓞 D.host.E))
    (h1 : ∀ a b, b < a → ξ a b = 0) (h2 : ∀ a, ξ a a = 1) (hG : GFacts Λ f g1 (frameAct h ξ⁻¹) β) :
    GFacts Λ f g1 h β := by
  have hη := inv_unitri ξ h1 h2
  refine gfacts_move hG (Xs_frameAct_inv h ξ h1 h2) (span_frameAct_inv h ξ h1 h2) ?_
    (GDl_frameAct_top f h ξ⁻¹ hη.1 hη.2) (GDl_frameAct_r f h ξ⁻¹ hη.1 hη.2)
    (Gom'_frameAct f h ξ⁻¹ hη.1 hη.2) (Gom_frameAct f h ξ⁻¹ hη.1 hη.2)
  exact frameAct_last_sub h ξ⁻¹ (hη.2 _)

end Glob

section LocIota

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : Loc.HermSp M V)

theorem iotaG_congr {q : E} {abelian₂ : Submodule M.L.O V} {r : ℕ} {f₀ f₁ f₂ f₂' : Fin (r + 1) → V} {e : V ≃ₗ[E] V}
    (hX : H.X f₂ = H.X f₂') (h : IotaG H q abelian₂ f₀ f₁ f₂ e) : IotaG H q abelian₂ f₀ f₁ f₂' e := by
  unfold IotaG at h ⊢
  rw [← hX]
  exact h

end LocIota

section Loc

variable {D : D7} (Z : LocDat D) (p : PlF D)

theorem locX_eq {g2 g2' : Fin (D.R.rS + 1) → (VS D).V}
    (hX : Submodule.span D.host.E (Set.range fun b : Fin D.R.rS => g2' b.castSucc) =
      Submodule.span D.host.E (Set.range fun b : Fin D.R.rS => g2 b.castSucc)) :
    (locH Z p).X (fun b => sF' Z p b • baseChange₂ D p (g2' b)) = (locH Z p).X (fun b => sF' Z p b • baseChange₂ D p (g2 b)) := by
  apply le_antisymm
  · unfold Loc.HermSp.X
    rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    have hm : g2' a.castSucc ∈ Submodule.span D.host.E (Set.range fun b : Fin D.R.rS => g2 b.castSucc) := by
      rw [← hX]; exact Submodule.subset_span ⟨a, rfl⟩
    exact Submodule.smul_mem _ _ (bcP_mem_X Z p g2 (sF' Z p) (isUnit_sF' Z p) hm)
  · unfold Loc.HermSp.X
    rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    have hm : g2 a.castSucc ∈ Submodule.span D.host.E (Set.range fun b : Fin D.R.rS => g2' b.castSucc) := by
      rw [hX]; exact Submodule.subset_span ⟨a, rfl⟩
    exact Submodule.smul_mem _ _ (bcP_mem_X Z p g2' (sF' Z p) (isUnit_sF' Z p) hm)

theorem iotaEl_frameAct {Λ : Submodule (𝓞 D.host.E) (VS D).V} {f g1 h : Fin (D.R.rS + 1) → (VS D).V}
    {β : (VS D).V ≃ₗ[D.host.E] (VS D).V} (ξ : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (𝓞 D.host.E))
    (h1 : ∀ a b, b < a → ξ a b = 0) (h2 : ∀ a, ξ a a = 1) (hI : IotaEl Z p Λ f g1 (frameAct h ξ⁻¹) β) :
    IotaEl Z p Λ f g1 h β := by
  intro gg hgg
  exact iotaG_congr (locH Z p) (locX_eq Z p (Xs_frameAct_inv h ξ h1 h2)) (hI gg hgg)

end Loc

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.LprEx
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.KloostermanCosetSumLe
section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp
  Formalism.L2.SG.Full Formalism.MainNotions.KTwoCosetCount Formalism.MainNotions.MinorIntegralityTorus

namespace Formalism.L2.SG.KappaOffDiagonal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

theorem cosets_sum_gen {D : D7} (hNT : KTwoMinorIntegrality.NormLB) (hLS : KTwoMinorIntegrality.LatSum)
    [Nonempty D.what₂.Tau] (hrd : 0 < D.host.rdE) {H1 : ℝ}
    (hH : 0 < H1) {j : ℕ} (hj : j ≤ D.R.rS) (T : Finset (ℕ → D.host.E))
    (hfact : ∀ δ ∈ T, (∀ l, IsIntegral ℤ (δ l)) ∧ (∀ l, j < l → δ l = 0) ∧ δ 0 = 1) :
    ∑ δ ∈ T, KappaEndpoints.k2S D H1 j δ ^ (-(3 * (D.R.rS : ℝ))) ≤
      2 ^ j * ∏ l ∈ Finset.Icc 1 j, (64 * Rl (D := D) H1 l) ^ (2 * Fintype.card D.what₂.Tau) := by
  classical
  set K : ℝ := ∏ l ∈ Finset.Icc 1 j, (64 * Rl (D := D) H1 l) ^ (2 * Fintype.card D.what₂.Tau) with hK
  have hmaps : ∀ δ ∈ T, KappaEndpoints.k2ends D j δ ∈ (Finset.Icc 1 j).powerset := by
    intro δ _
    rw [Finset.mem_powerset]
    unfold KappaEndpoints.k2ends
    exact Finset.filter_subset _ _
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hS : ∀ S ∈ (Finset.Icc 1 j).powerset,
      ∑ δ ∈ T with KappaEndpoints.k2ends D j δ = S, KappaEndpoints.k2S D H1 j δ ^ (-(3 * (D.R.rS : ℝ))) ≤ K := by
    intro S hSm
    have hSsub := Finset.mem_powerset.1 hSm
    set TS := T.filter (fun δ => KappaEndpoints.k2ends D j δ = S) with hTS
    have step1 : ∑ δ ∈ TS, KappaEndpoints.k2S D H1 j δ ^ (-(3 * (D.R.rS : ℝ))) ≤
        ∑ δ ∈ TS, ∏ l ∈ S, wl (D := D) H1 l (δ l) := by
      apply Finset.sum_le_sum
      intro δ hδ
      have he := (Finset.mem_filter.1 hδ).2
      have := S_rpow_le (D := D) H1 hj δ
      rwa [he] at this
    have hinj : ∀ δ ∈ TS, ∀ δ' ∈ TS, (∀ l ∈ S, δ l = δ' l) → δ = δ' := by
      intro δ hδ δ' hδ' h
      obtain ⟨hδT, he⟩ := Finset.mem_filter.1 hδ
      obtain ⟨hδT', he'⟩ := Finset.mem_filter.1 hδ'
      obtain ⟨-, hz, h0⟩ := hfact δ hδT
      obtain ⟨-, hz', h0'⟩ := hfact δ' hδT'
      funext l
      by_cases hl0 : l = 0
      · rw [hl0, h0, h0']
      by_cases hlj : j < l
      · rw [hz l hlj, hz' l hlj]
      by_cases hlS : l ∈ S
      · exact h l hlS
      have hI : l ∈ Finset.Icc 1 j := Finset.mem_Icc.2 ⟨by omega, by omega⟩
      have a1 : δ l = 0 := by
        by_contra hne
        apply hlS
        rw [← he]
        unfold KappaEndpoints.k2ends
        exact Finset.mem_filter.2 ⟨hI, hne⟩
      have a2 : δ' l = 0 := by
        by_contra hne
        apply hlS
        rw [← he']
        unfold KappaEndpoints.k2ends
        exact Finset.mem_filter.2 ⟨hI, hne⟩
      rw [a1, a2]
    have step2 := sum_prod_le S TS (fun l x => wl (D := D) H1 l x) (fun l x => wl_nonneg H1 l x) hinj
    have step3 : ∏ l ∈ S, ∑ x ∈ TS.image (fun δ => δ l), wl (D := D) H1 l x ≤
        ∏ l ∈ S, (64 * Rl (D := D) H1 l) ^ (2 * Fintype.card D.what₂.Tau) := by
      apply Finset.prod_le_prod₀
      · intro l _; exact Finset.sum_nonneg fun x _ => wl_nonneg H1 l x
      · intro l _
        have hint : ∀ x ∈ TS.image (fun δ => δ l), IsIntegral ℤ x := by
          intro x hx
          obtain ⟨δ, hδ, rfl⟩ := Finset.mem_image.1 hx
          exact (hfact δ (Finset.mem_filter.1 hδ).1).1 l
        calc ∑ x ∈ TS.image (fun δ => δ l), wl (D := D) H1 l x
            ≤ ∑ x ∈ TS.image (fun δ => δ l), ∏ τ : D.what₂.Tau, (max 1 (‖embS D τ x‖ / Rl (D := D) H1 l)) ^ (-(3 : ℝ)) :=
              Finset.sum_le_sum fun x _ => wl_le hrd hH l x
          _ ≤ _ := sum_one_coord hNT hLS _ hint (one_le_Rl H1 l)
    have step4 : ∏ l ∈ S, (64 * Rl (D := D) H1 l) ^ (2 * Fintype.card D.what₂.Tau) ≤ K := by
      rw [hK, ← Finset.prod_sdiff hSsub]
      have hge : ∀ l, 1 ≤ (64 * Rl (D := D) H1 l) ^ (2 * Fintype.card D.what₂.Tau) :=
        fun l => one_le_pow₀ (by linarith [one_le_Rl (D := D) H1 l])
      have h1 : 1 ≤ ∏ l ∈ Finset.Icc 1 j \ S, (64 * Rl (D := D) H1 l) ^ (2 * Fintype.card D.what₂.Tau) :=
        Finset.prod_induction _ (fun x => 1 ≤ x) (fun a b ha hb => one_le_mul_of_one_le_of_one_le ha hb) le_rfl
          (fun l _ => hge l)
      have h0 : 0 ≤ ∏ l ∈ S, (64 * Rl (D := D) H1 l) ^ (2 * Fintype.card D.what₂.Tau) :=
        Finset.prod_nonneg fun l _ => le_trans zero_le_one (hge l)
      nlinarith
    exact step1.trans (step2.trans (step3.trans step4))
  calc _ ≤ ∑ S ∈ (Finset.Icc 1 j).powerset, K := Finset.sum_le_sum hS
    _ = 2 ^ j * K := by
      rw [Finset.sum_const, Finset.card_powerset, nsmul_eq_mul]
      simp

theorem kloostermanCosetSum_le {D : D7} (hNT : KTwoMinorIntegrality.NormLB) (hLS : KTwoMinorIntegrality.LatSum) (large₂ : SizeData₂ D)
    {C' Cl Cg cb Cu cT CT C0 : ℝ} (hH : Formalism.MainNotions.NonGenericAndKTwoTheorems.KTwoHypotheses D large₂ C' Cl Cg cb Cu cT CT C0) (CH : ℝ)
    (j : ℕ) (hj : j ∈ Finset.Icc 1 D.R.rS) (T : Finset (ℕ → D.host.E))
    (hfact : ∀ δ ∈ T, (∀ l, IsIntegral ℤ (δ l)) ∧ (∀ l, j < l → δ l = 0) ∧ δ 0 = 1) :
    ∑ δ ∈ T, KappaEndpoints.k2S D (large₂.sc.b ^ (CH * (D.R.m : ℝ))) j δ ^ (-(3 * (D.R.rS : ℝ))) ≤
      Hb large₂.sc.b (ccOf CH Cl) D.R.m D.R.f ^ (ccOf CH Cl * (D.R.rS : ℝ)) := by
  obtain ⟨⟨h0, -, -⟩, -⟩ := hH
  obtain ⟨-, -, hmf, -, -, -, -, -, -, -, hrdL, -, -, -, -, -, -, -, hv, -, -, -, -, -, hCl⟩ := h0
  have hjI := Finset.mem_Icc.1 hj
  have hrd2 : 2 ≤ D.host.rdE := by unfold Formalism.BasicNotions.Host.v at hv; linarith
  have hm2 := D.R.two_le_m
  have hf1 : 1 ≤ D.R.f := le_trans (Nat.one_le_pow _ _ (by omega)) hmf
  have : Nonempty D.what₂.Tau := Fintype.card_pos_iff.1 (by rw [D.what₂.card_Tau]; omega)
  have hb2 := KappaEndpoints.two_le_scale_b D large₂
  set H1 : ℝ := large₂.sc.b ^ (CH * (D.R.m : ℝ)) with hH1def
  have hH1 : 0 < H1 := Real.rpow_pos_of_pos (by linarith) _
  have hsum := cosets_sum_gen hNT hLS (by linarith) hH1 hjI.2 T hfact
  set B : ℝ := D.host.rdE ^ (((2 * (D.R.rS * D.R.rS) : ℕ)) : ℝ) * (max 1 (2 * H1)) ^ (2 * D.R.rS) with hB
  have hB1 : 1 ≤ B := one_le_mul_of_one_le_of_one_le (Real.one_le_rpow (by linarith) (Nat.cast_nonneg _))
    (one_le_pow₀ (le_max_left _ _))
  have hRl : ∀ l ∈ Finset.Icc 1 j, Rl (D := D) H1 l ≤ B := by
    intro l hl
    have hlr : l ≤ D.R.rS := (Finset.mem_Icc.1 hl).2.trans hjI.2
    have hfe := frameExp_le hlr
    refine max_le hB1 (mul_le_mul ?_ (pow_le_pow_left₀ (by positivity) (le_max_right _ _) _) (by positivity)
      (Real.rpow_nonneg (by linarith) _))
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by exact_mod_cast (by omega : 2 * frameExp D.R.rS l ≤ 2 * (D.R.rS * D.R.rS)))
  have hprod : ∏ l ∈ Finset.Icc 1 j, (64 * Rl (D := D) H1 l) ^ (2 * Fintype.card D.what₂.Tau) ≤
      ((64 * B) ^ (2 * Fintype.card D.what₂.Tau)) ^ j := by
    calc ∏ l ∈ Finset.Icc 1 j, (64 * Rl (D := D) H1 l) ^ (2 * Fintype.card D.what₂.Tau)
        ≤ ∏ l ∈ Finset.Icc 1 j, (64 * B) ^ (2 * Fintype.card D.what₂.Tau) :=
          Finset.prod_le_prod₀ (fun l _ => pow_nonneg (by linarith [one_le_Rl (D := D) H1 l]) _)
            (fun l hl => pow_le_pow_left₀ (by linarith [one_le_Rl (D := D) H1 l]) (by linarith [hRl l hl]) _)
      _ = ((64 * B) ^ (2 * Fintype.card D.what₂.Tau)) ^ j := by rw [Finset.prod_const]; simp
  have hfin := final_arith (L := large₂.sc.L) (CH := CH) (rd := D.host.rdE) (r := D.R.rS) (m := D.R.m) (f := D.R.f)
    (n := Fintype.card D.what₂.Tau) (j := j) (KappaEndpoints.one_lt_scale_L D large₂) hCl (by linarith) hrdL (by omega)
    (by have := KappaEndpoints.two_rank_add_two_eq_m D; omega) hjI.2 (by rw [D.what₂.card_Tau]) hf1
  unfold Hb
  calc _ ≤ _ := hsum
    _ ≤ 2 ^ j * ((64 * B) ^ (2 * Fintype.card D.what₂.Tau)) ^ j := mul_le_mul_of_nonneg_left hprod (by positivity)
    _ ≤ _ := hfin

end Gen

section Conc

variable {D : D7} {X : HidaSetting D} {Y : Full X} {u : D.what₂.Word}

theorem minorInt_conc (t : GTu Y u) (l : ℕ) (hl : l ≤ D.R.rS) :
    IsIntegral ℤ (Dl (lf D (X.Fu u)).fl (frq X t.rep).fl l) := by
  have hRow : IsRowLat D (X.Fu u) t.lam := (Y.rowsOK u).1 t.lam t.mem
  have hOK : FrameOK D t.lam (frq X t.rep) := t.rep.2.2.2.2.2.2
  have hU : Formalism.HermitianLatticesTheory.IsUnimodular (hS D).hT t.lam := hRow.2.1.2.1
  have he : ∀ a, (lf D (X.Fu u)).fl.e a ∈ t.lam := e_mem_lam D t.lam (lf D (X.Fu u)) hRow.2.2
  have he' : ∀ a, (frq X t.rep).fl.e a ∈ t.lam := e_mem_lam D t.lam (frq X t.rep) hOK.2
  have hl' : l ≤ D.R.rS + 1 := by omega
  unfold Dl leadMinorE
  rw [dite_eq_left hl']
  apply det_isIntegral
  intro i j
  have hi : Fin.castLE hl' i = Fin.castSucc ⟨i, by omega⟩ := Fin.ext rfl
  have hj : Fin.castLE hl' j = Fin.castSucc ⟨j, by omega⟩ := Fin.ext rfl
  simp only [Matrix.submatrix_apply, Zhat, brS]
  rw [hi, hj]
  simp only [FlagG.fvec, Fin.snoc_castSucc]
  exact pair_int D hU (he' _) (he _)

theorem labFacts_conc (t : GTu Y u) :
    (∀ l, IsIntegral ℤ (labT t l)) ∧ (∀ l, jT t < l → labT t l = 0) ∧ labT t 0 = 1 := by
  refine ⟨fun l => ?_, fun l hl => ?_, ?_⟩
  · unfold labT
    split_ifs with hl
    · exact minorInt_conc t l (le_trans hl (Nat.sub_le _ _))
    · exact isIntegral_zero
  · unfold labT
    rw [if_neg (not_le.mpr (by unfold jT at hl; exact hl))]
  · unfold labT
    rw [if_pos (Nat.zero_le _)]
    unfold Dl leadMinorE
    first
      | exact Matrix.det_isEmpty
      | simp
      | done

theorem cosetsC_holds : CosetsC := by
  intro Cg cb Cw cT CT C0 CH hCH
  refine ⟨21 + 4 * |CH|, by positivity, 0, 1, fun C' Cl _ hCl1 D large₂ X Y u hH _ j hj T hTm => ?_⟩
  have hfact : ∀ δ ∈ T, (∀ l, IsIntegral ℤ (δ l)) ∧ (∀ l, j < l → δ l = 0) ∧ δ 0 = 1 := by
    intro δ hδ
    obtain ⟨t, -, rfl, rfl⟩ := hTm δ hδ
    exact labFacts_conc t
  have h := kloostermanCosetSum_le NormLB_holds Formalism.MainNotions.LatticeSumConvergence.LatSum_holds large₂ hH CH j hj T hfact
  unfold H1C
  refine h.trans ?_
  have hb : 1 ≤ large₂.sc.b := by linarith [KappaEndpoints.two_le_scale_b D large₂]
  have hCl0 : 0 < Cl := by linarith
  have hc0 : 0 ≤ ccOf CH Cl := by unfold ccOf; positivity
  have hcle : ccOf CH Cl ≤ 21 + 4 * |CH| := by
    unfold ccOf
    have : 4 / Cl ≤ 4 := by rw [div_le_iff₀ hCl0]; linarith
    linarith
  unfold Hb
  rw [← Real.rpow_mul (by linarith), ← Real.rpow_mul (by linarith)]
  apply Real.rpow_le_rpow_of_exponent_le hb
  have hx : 0 ≤ (D.R.m : ℝ) ^ 2 * D.R.f * D.R.rS := by positivity
  have e1 : ccOf CH Cl * (D.R.m : ℝ) ^ 2 * D.R.f * (ccOf CH Cl * D.R.rS) =
      ccOf CH Cl * ccOf CH Cl * ((D.R.m : ℝ) ^ 2 * D.R.f * D.R.rS) := by ring
  have e2 : (21 + 4 * |CH|) * (D.R.m : ℝ) ^ 2 * D.R.f * ((21 + 4 * |CH|) * D.R.rS) =
      (21 + 4 * |CH|) * (21 + 4 * |CH|) * ((D.R.m : ℝ) ^ 2 * D.R.f * D.R.rS) := by ring
  rw [e1, e2]
  exact mul_le_mul_of_nonneg_right (mul_le_mul hcle hcle hc0 (by positivity)) hx

end Conc

end Formalism.L2.SG.KappaOffDiagonal
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RealDecomp
section
noncomputable section

open scoped Classical ComplexConjugate

namespace Formalism.L2.SG.Pf.RowForm

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.TypedSets
  Formalism.L2.SG.MassDataConc Formalism.L2.SG.MassDataForm MeasureTheory

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (u u' : D.what₂.Word)
  (κ : Term D u u' (X.Fu u) (Y.what₂ u) → ℕ)

def RealDecompC : Prop :=
  ∀ t : Formalism.L2.SG.TermOp.GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u'), t.relevant → t.G ≠ 0 →
    (∃ γ, Formalism.L2.SG.RealObj.IsPtRep X u u' (Formalism.L2.SG.PairVal.ptOf t.toTerm) γ) ∧
      ∀ γ, Formalism.L2.SG.RealObj.IsPtRep X u u' (Formalism.L2.SG.PairVal.ptOf t.toTerm) γ →
        ∃ g ∈ X.SinfU u, ∃ g' ∈ X.SinfU u', t.pt.1 = g * γ * g'⁻¹

theorem isPtRep_gamW {w : Point D.host.E (D.R.rS + 1)} (h : ∃ γ, Formalism.L2.SG.RealObj.IsPtRep X u u' w γ) :
    Formalism.L2.SG.RealObj.IsPtRep X u u' w (Formalism.L2.SG.RealObj.gamW X u u' w) := by
  unfold Formalism.L2.SG.RealObj.gamW
  rw [dite_eq_left h]
  exact h.choose_spec

theorem realDecompC_gamW (h : RealDecompC X Y u u')
    (t : Formalism.L2.SG.TermOp.GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u')) (hrel : t.relevant) (hG : t.G ≠ 0) :
    (∃ γ, Formalism.L2.SG.RealObj.IsPtRep X u u' (Formalism.L2.SG.PairVal.ptOf t.toTerm) γ) ∧
      ∃ g ∈ X.SinfU u, ∃ g' ∈ X.SinfU u',
        t.pt.1 = g * Formalism.L2.SG.RealObj.gamW X u u' (Formalism.L2.SG.PairVal.ptOf t.toTerm) * g'⁻¹ := by
  obtain ⟨hex, hall⟩ := h t hrel hG
  exact ⟨hex, hall _ (isPtRep_gamW X u u' hex)⟩

theorem realDecomp_G_ne (s : Formalism.L2.SG.TermOp.GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u'))
    (h : (Y.tO u u').G s ≠ 0) : s.G ≠ 0 := by
  intro h0
  apply h
  show Formalism.L2.SG.TermOp.Gt s = 0
  simp [Formalism.L2.SG.TermOp.Gt, h0]

theorem liftDecompC_of_real (h : RealDecompC X Y u u') : LiftDecompC X Y u u' κ := by
  intro R ρ s hrel
  exact realDecompC_gamW X Y u u' h s.1 hrel (realDecomp_G_ne X Y u u' s.1 s.2.1)

end Formalism.L2.SG.Pf.RowForm
end
end

