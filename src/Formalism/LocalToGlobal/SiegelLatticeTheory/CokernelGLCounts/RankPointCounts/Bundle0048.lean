module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0031
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CoefNotInt
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0028
public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0012
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0046
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0047
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0025
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0029
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0024
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0019
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SatGram
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.TypedLoc
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SatGramLocPfB
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.ConcreteLevelAdelicSubset
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.GenericRatioOfBoundHolds
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.GrowthOfBasic
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.UnitaryDimensionFormula
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThSomePf

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CoefLoc
section
noncomputable section

namespace Formalism.L2.SG.Pf.Coef

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB
open Classical ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep}
  {δ : ∀ p : PlF D, (D.s.atP p).Fp} {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem normRepElig_of (hN : PairVal.NormRepExists D u u' F0 what₂) : NormRepElig u u' F0 what₂ := by
  intro γ w hγ
  obtain ⟨y, hy⟩ := hN γ w hγ.2 (PCount.eligRel_holds γ w hγ) hγ.1.1
  exact ⟨(w, y), hy⟩

theorem locClsE_of (hA : ∀ p, Agree δ M p) (hT : (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2])
    (hrows : IsRowReps D F0 what₂) (hN : PairVal.NormRepExists D u u' F0 what₂)
    (hO : ∀ Zd : TermLoc.LocDat D, PCount.InOrbZ Zd u u') : LocClsE M δ u u' F0 what₂ := by
  intro γ w hγ p
  refine ⟨fun a b => ?_, hO ⟨δ, M, hA⟩ w (zT γ) (PCount.atMat_zT hN hrows hγ (PCount.eligRel_holds γ w hγ)) p⟩
  obtain ⟨Λ, hΛ, F', hF'⟩ := dnInDens_of (normRepElig_of hN) hrows γ w hγ
  have hI := PI.CntNotIntW.integral_on_pairs_holds D δ M hA u u' hT F0 what₂ hrows Λ hΛ (zT γ) F' hF' p
  simp only [yT, LsDatumB.sgnP, Matrix.mul_diagonal]
  exact Subring.mul_mem _ (hI a b) (Subring.pow_mem _ (Subring.neg_mem _ (Subring.one_mem _)) _)

end Formalism.L2.SG.Pf.Coef
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DensCongClose
section
noncomputable section

namespace Formalism.L2.SG.Pf

theorem density_congruence_holds : Coef.DensCong := by
  intro F E _ _ _ _ _ _ _ M V _ _ H ϖ abelian₂ ι _ _ G A hA hdet
  obtain ⟨y, hy, hyd⟩ := hdet
  have hyd' : y * A.det = 1 := by rw [mul_comm]; exact hyd
  set B : Matrix ι ι E := y • A.adjugate with hBdef
  have hB : ∀ i j, B i j ∈ M.L.O := fun i j => by
    simp only [hBdef, Matrix.smul_apply, smul_eq_mul]
    exact M.L.O.mul_mem hy (DensCongPf.adj_mem A hA i j)
  have hAB : A * B = 1 := by
    rw [hBdef, Matrix.mul_smul, Matrix.mul_adjugate, smul_smul, hyd', one_smul]
  have hBA : B * A = 1 := by
    rw [hBdef, Matrix.smul_mul, Matrix.adjugate_mul, smul_smul, hyd', one_smul]
  have hm : ∀ X Y : Matrix ι ι E, (X * Y).map M.L.cj = X.map M.L.cj * Y.map M.L.cj := by
    intro X Y
    ext i j
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Matrix.mul_apply, map_sum, map_mul]
  have hone : (1 : Matrix ι ι E).map M.L.cj = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  have hG : (B.map M.L.cj).transpose * ((A.map M.L.cj).transpose * G * A) * B = G := by
    calc _ = ((A * B).map M.L.cj).transpose * G * (A * B) := by
          rw [hm, Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
      _ = G := by rw [hAB, hone, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]
  unfold MainNotions.S.Loc.HermSp.dens
  congr 2
  have fwd : ∀ (K P Q : Matrix ι ι E) (hP : ∀ i j, P i j ∈ M.L.O), (∀ i j, Q i j ∈ M.L.O) →
      P * Q = 1 → Q * P = 1 → ∀ x, x ∈ Set.range (fun (v : {v : ι → V // H.Prim abelian₂ v ∧
        ∀ a b, H.h (v b) (v a) - K a b ∈ (M.L.O ∙ (algebraMap F E) ↑ϖ)}) (a : ι) =>
          (Submodule.Quotient.mk (p := H.smulLat ((algebraMap F E) ↑ϖ) abelian₂) (v.1 a))) →
      DensCongPf.psi H abelian₂ ((algebraMap F E) ↑ϖ) P hP x ∈ Set.range (fun (v : {v : ι → V //
        H.Prim abelian₂ v ∧ ∀ a b, H.h (v b) (v a) - ((P.map M.L.cj).transpose * K * P) a b ∈
          (M.L.O ∙ (algebraMap F E) ↑ϖ)}) (a : ι) =>
          (Submodule.Quotient.mk (p := H.smulLat ((algebraMap F E) ↑ϖ) abelian₂) (v.1 a))) := by
    rintro K P Q hP hQ hPQ hQP x ⟨⟨v, hv1, hv2⟩, rfl⟩
    exact ⟨⟨DensCongPf.act P v, DensCongPf.prim_act H abelian₂ P Q hP hQ hPQ hQP v hv1,
      DensCongPf.cong_act H _ P K hP v hv2⟩, (DensCongPf.psi_mk H abelian₂ _ P hP v).symm⟩
  refine Nat.card_congr
    { toFun := fun x => ⟨DensCongPf.psi H abelian₂ ((algebraMap F E) ↑ϖ) B hB x.1, by
        have h := fwd _ B A hB hA hBA hAB x.1 x.2
        rw [hG] at h
        exact h⟩
      invFun := fun x => ⟨DensCongPf.psi H abelian₂ ((algebraMap F E) ↑ϖ) A hA x.1,
        fwd G A B hA hB hAB hBA x.1 x.2⟩
      left_inv := fun x => Subtype.ext (DensCongPf.psi_psi H abelian₂ _ B A hB hA hBA x.1)
      right_inv := fun x => Subtype.ext (DensCongPf.psi_psi H abelian₂ _ A B hA hB hAB x.1) }

end Formalism.L2.SG.Pf
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DetZhatSwapUnit
section
noncomputable section

open ValuativeRel Matrix

namespace Formalism.L2.SG.LsDatumA

open Formalism.MainNotions.S.Loc

section CR2

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) {r : ℕ}

theorem U_swap (f f' : Fin (r + 1) → V) :
    Submodule.span E (Set.range (Sum.elim f' f)) = Submodule.span E (Set.range (Sum.elim f f')) := by
  rw [Set.Sum.elim_range, Set.Sum.elim_range, Set.union_comm]

theorem Zhat_swap (f f' : Fin (r + 1) → V) :
    H.Zhat f' f = ((M.L.cj.toRingEquiv.toRingHom).mapMatrix (H.Zhat f f'))ᵀ := by
  ext a b
  simp only [HermSp.Zhat, Matrix.transpose_apply, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]
  exact H.h_herm _ _

theorem om'_swap (f f' : Fin (r + 1) → V) : H.om' f' f = H.om f f' := by
  unfold HermSp.om' HermSp.om
  rw [Zhat_swap, ← Matrix.adjugate_transpose, ← RingHom.map_adjugate]
  simp only [Matrix.transpose_apply, RingHom.mapMatrix_apply, Matrix.map_apply]
  rfl

theorem det_Zhat_swap_unit (f f' : Fin (r + 1) → V) (h : IsUnit (H.Zhat f f').det) :
    IsUnit (H.Zhat f' f).det := by
  rw [Zhat_swap, Matrix.det_transpose, ← RingHom.map_det]
  exact h.map _

theorem cond_second_of_iso (g₁ g₁' g₂ g₂' : Fin (r + 1) → V) (T₁ T₂ : F) (hF₁ : Formalism.MainNotions.ThinScalesBound.FrameK H g₁ T₁)
    (hF₂ : Formalism.MainNotions.ThinScalesBound.FrameK H g₂ T₂) (hZ₁ : IsUnit (H.Zhat g₁ g₁').det) (χ : H.Wb g₁ ≃ₗ[E] H.Wb g₂) (κ : E)
    (hz : χ (H.mkW g₁ ⟨g₁ (Fin.last r), z_mem_perpX H hF₁⟩) = H.mkW g₂ ⟨g₂ (Fin.last r), z_mem_perpX H hF₂⟩)
    (ho : χ (H.mkW g₁ ⟨H.om' g₁ g₁', om'_mem_perpX H _ _⟩) = κ • H.mkW g₂ ⟨H.om' g₂ g₂', om'_mem_perpX H _ _⟩) :
    ∀ u ∈ Submodule.span E (Set.range (Sum.elim g₁ g₁')), ∀ hu : u ∈ H.perp (H.X g₁),
      ∃ u' ∈ Submodule.span E (Set.range (Sum.elim g₂ g₂')), ∃ hu' : u' ∈ H.perp (H.X g₂),
        χ (H.mkW g₁ ⟨u, hu⟩) = H.mkW g₂ ⟨u', hu'⟩ := by
  intro u hu hup
  obtain ⟨x, hx, β, γ, hxe⟩ := decomp_U_perpX H hF₁ hZ₁ hu hup
  let zP₁ : ↥(H.perp (H.X g₁)) := ⟨g₁ (Fin.last r), z_mem_perpX H hF₁⟩
  let oP₁ : ↥(H.perp (H.X g₁)) := ⟨H.om' g₁ g₁', om'_mem_perpX H _ _⟩
  let zP₂ : ↥(H.perp (H.X g₂)) := ⟨g₂ (Fin.last r), z_mem_perpX H hF₂⟩
  let oP₂ : ↥(H.perp (H.X g₂)) := ⟨H.om' g₂ g₂', om'_mem_perpX H _ _⟩
  have h1 : H.mkW g₁ ⟨u, hup⟩ = H.mkW g₁ (β • zP₁ + γ • oP₁) := by
    apply mkW_eq_of_sub_mem
    show u - (β • g₁ (Fin.last r) + γ • H.om' g₁ g₁') ∈ H.X g₁
    rw [hxe]
    convert hx using 1
    abel
  refine ⟨((β • zP₂ + (γ * κ) • oP₂ : ↥(H.perp (H.X g₂))) : V), ?_, (β • zP₂ + (γ * κ) • oP₂).2, ?_⟩
  · exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inl (Fin.last r), rfl⟩))
      (Submodule.smul_mem _ _ (om'_mem_U H g₂ g₂'))
  · rw [h1]
    simp only [map_add (f := _), map_smul]
    rw [show χ (H.mkW g₁ zP₁) = H.mkW g₂ zP₂ from hz, show χ (H.mkW g₁ oP₁) = κ • H.mkW g₂ oP₂ from ho, smul_smul]

end CR2

end Formalism.L2.SG.LsDatumA
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarCohPfD
section
noncomputable section

open ValuativeRel Matrix

namespace Formalism.MainNotions.S.Loc.HermSp.CohU

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V}

theorem coef_zero {ι : Type} [Fintype ι] [DecidableEq ι] {v : ι → V} (hN : GramInv H v) {c : ι → E}
    (h0 : ∀ i, H.h (∑ j, c j • v j) (v i) = 0) : c = 0 := by
  obtain ⟨N, -, hNG⟩ := hN
  have hG : H.gram v *ᵥ c = 0 := by
    funext i
    have h := h0 i
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hL_apply, map_sum] at h
    simp only [map_smul, hL_apply, smul_eq_mul] at h
    simp only [Matrix.mulVec, dotProduct, HermSp.gram, Matrix.of_apply, Pi.zero_apply]
    rw [← h]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have h := congrArg (fun x => N *ᵥ x) hG
  simp only [Matrix.mulVec_mulVec, hNG, Matrix.one_mulVec, Matrix.mulVec_zero] at h
  exact h

theorem linInd_of_gramInv {ι : Type} [Fintype ι] [DecidableEq ι] {v : ι → V} (hN : GramInv H v) :
    LinearIndependent E v := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have h := coef_zero hN (c := g) (fun k => by rw [hg]; exact H.h_zero_left _)
  exact congrFun h i

theorem prim_of_gramInv {ι : Type} [Fintype ι] [DecidableEq ι] {v : ι → V} (hN : GramInv H v)
    {Λ : Submodule M.L.O V} (hI : ∀ x ∈ Λ, ∀ y ∈ Λ, H.h x y ∈ M.L.O) (hv : ∀ i, v i ∈ Λ) : H.Prim Λ v := by
  refine ⟨hv, linInd_of_gramInv hN, fun x hx hxs => ?_⟩
  obtain ⟨c, hc, hw⟩ := decomp hN hI hv hx
  have hw0 : x - ∑ j, c j • v j = 0 := eq_zero_of_orth hN (Submodule.sub_mem _ hxs (comb_mem_span v c)) hw
  rw [sub_eq_zero.1 hw0]
  exact Submodule.sum_mem _ fun j _ =>
    (Submodule.span M.L.O (Set.range v)).smul_mem (⟨c j, hc j⟩ : M.L.O) (Submodule.subset_span ⟨j, rfl⟩)

theorem prim_inr {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₁] [DecidableEq ι₂] {a : ι₁ → V}
    {b : ι₂ → V} (hN : GramInv H (Sum.elim a b)) {Λ : Submodule M.L.O V}
    (hI : ∀ x ∈ Λ, ∀ y ∈ Λ, H.h x y ∈ M.L.O) (hv : ∀ k, Sum.elim a b k ∈ Λ) : H.Prim Λ b := by
  refine ⟨fun j => hv (Sum.inr j), (linInd_of_gramInv hN).comp Sum.inr Sum.inr_injective, fun x hx hxs => ?_⟩
  obtain ⟨c, hc, hw⟩ := decomp hN hI hv hx
  have hsp : Submodule.span E (Set.range b) ≤ Submodule.span E (Set.range (Sum.elim a b)) :=
    Submodule.span_mono (by rintro _ ⟨j, rfl⟩; exact ⟨Sum.inr j, rfl⟩)
  have hw0 : x - ∑ k, c k • Sum.elim a b k = 0 :=
    eq_zero_of_orth hN (Submodule.sub_mem _ (hsp hxs) (comb_mem_span _ c)) hw
  have hx' : x = ∑ k, c k • Sum.elim a b k := sub_eq_zero.1 hw0
  obtain ⟨e, he⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hxs
  have hsum : ∑ k, Sum.elim (0 : ι₁ → E) e k • Sum.elim a b k = x := by
    rw [Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, zero_smul, Finset.sum_const_zero, zero_add]
    exact he
  have hz : ∑ k, (c k - Sum.elim (0 : ι₁ → E) e k) • Sum.elim a b k = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib]
    rw [hsum, ← hx', sub_self]
  have hce := Fintype.linearIndependent_iff.1 (linInd_of_gramInv hN) _ hz
  have hl : ∀ i, c (Sum.inl i) = 0 := fun i => by
    have h := hce (Sum.inl i)
    simpa using h
  have hx2 : x = ∑ j, c (Sum.inr j) • b j := by
    conv_lhs => rw [hx']
    rw [Fintype.sum_sum_type]
    simp [hl]
  rw [hx2]
  exact Submodule.sum_mem _ fun j _ =>
    (Submodule.span M.L.O (Set.range b)).smul_mem (⟨c (Sum.inr j), hc _⟩ : M.L.O) (Submodule.subset_span ⟨j, rfl⟩)

end Formalism.MainNotions.S.Loc.HermSp.CohU

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open CohCut

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem vP_eq {p : PlF D} (γ : TermDef.Term D u u' F0 what₂) (F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
    (hs : (Zd.M p).split = none) : vP Zd p γ F'₂ = Sum.elim (tLoc Zd p γ).f (locF' Zd p F'₂) := by
  unfold vP Formalism.MainNotions.S.Loc.HermSp.MMfam
  rw [hs]
  rfl

variable (u u' F0 what₂)

def CohInt : Prop :=
  CtxP u u' F0 what₂ →
  ∀ (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D) (F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
    (φ' : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂)),
    CohHyp Zd γ Z F'₂ φ' →
    {p | ¬ ∀ b, locF' Zd p F'₂ b ∈ lattice₂ D Zd.M p γ.lam}.Finite

def CohDG : Prop :=
  CtxP u u' F0 what₂ →
  ∀ (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D) (F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
    (φ' : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂)),
    CohHyp Zd γ Z F'₂ φ' →
    {p | ¬ (IsUnit ((locH Zd p).Dl (tLoc Zd p γ).f (locF' Zd p F'₂) (D.R.rS + 1)) ∧
      (locH Zd p).Gdet (tLoc Zd p γ).f (locF' Zd p F'₂) (tLoc Zd p γ).T (tLoc Zd p γ).T' ≠ 0)}.Finite

variable {u u' F0 what₂}

theorem cohGen_of (hInt : CohInt Zd u u' F0 what₂) (hDG : CohDG Zd u u' F0 what₂) (hGood : CohGood Zd u u' F0 what₂) :
    CohGen Zd u u' F0 what₂ := by
  intro hP γ Z F'₂ φ' hH
  refine (((hInt hP γ Z F'₂ φ' hH).union (hDG hP γ Z F'₂ φ' hH)).union
    ((hGood hP γ Z F'₂ φ' hH).union (split_finite Zd))).subset ?_
  intro p hp
  by_contra hn
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hn
  obtain ⟨⟨hi, hdg⟩, hN, hs⟩ := hn
  have hsn : (Zd.M p).split = none := Option.not_isSome_iff_eq_none.1 hs
  apply hp
  have T1 := hH.2.2.2 p
  have sd := T1.1.1.1
  have frf := T1.1.1.2.1
  have frf' := T1.1.1.2.2.1
  have hI : ∀ x ∈ lattice₂ D Zd.M p γ.lam, ∀ y ∈ lattice₂ D Zd.M p γ.lam, (locH Zd p).h x y ∈ (Zd.M p).L.O :=
    fun x hx => (sd.2.2 x).1 hx
  have hv' : ∀ k, Sum.elim (tLoc Zd p γ).f (locF' Zd p F'₂) k ∈ lattice₂ D Zd.M p γ.lam := by
    intro k
    cases k with
    | inl a => exact frf.1.1 a
    | inr b => exact hi b
  have hN' := hN
  rw [vP_eq Zd γ F'₂ hsn] at hN'
  have hv : ∀ k, vP Zd p γ F'₂ k ∈ lattice₂ D Zd.M p γ.lam := by
    rw [vP_eq Zd γ F'₂ hsn]
    exact hv'
  have hfr2 : (locH Zd p).IsFrame (lattice₂ D Zd.M p γ.lam) D.R.rS (locF' Zd p F'₂) (tLoc Zd p γ).T' :=
    ⟨Formalism.MainNotions.S.Loc.HermSp.CohU.prim_inr hN' hI hv', T1.2.2.1.1, T1.2.2.1.2, frf'.2.2.2.1, frf'.2.2.2.2⟩
  refine ⟨⟨sd, frf, hfr2, hdg.1, hdg.2, fun g hg => ?_⟩, ?_⟩
  · rw [hsn] at hg
    cases hg
  · exact Formalism.MainNotions.S.Loc.HermSp.CohU.prim_of_gramInv hN hI hv

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.IntDiag
section
noncomputable section

namespace Formalism.L2.SG.Pf.TupGlobApprox

open Formalism.L2.SG.Pf.AtPt Formalism.L2.SG.Pf.ProdEApprox Formalism.L2.SG.Pf.PCount ValuativeRel

section IntM

variable {K : Type*} [CommRing K] (I : Subring K) {n : ℕ}

theorem int_mul {A B : Matrix (Fin n) (Fin n) K} (hA : ∀ i j, A i j ∈ I) (hB : ∀ i j, B i j ∈ I) :
    ∀ i j, (A * B) i j ∈ I := by
  intro i j
  rw [Matrix.mul_apply]
  exact I.sum_mem fun k _ => I.mul_mem (hA i k) (hB k j)

theorem int_diag {d : Fin n → K} (hd : ∀ a, d a ∈ I) : ∀ i j, Matrix.diagonal d i j ∈ I := by
  intro i j
  rw [Matrix.diagonal_apply]
  split_ifs
  · exact hd i
  · exact I.zero_mem

end IntM

section Good

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.TupGlob
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D)

theorem gY_int (p : PlF D) (w : Point D.host.E (D.R.rS + 1)) {U₁ X' : PairVal.MatR D} (hX' : IsLo X')
    (hpat : ∀ i j, fσ w j < fσ w i → X' i j = 0) (hU : ∀ i j, (D.s.atP p).ιE (U₁ i j) ∈ (D.s.atP p).O)
    (hU' : ∀ i j, (D.s.atP p).ιE (U₁⁻¹ i j) ∈ (D.s.atP p).O)
    (hν : ∀ a : Fin (D.R.rS + 1), (D.s.atP p).ιE (pv w.1 a) ∈ (D.s.atP p).O)
    (hν' : ∀ a : Fin (D.R.rS + 1), (D.s.atP p).ιE (pv w.1 a)⁻¹ ∈ (D.s.atP p).O)
    (hX : ∀ i j, (D.s.atP p).ιE (X' i j) ∈ (D.s.atP p).O) :
    ∀ i j, ((gY w U₁ X').map (D.s.atP p).ιE) i j ∈ (D.s.atP p).O := by
  have hν0 : ∀ a : Fin (D.R.rS + 1), IsUnit (pv w.1 a) := fun a => IsUnit.mk0 _ (pv_ne' w a)
  have hup := cOf_up (fσ_fσ w) (fun a => pv w.1 a) X' hX'.1 hpat hν0
  have hc : IsUp (cOf (fσ w) (fun a => pv w.1 a) X') := ⟨hup.1, fun a b hab => hup.2 b a hab⟩
  have hcm : ∀ i j, ((cOf (fσ w) (fun a => pv w.1 a) X').map (D.s.atP p).ιE) i j ∈ (D.s.atP p).O := by
    intro i j
    simp only [Matrix.map_apply, cOf, Matrix.of_apply, Ring.inverse_eq_inv', map_mul]
    exact (D.s.atP p).O.mul_mem ((D.s.atP p).O.mul_mem (hν' _) (hX _ _)) (hν _)
  have hci : ∀ i j, (((cOf (fσ w) (fun a => pv w.1 a) X')⁻¹).map (D.s.atP p).ιE) i j ∈ (D.s.atP p).O := by
    intro i j
    rw [ZsVolGrp.inv_eq_adj (det_up' hc)]
    have e := RingHom.map_adjugate (D.s.atP p).ιE (cOf (fσ w) (fun a => pv w.1 a) X')
    rw [RingHom.mapMatrix_apply, RingHom.mapMatrix_apply] at e
    rw [e]
    exact ZsVolGrp.adj_mem (D.s.atP p).O hcm i j
  simp only [gY, Matrix.map_mul]
  exact int_mul _ (int_mul _ hU' hci) hU

theorem good_at (p : PlF D) (hM : (Zd.M p).split = none) (w : Point D.host.E (D.R.rS + 1))
    {L₁ U₁ A₀ B₀ X' : PairVal.MatR D} (hL₁ : IsLo L₁) (hU₁ : IsUp U₁) (hA₀ : IsLo A₀) (hB₀ : IsUp B₀)
    (hX' : IsLo X') (hpat : ∀ i j, fσ w j < fσ w i → X' i j = 0)
    (hcf : ∀ a, algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cf Zd p a) ∈ (D.s.atP p).O)
    (hcfi : ∀ a, algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cfi Zd p a) ∈ (D.s.atP p).O)
    (hA : ∀ i j, (D.s.atP p).ιE (A₀ i j) ∈ (D.s.atP p).O) (hB : ∀ i j, (D.s.atP p).ιE (B₀ i j) ∈ (D.s.atP p).O)
    (hL : ∀ i j, (D.s.atP p).ιE (L₁ i j) ∈ (D.s.atP p).O) (hL' : ∀ i j, (D.s.atP p).ιE (L₁⁻¹ i j) ∈ (D.s.atP p).O)
    (hU : ∀ i j, (D.s.atP p).ιE (U₁ i j) ∈ (D.s.atP p).O) (hU' : ∀ i j, (D.s.atP p).ιE (U₁⁻¹ i j) ∈ (D.s.atP p).O)
    (hν : ∀ a : Fin (D.R.rS + 1), (D.s.atP p).ιE (pv w.1 a) ∈ (D.s.atP p).O)
    (hν' : ∀ a : Fin (D.R.rS + 1), (D.s.atP p).ιE (pv w.1 a)⁻¹ ∈ (D.s.atP p).O)
    (hX : ∀ i j, (D.s.atP p).ιE (X' i j) ∈ (D.s.atP p).O) : GoodAt Zd p w L₁ U₁ A₀ B₀ X' := by
  obtain ⟨hgX, hgY, -⟩ : IsLo (gX L₁ X') ∧ IsUp (gY w U₁ X') ∧ True := by
    have hν0 : ∀ a : Fin (D.R.rS + 1), IsUnit (pv w.1 a) := fun a => IsUnit.mk0 _ (pv_ne' w a)
    have hup := cOf_up (fσ_fσ w) (fun a => pv w.1 a) X' hX'.1 hpat hν0
    have hc : IsUp (cOf (fσ w) (fun a => pv w.1 a) X') := ⟨hup.1, fun a b hab => hup.2 b a hab⟩
    exact ⟨isLo_mul (isLo_mul hL₁ hX') (isLo_inv hL₁), isUp_mul (isUp_mul (isUp_inv hU₁) (isUp_inv hc)) hU₁, trivial⟩
  have hgYi := gY_int p w hX' hpat hU hU' hν hν' hX
  have hR : (Zd.M p).R = (D.s.atP p).O := Formalism.L2.SG.Pf.LMK.R_eq_O (Zd.agree p) hM
  have hlo := locL_lo Zd p (isLo_mul hA₀ hgX) (isUp_mul hgY hB₀)
  have hup := locR_up Zd p (isLo_mul hA₀ hgX) (isUp_mul hgY hB₀)
  refine ⟨⟨hlo.1, hlo.2, fun i j => ?_⟩, ⟨hup.1, fun a b hab => hup.2 b a hab, fun i j => ?_⟩⟩
  · rw [hR, locL_L Zd p hM]
    refine int_mul _ (int_mul _ (int_diag _ hcf) ?_) (int_diag _ hcfi) i j
    simp only [gX, Matrix.map_mul]
    exact int_mul _ hA (int_mul _ (int_mul _ hL hX) hL')
  · rw [hR, locR_L Zd p hM]
    refine int_mul _ (int_mul _ (int_diag _ hcfi) ?_) (int_diag _ hcf) i j
    rw [Matrix.map_mul]
    exact int_mul _ hgYi hB

end Good

end Formalism.L2.SG.Pf.TupGlobApprox
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.KloostermanDiagonalOfConditions
section
noncomputable section

open Formalism.L2.SG.Full Formalism.L2.SG.KappaOffDiagonal

namespace Formalism.L2.SG.KappaOffDiagonal

theorem corankPosC_holds : Formalism.L2.SG.RowsConc.CorankPosC :=
  fun _ _ Y u u' _ => Formalism.L2.SG.Pf.SatGram.corankPos_tO Y u u'

end Formalism.L2.SG.KappaOffDiagonal
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThSomeClose
section
noncomputable section

namespace Formalism.L2.SG.Pf

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem thSome_holds {D : Formalism.BasicNotions.D7} {δ : ∀ p : PlF D, (D.s.atP p).Fp}
    {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep} (hA : ∀ p, Agree δ M p) {u u' : D.what₂.Word}
    (hT : (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2])
    {F0 : FlagG (VS D) D.R.rS (Formalism.L2.SG.CntLocal.Tn u)} {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}
    (hrows : IsRowReps D F0 what₂) (hNR : NormRepElig u u' F0 what₂) :
    ThSome M δ u u' F0 what₂ := by
  refine thSome_holds_of hA hNR fun γ w hγ p a b => ?_
  obtain ⟨Λ, hΛ, F', hF'⟩ := dnInDens_of hNR hrows γ w hγ
  exact PI.CntNotIntW.integral_on_pairs_holds D δ M hA u u' hT F0 what₂ hrows Λ hΛ (zT γ) F' hF' p a b

end Formalism.L2.SG.Pf
end
end

