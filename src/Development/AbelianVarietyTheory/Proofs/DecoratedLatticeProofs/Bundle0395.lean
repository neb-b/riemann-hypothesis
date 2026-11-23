module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0347
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PinnedLocalGroupsHaveLevel
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0351
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0027
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0276
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0291
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0322
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0091
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0367
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceCharacterConductorIntegers
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0371
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0352
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0101
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0349
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedThetaSeriesTermsLawsUnipotentRational
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsotropicUnipotentRadicalsRationalCocompact
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0357
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0049

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPointBaseLatticeCoordsIntegralLastInPrime
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocMod.SplitCoord

open GlobalTheory.FinPl


set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem coord_int_last : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (P : HeightOneSpectrum (𝓞 D.host.E)), Formalism.L2.NTheta.IsIdemAt p.e P → ∀ (n : ℕ) (t : 𝓞 D.host.E), t ∈ P.asIdeal → ∀ (Lb : Submodule (𝓞 D.host.E) (Fin n → D.host.E)), (∀ x, x ∈ Lb ↔ ∀ j : Fin n, ∃ r : 𝓞 D.host.E, x j = (r : D.host.E) ∧ (j.1 + 1 = n → t ∣ r)) → ∀ y : Fin n → AE D, (fun r => Formalism.UG.prV (E := D.host.E) p.v (toEAf D (y r))) ∈ Formalism.UG.latS (F := D.host.F) (p.v.adicCompletion D.host.F) (intV D.host.E p.v) Lb → ∀ r, p.pr (y r) ∈ 𝒪[k] ∧ (r.1 + 1 = n → valuation k (p.pr (y r)) < 1) := by
  intro D k _ _ _ _ p P hP n t ht Lb hLb y hy
  obtain ⟨π₀, hπ₀, -, hint, -⟩ := GlobalTheory.LocMod.LevBack.exists_chart p hP

  have he : toEAf D p.e = Formalism.UG.P.afsplitEps D.host.E p.v * toEAf D p.e := by
    obtain ⟨ε, hε, hsum⟩ := p.above
    have hee : algebraMap (AF D.host.F) (AE D) ε * p.e = p.e := by
      rw [← hsum, add_mul, p.split.1, mul_comm (cA D p.e) p.e, p.split.2.1, add_zero]
    rw [← sub_eq_zero]
    refine Formalism.UG.P.afsplit_inj _ fun w => ?_
    rw [map_sub, map_mul]
    by_cases hw : w = p.v
    · subst hw; rw [Formalism.UG.P.afsplit_prV_eps, one_mul, sub_self]
    · rw [← hee, GlobalTheory.AdForm.ChiStd.prV_toEAf_idem_mul hε hw, mul_zero, sub_zero]
  have hpe : π₀ (toEAf D p.e) = 1 := by rw [hπ₀]; exact GlobalTheory.LocMod.LevBack.pr_e p
  have heps : π₀ (Formalism.UG.P.afsplitEps D.host.E p.v) = 1 := by
    have h1 := congrArg π₀ he
    rw [map_mul, hpe, mul_one] at h1
    exact h1.symm

  let π : D.host.E ⊗[D.host.F] p.v.adicCompletion D.host.F →+* k :=
    { toFun := fun s => π₀ (Formalism.UG.P.afsplitIE p.v s)
      map_one' := heps
      map_mul' := fun a b => by
        show π₀ (Formalism.UG.P.afsplitIE p.v (a * b)) = π₀ (Formalism.UG.P.afsplitIE p.v a) * π₀ (Formalism.UG.P.afsplitIE p.v b)
        rw [map_mul (Formalism.UG.P.afsplitIE p.v), map_mul π₀]
      map_zero' := by
        show π₀ (Formalism.UG.P.afsplitIE p.v 0) = 0
        rw [map_zero (Formalism.UG.P.afsplitIE p.v), map_zero π₀]
      map_add' := fun a b => by
        show π₀ (Formalism.UG.P.afsplitIE p.v (a + b)) = π₀ (Formalism.UG.P.afsplitIE p.v a) + π₀ (Formalism.UG.P.afsplitIE p.v b)
        rw [map_add (Formalism.UG.P.afsplitIE p.v), map_add π₀] }
  have hπ : ∀ z, π (Formalism.UG.prV (E := D.host.E) p.v z) = π₀ z := fun z => by
    change π₀ (Formalism.UG.P.afsplitIE p.v _) = _
    rw [Formalism.UG.P.afsplit_decomp, map_mul, heps, one_mul]

  have hV : intV D.host.E p.v ≤ (𝒪[k]).comap π := by
    refine Subring.closure_le.2 ?_
    rintro s (⟨x, rfl⟩ | ⟨x, rfl⟩)
    · change π (Formalism.UG.prV (E := D.host.E) p.v ((x : D.host.E) ⊗ₜ[D.host.F] (1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F))) ∈ 𝒪[k]
      rw [hπ]
      exact hint ⟨_, Subring.subset_closure (Or.inl ⟨x, rfl⟩)⟩
    · change π₀ ((1 : D.host.E) ⊗ₜ[D.host.F] Formalism.UG.P.afsplitI p.v (x : p.v.adicCompletion D.host.F)) ∈ 𝒪[k]
      exact hint ⟨_, Subring.subset_closure (Or.inr ⟨⟨_, Formalism.UG.P.afsplitI_mem_intAd p.v _ x.2⟩, rfl⟩)⟩

  have key : ∀ w ∈ Formalism.UG.latS (F := D.host.F) (p.v.adicCompletion D.host.F) (intV D.host.E p.v) Lb,
      ∀ r : Fin n, π (w r) ∈ 𝒪[k] ∧ (r.1 + 1 = n → valuation k (π (w r)) < 1) := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨x, hxL, rfl⟩ := hx
      intro r
      obtain ⟨ρ, hρ, hlast⟩ := (hLb x).1 hxL r
      have h0 : π (Formalism.UG.inclE (F := D.host.F) (p.v.adicCompletion D.host.F) (x r)) = p.pr (incA D (ρ : D.host.E)) := by
        rw [hρ]
        change π (Formalism.UG.prV (E := D.host.E) p.v ((ρ : D.host.E) ⊗ₜ[D.host.F] (1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F))) = _
        rw [hπ, ← hπ₀]
        rfl
      refine ⟨?_, fun hr => ?_⟩
      · change π (Formalism.UG.inclE (F := D.host.F) (p.v.adicCompletion D.host.F) (x r)) ∈ 𝒪[k]
        have hq : toEAf D (incA D (ρ : D.host.E)) =
            (ρ : D.host.E) ⊗ₜ[D.host.F] (1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) := by
          first | rfl | simp [toEAf, finPart, incA]
        have hm : toEAf D (incA D (ρ : D.host.E)) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
          rw [hq]; exact Subring.subset_closure (Or.inl ⟨⟨(ρ : D.host.E), ρ, rfl⟩, rfl⟩)
        rw [h0, ← hπ₀]
        exact hint ⟨_, hm⟩
      · change valuation k (π (Formalism.UG.inclE (F := D.host.F) (p.v.adicCompletion D.host.F) (x r))) < 1
        rw [h0, ← GlobalTheory.LocMod.LevBack.pr_lt p hP]
        obtain ⟨c, hc⟩ := hlast hr
        rw [hc]; exact Ideal.mul_mem_right _ _ ht
    | zero =>
      intro r
      simp
    | add a b _ _ ha hb =>
      intro r
      refine ⟨?_, fun hr => ?_⟩
      · rw [Pi.add_apply, map_add (f := _)]; exact add_mem (ha r).1 (hb r).1
      · rw [Pi.add_apply, map_add (f := _)]; exact Valuation.map_add_lt _ ((ha r).2 hr) ((hb r).2 hr)
    | smul s a _ ha =>
      intro r
      have hs : π s ∈ 𝒪[k] := hV s.2
      have e1 : π ((s • a) r) = π s * π (a r) := by
        rw [Pi.smul_apply, Subring.smul_def, smul_eq_mul, map_mul]
      refine ⟨?_, fun hr => ?_⟩
      · rw [e1]; exact mul_mem hs (ha r).1
      · rw [e1, map_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_left' ((Valuation.mem_integer_iff _ _).1 hs)) ((ha r).2 hr)
  intro r
  have h := key _ hy r
  rw [hπ, hπ₀] at h
  exact h

end GlobalTheory.LocMod.SplitCoord
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StabilizesSelfDualIffFrameMatrixStabilizes
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Pointwise

noncomputable section

namespace GlobalTheory.FrameMoves

variable {D : D7}

theorem mulVec_of_grpOff (S : HSp D) {v : Pl D} {h : GA D S} (hh : h ∈ grpOff S (· = v))
    {y : Fin S.rank → AE D} (hy : ∀ i, y i ∈ idAt D (· = v)) : mt S h *ᵥ y = y := by
  have hM := (GlobalTheory.FinPlLoc.mem_grpOff_iff (· = v) h).1 hh
  have hij : ∀ i j, GlobalTheory.FinPlLoc.idem D (· = v) * mt S h i j =
      GlobalTheory.FinPlLoc.idem D (· = v) * (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j := by
    intro i j
    have := congrFun (congrFun hM i) j
    simp only [GlobalTheory.FinPlLoc.mix, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] at this
    linear_combination (-1 : AE D) * this
  have hy' : ∀ j, GlobalTheory.FinPlLoc.idem D (· = v) * y j = y j := fun j =>
    (GlobalTheory.FinPlLoc.mem_idAt_iff _ _).1 (hy j)
  ext i
  calc (mt S h *ᵥ y) i = ∑ j, mt S h i j * y j := rfl
    _ = ∑ j, (GlobalTheory.FinPlLoc.idem D (· = v) * mt S h i j) * y j := by
        refine Finset.sum_congr rfl fun j _ => ?_
        conv_lhs => rw [← hy' j]
        ring
    _ = ∑ j, (GlobalTheory.FinPlLoc.idem D (· = v) * (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j) * y j := by
        simp_rw [hij]
    _ = y i := by
        simp [Matrix.one_apply, hy' i]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem map_pr_of_grpOff (p : SplitPt D k) (S : HSp D) {h : GA D S} (hh : h ∈ grpOff S (· = p.v)) :
    (mt S h).map p.pr = 1 := by
  have hM := (GlobalTheory.FinPlLoc.mem_grpOff_iff (· = p.v) h).1 hh
  have hij : ∀ i j, GlobalTheory.FinPlLoc.idem D (· = p.v) * mt S h i j =
      GlobalTheory.FinPlLoc.idem D (· = p.v) * (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j := by
    intro i j
    have := congrFun (congrFun hM i) j
    simp only [GlobalTheory.FinPlLoc.mix, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] at this
    linear_combination (-1 : AE D) * this
  have hpr : ∀ x, p.pr x = p.pr (p.e * x) := fun x => by rw [← p.sec_pr, p.pr_sec]
  have he : GlobalTheory.FinPlLoc.idem D (· = p.v) * p.e = p.e :=
    (GlobalTheory.FinPlLoc.mem_idAt_iff _ _).1 (GlobalTheory.FinPl.LatIndHalf.e_mem_idAt p)
  rw [← Matrix.map_one p.pr (map_zero _) (map_one _)]
  ext i j
  simp only [Matrix.map_apply]
  rw [hpr, hpr ((1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j), ← he, mul_comm (GlobalTheory.FinPlLoc.idem D _) p.e,
    mul_assoc, hij i j, ← mul_assoc]

theorem moves_iff_smul : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : GlobalTheory.FinPl.SplitPt D k) (A : HSp D) (n : Type) [Fintype n] [DecidableEq n] (β : GlobalTheory.FinPl.Frame p A n) (L : GlobalTheory.FinPl.Lat A) (Λ : Submodule 𝒪[k] (n → k)), IsSelfDualC A L → β.IsLat L Λ → ∀ κ : GA D A, (GlobalTheory.FinPl.Moves A κ L L (· = p.v) ↔ coordHom A p.pr β.b β.b' β.bb' β.b'b κ • Λ = Λ) := by
  intro D k _ _ _ _ p A n _ _ β L Λ hL hΛ κ
  obtain ⟨h1, -, -, h4, -, -⟩ := _root_.GlobalTheory.FrameAt.frame_facts D k p A n β
  obtain ⟨Λ', -, hΛ', hK⟩ := h4 L hL
  have hΛeq : Λ' = Λ := by
    ext x
    rw [hΛ' x, hΛ x]
  subst hΛeq
  obtain ⟨hv, hvAt, h', h'Off, rfl⟩ := (GlobalTheory.FinPlLoc.part_grp (· = p.v) A).1 κ
  obtain ⟨g, rfl⟩ := (h1 hv).1 hvAt
  have hoff : coordHom A p.pr β.b β.b' β.bb' β.b'b h' = 1 := by
    refine Units.ext ?_
    rw [coordHom_val, map_pr_of_grpOff p A h'Off, Matrix.mul_one, β.b'b]
    rfl
  have hg : coordHom A p.pr β.b β.b' β.bb' β.b'b (β.gl g) = g :=
    ((eq_coordHom_iff A p.pr β.b β.b' β.bb' β.b'b (β.gl g) g).1 (β.gl_mat g)).symm
  rw [map_mul, hoff, mul_one, hg, ← hK g]
  constructor
  · intro hm
    refine ⟨hvAt, fun y hy => ?_⟩
    rw [hm y hy, GlobalTheory.FinPlLoc.mt_mul, ← Matrix.mulVec_mulVec, mulVec_of_grpOff A h'Off hy]
  · rintro ⟨-, hm⟩ y hy
    rw [hm y hy, GlobalTheory.FinPlLoc.mt_mul, ← Matrix.mulVec_mulVec, mulVec_of_grpOff A h'Off hy]

end GlobalTheory.FrameMoves

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StdHomLatticePointIntegralMatrixAtSplitPlace
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.LocMod
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocMod.StdHomDown

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem pr_int_of_isIntegral (q : GlobalTheory.FinPl.SplitPt D k) {x : D.host.E} (hx : IsIntegral ℤ x) :
    q.pr (incA D x) ∈ 𝒪[k] := by
  have h1 : IsIntegral ℤ (q.pr (incA D x)) := hx.map ((q.pr.comp (incA D)).toIntAlgHom)
  exact (Valuation.integer.integers (valuation k)).mem_of_integral h1.tower_top

theorem star_isIntegral {x : D.host.E} (hx : IsIntegral ℤ x) : IsIntegral ℤ (star x) :=
  hx.map (starRingEnd D.host.E).toIntAlgHom

theorem tmul_eq (α : AF D.host.F) (y : D.host.E) :
    (α ⊗ₜ[D.host.F] y : AE D) = algebraMap (AF D.host.F) (AE D) α * incA D y := by
  change _ = (α ⊗ₜ[D.host.F] (1 : D.host.E)) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] y)
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

theorem down_mem_integer : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (S T : HSp D) (c : k), c ≠ 0 → (∀ a ∈ (D.host.AA : Set D.host.E), q.pr (incA D a) / c ∈ 𝒪[k]) → ∀ (FS : Frame k S.rank (Fin S.rank)) (FT : Frame k T.rank (Fin T.rank)), FT.β = 1 → FT.γ = 1 → FS.γ = c • (HSpace.gram S).map (fun a => q.pr (incA D a)) → ∀ u ∈ stdHom S T, ∀ r s, (Place.ofSplitPt q).down FS FT u r s ∈ 𝒪[k] := by
  intro D k _ _ _ _ q S T c hc hAA FS FT _ hγT hγS u hu
  set Gw : Matrix (Fin S.rank) (Fin S.rank) k := (HSpace.gram S).map (fun a => q.pr (incA D a)) with hGw
  have hGβ : Gw * FS.β = c⁻¹ • (1 : Matrix (Fin S.rank) (Fin S.rank) k) := by
    have h := FS.γβ
    rw [hγS, Matrix.smul_mul] at h
    rw [← h, smul_smul, inv_mul_cancel₀ hc, one_smul]
  induction hu using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, -, a, ha, s, hs, t, ht, rfl⟩ := hw
    intro r j
    set lam : k := q.pr (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α)) * q.pr (incA D a) with hlam
    let M : Matrix (Fin T.rank) (Fin S.rank) k := Matrix.of fun i l => lam * q.pr (incA D (t i)) * q.pr (incA D (star (s l)))
    have hmap : (Matrix.of fun i j => (pairA D.host.F 0 α) ⊗ₜ[D.host.F] (a * t i * ∑ l, star (s l) * S.gram l j) :
        WO S T).map q.pr = M * Gw := by
      ext i j
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Matrix.map_apply, Matrix.of_apply, Matrix.mul_apply, M, hGw, tmul_eq, map_mul, map_sum, hlam]
      simp only [Finset.mul_sum]
      exact Finset.sum_congr rfl fun l _ => by ring
    have hd : (Place.ofSplitPt q).down FS FT (Matrix.of fun i j => (pairA D.host.F 0 α) ⊗ₜ[D.host.F]
        (a * t i * ∑ l, star (s l) * S.gram l j)) = c⁻¹ • M := by
      have hπ : (Place.ofSplitPt q).π = q.pr := rfl
      simp only [Place.down, hπ]
      rw [hγT, Matrix.one_mul, hmap, Matrix.mul_assoc, hGβ, Matrix.mul_smul, Matrix.mul_one]
    rw [hd, Matrix.smul_apply, smul_eq_mul]
    have e : c⁻¹ * M r j = q.pr (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α)) * (q.pr (incA D a) / c) *
        q.pr (incA D (t r)) * q.pr (incA D (star (s j))) := by
      simp only [M, Matrix.of_apply, hlam]; field_simp
    rw [e]
    refine mul_mem (mul_mem (mul_mem (GlobalTheory.SplitCharCond.pr_pair_int q hα) (hAA a ha)) ?_) ?_
    · exact pr_int_of_isIntegral q (ht r)
    · exact pr_int_of_isIntegral q (star_isIntegral (hs j))
  | zero =>
    intro r j
    have : (Place.ofSplitPt q).down FS FT 0 = 0 := map_zero (Witness.downH (Place.ofSplitPt q) FS FT)
    rw [this]; exact zero_mem _
  | add x y _ _ hx hy =>
    intro r j
    rw [Witness.down_add, Matrix.add_apply]
    exact add_mem (hx r j) (hy r j)
  | neg x _ hx =>
    intro r j
    have : (Place.ofSplitPt q).down FS FT (-x) = -(Place.ofSplitPt q).down FS FT x :=
      map_neg (Witness.downH (Place.ofSplitPt q) FS FT) x
    rw [this, Matrix.neg_apply]
    exact neg_mem (hx r j)

end GlobalTheory.LocMod.StdHomDown
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaKernelMeanEqOrbitSumMean
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.Unf

theorem mean_theta_orbit : ∀ (D : D7), Descent D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (χV χW : (AE D)ˣ →* Circle) (om : Om V W) (om' : Om V₀ W), IsWeilDatumO ψ V W χV χW om → IsWeilDatumO ψ V₀ W χV χW om' → ∀ (vS : VolM D W.rank ρ) (vN : VolN d) (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E) (Th : GA D V → ℂ), IsBase W x₀ → IsTh ψ d W x₀ Th → ∀ Ψ : WO V W → ℂ, IsThetaFunO ψ V W Ψ → ∫ n in vN.𝓝, Th n.1 * om (n.1, 1) Ψ 0 ∂vN.ν = ∫ n in vN.𝓝, ∑' x : Orb W x₀, Th n.1 * term ψ d W vS (om (n.1, 1) Ψ) x.1 ∂vN.ν := by
  intro D hDesc ψ V V₀ W ρ d χV χW om om' hw hw' vS vN x₀ Th hB hTh Ψ hΨ
  have : Countable D.host.E := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableE
  have : Countable (Matrix (Fin W.rank) (Fin ρ) D.host.E) :=
    inferInstanceAs (Countable (Fin W.rank → Fin ρ → D.host.E))
  have hT := _root_.GlobalTheory.Unf.TermLaw.term_laws D ψ V V₀ W ρ d χV χW om om' hw hw' vS
  have hsum : ∀ n : flagN d, HasSum (term ψ d W vS (om (n.1, 1) Ψ)) (om (n.1, 1) Ψ 0) :=
    fun n => (hT _ (hw.om_pres _ _ hΨ)).2.2.2.2
  have hcont : ∀ x, Continuous fun n : flagN d => term ψ d W vS (om (n.1, 1) Ψ) x := fun x =>
    ((hT Ψ hΨ).2.2.2.1 x).comp (continuous_subtype_val.prodMk continuous_const)
  obtain ⟨C, A, hC⟩ := _root_.GlobalTheory.Unf.sum_term_bound D ψ V V₀ W ρ d χV χW om om' hw hw' vS Ψ hΨ
  have hbd : ∀ n : flagN d, ∑' x, ‖term ψ d W vS (om (n.1, 1) Ψ) x‖ₑ ≤
      ENNReal.ofReal (C * (height V 1 * quotHeight W 1) ^ A) := fun n => by
    have := hC 1 1 n.1 n.2
    rwa [mul_one] at this
  obtain ⟨K, hK, hcov⟩ := (GlobalTheory.Mem.UnipCocompact.radicals_cocompact D V ρ d.e (isIsoSub_e d)).1
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (f := fun n : flagN d => Th n.1) hTh.cont.continuousOn
  have hThb : ∀ n : flagN d, ‖Th n.1‖ ≤ M := by
    intro n
    obtain ⟨γ, hγ, k, hk, rfl⟩ := hcov n
    have hγ' : (γ : GA D V) ∈ GQ V := Subgroup.mem_subgroupOf.1 hγ
    have : Th ((γ * k : flagN d) : GA D V) = Th k.1 := hTh.left γ.1 hγ' γ.2 k.1 k.2
    rw [this]
    exact hM k hk
  have hpart : ∀ (S : Set (Matrix (Fin W.rank) (Fin ρ) D.host.E)) (n : flagN d),
      ‖∑' x : S, Th n.1 * term ψ d W vS (om (n.1, 1) Ψ) x.1‖ ≤
        M * max (C * (height V 1 * quotHeight W 1) ^ A) 0 := by
    intro S n
    rw [tsum_mul_left, norm_mul]
    refine mul_le_mul (hThb n) ?_ (norm_nonneg _) ((norm_nonneg _).trans (hThb n))
    have h1 : ‖∑' x : S, term ψ d W vS (om (n.1, 1) Ψ) x.1‖ₑ ≤
        ENNReal.ofReal (C * (height V 1 * quotHeight W 1) ^ A) :=
      enorm_tsum_le_tsum_enorm.trans
        ((ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective _).trans (hbd n))
    have h2 := ENNReal.toReal_mono ENNReal.ofReal_ne_top h1
    rwa [toReal_enorm, ENNReal.toReal_ofReal'] at h2
  have hmeas : ∀ S : Set (Matrix (Fin W.rank) (Fin ρ) D.host.E),
      AEStronglyMeasurable (fun n : flagN d => ∑' x : S, Th n.1 * term ψ d W vS (om (n.1, 1) Ψ) x.1)
        (vN.ν.restrict vN.𝓝) := by
    intro S
    refine aestronglyMeasurable_of_tendsto_ae (Filter.atTop : Filter (Finset S))
      (f := fun s n => ∑ x ∈ s, Th n.1 * term ψ d W vS (om (n.1, 1) Ψ) x.1) (fun s => ?_)
      (Filter.Eventually.of_forall fun n => ?_)
    · exact (continuous_finsetSum _ fun x _ => hTh.cont.mul (hcont x.1)).aestronglyMeasurable
    · exact (((hsum n).summable.mul_left (Th n.1)).subtype (fun x => x ∈ S)).hasSum
  have : IsFiniteMeasure (vN.ν.restrict vN.𝓝) :=
    isFiniteMeasure_restrict.2 (by rw [vN.unit.2.2]; exact ENNReal.one_ne_top)
  have hint : ∀ S : Set (Matrix (Fin W.rank) (Fin ρ) D.host.E),
      Integrable (fun n : flagN d => ∑' x : S, Th n.1 * term ψ d W vS (om (n.1, 1) Ψ) x.1)
        (vN.ν.restrict vN.𝓝) :=
    fun S => Integrable.of_bound (hmeas S) _ (Filter.Eventually.of_forall (hpart S))

  have h61 := fun x : Matrix (Fin W.rank) (Fin ρ) D.host.E => _root_.GlobalTheory.DepFrame.dependent_frame_first_relation D.host.E W.rank ρ x
  let Sb : Set (Matrix (Fin W.rank) (Fin ρ) D.host.E) := {x | gramQ W x ≠ gramQ W x₀}
  let Sj : Fin ρ → Set (Matrix (Fin W.rank) (Fin ρ) D.host.E) := fun j => {x | gramQ W x = gramQ W x₀ ∧
    ((∀ a : Fin ρ → D.host.E, (∀ i, j ≤ i → a i = 0) → x *ᵥ a = 0 → a = 0) ∧
      ∃ a : Fin ρ → D.host.E, a j = 1 ∧ (∀ i, j < i → a i = 0) ∧ x *ᵥ a = 0)}
  have hpt : ∀ n : flagN d, Th n.1 * om (n.1, 1) Ψ 0 =
      (∑' x : Sb, Th n.1 * term ψ d W vS (om (n.1, 1) Ψ) x.1) +
      (∑' x : Orb W x₀, Th n.1 * term ψ d W vS (om (n.1, 1) Ψ) x.1) +
      ∑ j, ∑' x : Sj j, Th n.1 * term ψ d W vS (om (n.1, 1) Ψ) x.1 := by
    intro n
    have hs : Summable fun x => Th n.1 * term ψ d W vS (om (n.1, 1) Ψ) x := (hsum n).summable.mul_left _
    rw [← ((hsum n).mul_left (Th n.1)).tsum_eq]
    have ht : ∀ S : Set (Matrix (Fin W.rank) (Fin ρ) D.host.E),
        ∑' x : S, Th n.1 * term ψ d W vS (om (n.1, 1) Ψ) x.1 =
          ∑' x, S.indicator (fun x => Th n.1 * term ψ d W vS (om (n.1, 1) Ψ) x) x := fun S => tsum_subtype S (fun x => Th n.1 * term ψ d W vS (om (n.1, 1) Ψ) x)
    rw [ht, ht, Finset.sum_congr rfl fun j _ => ht (Sj j)]
    rw [← Summable.tsum_finsetSum (fun j _ => hs.indicator _), ← Summable.tsum_add (hs.indicator _) (hs.indicator _),
      ← Summable.tsum_add ((hs.indicator _).add (hs.indicator _)) (summable_sum fun j _ => hs.indicator _)]
    congr 1
    funext x
    by_cases hg : gramQ W x = gramQ W x₀
    · have h1 : x ∉ Sb := fun h => h hg
      rw [Set.indicator_of_notMem h1, zero_add]
      by_cases hl : LinearIndependent D.host.E x.transpose
      · have h2 : x ∈ Orb W x₀ := ⟨hl, hg⟩
        have h3 : ∀ j, x ∉ Sj j := fun j h => (h61 x).1.2 ⟨j, h.2⟩ hl
        rw [Set.indicator_of_mem h2, Finset.sum_eq_zero fun j _ => Set.indicator_of_notMem (h3 j) _, add_zero]
      · have h2 : x ∉ Orb W x₀ := fun h => hl h.1
        obtain ⟨j, hj⟩ := (h61 x).1.1 hl
        rw [Set.indicator_of_notMem h2, zero_add, Finset.sum_eq_single j
          (fun j' _ hj' => Set.indicator_of_notMem (fun (h : x ∈ Sj j') => hj' ((h61 x).2.1 j' j h.2 hj)) _)
          (fun h => (h (Finset.mem_univ j)).elim), Set.indicator_of_mem (show x ∈ Sj j from ⟨hg, hj⟩)]
    · have h1 : x ∈ Sb := hg
      have h2 : x ∉ Orb W x₀ := fun h => hg h.2
      have h3 : ∀ j, x ∉ Sj j := fun j h => hg h.1
      rw [Set.indicator_of_mem h1, Set.indicator_of_notMem h2,
        Finset.sum_eq_zero fun j _ => Set.indicator_of_notMem (h3 j) _, add_zero, add_zero]
  have e1 : ∫ n in vN.𝓝, ∑' x : Sb, Th n.1 * term ψ d W vS (om (n.1, 1) Ψ) x.1 ∂vN.ν = 0 :=
    _root_.GlobalTheory.Unf.cut_gram_base D ψ V V₀ W ρ d χV χW om om' hw hw' vS vN x₀ Th hB hTh Ψ hΨ
  have e2 : ∀ j, ∫ n in vN.𝓝, ∑' x : Sj j, Th n.1 * term ψ d W vS (om (n.1, 1) Ψ) x.1 ∂vN.ν = 0 :=
    _root_.GlobalTheory.Unf.DepFrames.dep_frames_mean_zero D hDesc ψ V V₀ W ρ d χV χW om om' hw hw' vS vN x₀ Th hB hTh Ψ hΨ
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_add ?_ ?_, integral_add ?_ ?_,
    integral_finsetSum _ ?_, e1, Finset.sum_eq_zero fun j _ => e2 j, zero_add, add_zero]
  · exact fun j _ => hint _
  · exact hint _
  · exact hint _
  · exact (hint _).add (hint _)
  · exact integrable_finsetSum _ fun j _ => hint _

end GlobalTheory.Unf
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistPlaceLastTwoStepEntriesSchwartzBruhat
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.QPl.LastTwo

theorem entries_mem_SB : ∀ (D : D7) (c : Comm D) (v : VCom c) χ (Q : QAt v χ) α yb, Q.T.xiPen (box _ Q.c₂) (Q.rep Q.s 0 rfl α) yb ∈ SB _ ∧ Q.T.xiTop (box _ Q.c₂) Q.ψk Q.ν (-1) yb ∈ SB _ := by
  intro D c v χ Q α yb
  have hreg := Q.reg
  constructor
  · haveI := GlobalTheory.FinPl.Comm.t2Space_matrix_of_isNonarchimedeanLocalField (k := Q.k) (n := Q.X (Q.s + 1)) (n' := Q.X Q.s)
    refine GlobalTheory.FinPl.Comm.comp_mem_SB (om_mem_SB (Q.T.mu (Q.s + 1)) (Q.rep Q.s 0 rfl α) 1 (hreg.1 Q.s 0 rfl))
      (p := fun x₀ => withCol x₀ (Quotient.out yb)) (s := fun x => x.toBlocks₁₁) ?_ ?_ fun x => rfl
    · unfold withCol; fun_prop
    · exact continuous_pi fun i => continuous_pi fun j => (continuous_apply (Sum.inl j)).comp (continuous_apply (Sum.inl i))
  · haveI := GlobalTheory.FinPl.Comm.t2Space_matrix_of_isNonarchimedeanLocalField (k := Q.k) (n := Q.Z ⊕ Unit) (n' := Q.X (Q.s + 1))
    have hv1 : valuation Q.k (-1 : Q.k) = 1 := by simp
    have hh := (GlobalTheory.IndefiniteRowSideFullHecke.OmegaColumnSlices.hat_mem_SB_and_hat_omCol Q.k Q.ψk Q.ν (-1) Q.cond Q.unitVol hv1 (Q.X (Q.s + 1)) 1 1 _
      (cosetInd_mem_SB Q.c₂ yb)).1
    refine GlobalTheory.FinPl.Comm.prod_mem_SB hreg.2.1 hh
      (p := fun x : Matrix (Q.Z ⊕ Unit) (Q.X (Q.s + 1)) Q.k => fromCols x.toRows₁ (0 : Matrix Q.Z (Fin 0) Q.k))
      (r := fun x => x (Sum.inr ()))
      (s := fun z => fromRows z.1.toCols₁ (Matrix.of fun (_ : Unit) => z.2)) ?_ ?_ ?_ ?_
    · exact continuous_pi fun i => continuous_pi fun j => by
        rcases j with j | j
        · exact (continuous_apply j).comp (continuous_apply (Sum.inl i))
        · exact j.elim0
    · exact continuous_apply _
    · exact continuous_pi fun i => continuous_pi fun j => by
        rcases i with i | i
        · exact (continuous_apply (Sum.inl j)).comp ((continuous_apply i).comp continuous_fst)
        · exact (continuous_apply j).comp continuous_snd
    · intro x; ext (i | i) j <;> rfl

end GlobalTheory.QPl.LastTwo
end
end

