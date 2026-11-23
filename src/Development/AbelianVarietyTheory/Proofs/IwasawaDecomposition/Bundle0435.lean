module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0030
public import Formalism.LocalToGlobal.KernelLattices.TopPin
public import Formalism.LocalToGlobal.KernelLattices.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0425
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.DiagramFitsSourceRank
public import Formalism.UnipotentAdelicQuotients.Bundle0002
public import Formalism.LocalToGlobal.Divisibility.NumbersLemmas
public import Formalism.LocalToGlobal.Columns.TiedValLatG
public import Formalism.LocalToGlobal.GlobalTheory.GL4.PZBasis
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHermPosChainRealEndSpaceTuple
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowFiniteTypesIsotypicPartsSpanOrthogonal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0426
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0026
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.Bundle0005
public import Formalism.LocalRingCardinality.FactDelDualNabla
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0429
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0321

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemWeylLatticeIntegralSpanIffPadicFunction
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.Mem.IntSpanDelW

open Formalism.L2.GlobalTheoryTheory.TraceIntegrality

variable {ι : Type} [Fintype ι] {n : ℕ}

def evM {p : ℕ} [Fact p.Prime] (P : MvPolynomial (ι × Fin n × Fin n) ℂ_[p]) :
    (ι → Matrix (Fin n) (Fin n) ℂ_[p]) → ℂ_[p] :=
  fun y => MvPolynomial.eval (fun k : ι × Fin n × Fin n => y k.1 k.2.1 k.2.2) P

theorem ten_int_map (R : Type) [CommRing R] (f : ι → MvPolynomial (Fin n × Fin n) ℤ) :
    Formalism.L2.Forms.ten (fun τ => MvPolynomial.map (Int.castRingHom R) (f τ)) =
      MvPolynomial.map (Int.castRingHom R) (Formalism.MainNotions.flipTwoThree.ten f) := by
  unfold Formalism.L2.Forms.ten Formalism.MainNotions.flipTwoThree.ten
  rw [map_prod]
  exact Finset.prod_congr rfl fun τ _ => (MvPolynomial.map_rename _ _ _).symm

theorem prod_eval_eq_evM {p : ℕ} [Fact p.Prime] (f : ι → MvPolynomial (Fin n × Fin n) ℤ)
    (y : ι → Matrix (Fin n) (Fin n) ℂ_[p]) :
    ∏ τ, MvPolynomial.eval (fun k : Fin n × Fin n => y τ k.1 k.2) (MvPolynomial.map (Int.castRingHom ℂ_[p]) (f τ)) =
      evM (MvPolynomial.map (Int.castRingHom ℂ_[p]) (Formalism.MainNotions.flipTwoThree.ten f)) y := by
  unfold evM Formalism.MainNotions.flipTwoThree.ten
  rw [map_prod, map_prod]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [MvPolynomial.map_rename, MvPolynomial.eval_rename]
  rfl

theorem mem_vlIntSpan_iff {K : Type} [Field K] (σ : K →+* ℂ) (Pl : Rows.Places K) (w : Pl.Pl)
    (lam : ι → DomWeight n) (Z : ZBasis lam) (P : MvPolynomial (ι × Fin n × Fin n) ℂ) :
    P ∈ vlIntSpan σ Pl w lam ↔ ∃ c : Z.J0 → K, (∀ i, c i ∈ intW Pl w) ∧
      P = ∑ i, σ (c i) • MvPolynomial.map (Int.castRingHom ℂ) (Z.bZ i) := by
  constructor
  · intro hP
    induction hP using AddSubgroup.closure_induction with
    | mem P hP =>
      obtain ⟨r, f, hr, hf, rfl⟩ := hP
      have hx : Formalism.MainNotions.flipTwoThree.ten f ∈ Submodule.span ℤ (Set.range Z.bZ) := by
        rw [Z.span_eq]
        exact Submodule.subset_span ⟨f, hf, rfl⟩
      obtain ⟨z, hz⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hx
      refine ⟨fun i => r * (z i : K), fun i => mul_mem hr (intCast_mem _ _), ?_⟩
      set_option synthInstance.maxHeartbeats 100000 in
        rw [ten_int_map, ← hz, map_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_zsmul, map_mul, map_intCast, mul_smul, Int.cast_smul_eq_zsmul]
    | zero => exact ⟨0, fun _ => zero_mem _, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨c, hc, rfl⟩ := hx
      obtain ⟨c', hc', rfl⟩ := hy
      refine ⟨c + c', fun i => add_mem (hc i) (hc' i), ?_⟩
      simp [add_smul, Finset.sum_add_distrib]
    | neg x _ hx =>
      obtain ⟨c, hc, rfl⟩ := hx
      refine ⟨-c, fun i => neg_mem (hc i), ?_⟩
      simp [neg_smul, Finset.sum_neg_distrib]
  · rintro ⟨c, hc, rfl⟩
    have key : ∀ x ∈ Submodule.span ℤ {p | ∃ f : ι → MvPolynomial (Fin n × Fin n) ℤ,
        (∀ τ, f τ ∈ delSq ℤ n (lam τ)) ∧ p = Formalism.MainNotions.flipTwoThree.ten f}, ∀ r ∈ intW Pl w,
        σ r • MvPolynomial.map (Int.castRingHom ℂ) x ∈ vlIntSpan σ Pl w lam := by
      intro x hx r hr
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨f, hf, rfl⟩ := hx
        refine AddSubgroup.subset_closure ⟨r, f, hr, hf, ?_⟩
        rw [ten_int_map]
      | zero =>
        rw [map_zero, smul_zero]
        exact zero_mem _
      | add x y _ _ hx hy =>
        rw [map_add (f := _), smul_add]
        exact add_mem hx hy
      | smul a x _ hx =>
        rw [map_zsmul, smul_comm]
        exact zsmul_mem hx a
    refine sum_mem fun i _ => key _ ?_ _ (hc i)
    rw [← Z.span_eq]
    exact Submodule.subset_span ⟨i, rfl⟩

theorem mem_delW_iff {p : ℕ} [Fact p.Prime] (lam : ι → DomWeight n) (Z : ZBasis lam)
    (F : (ι → Matrix (Fin n) (Fin n) ℂ_[p]) → ℂ_[p]) :
    F ∈ WeylLatticeDuality.DelW p ι n (fun τ => (lam τ).natW) ↔ ∃ d : Z.J0 → ℂ_[p], (∀ i, ‖d i‖ ≤ 1) ∧
      F = fun y => ∑ i, d i * evM (MvPolynomial.map (Int.castRingHom ℂ_[p]) (Z.bZ i)) y := by
  constructor
  · intro hF
    induction hF using AddSubgroup.closure_induction with
    | mem F hF =>
      obtain ⟨r, f, hr, hf, rfl⟩ := hF
      have hx : Formalism.MainNotions.flipTwoThree.ten f ∈ Submodule.span ℤ (Set.range Z.bZ) := by
        rw [Z.span_eq]
        exact Submodule.subset_span ⟨f, fun τ => hf τ, rfl⟩
      obtain ⟨z, hz⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hx
      refine ⟨fun i => r * (z i : ℂ_[p]), fun i => ?_, ?_⟩
      · rw [norm_mul]
        exact mul_le_one₀ hr (norm_nonneg _) (IsUltrametricDist.norm_intCast_le_one _ _)
      · funext y
        rw [prod_eval_eq_evM, ← hz]
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [evM, map_sum, map_zsmul, zsmul_eq_mul, map_mul, map_intCast, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
    | zero => exact ⟨0, fun _ => by simp, by funext y; simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨d, hd, rfl⟩ := hx
      obtain ⟨d', hd', rfl⟩ := hy
      refine ⟨d + d', fun i => (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hd i) (hd' i)), ?_⟩
      funext v
      simp [add_mul, Finset.sum_add_distrib]
    | neg x _ hx =>
      obtain ⟨d, hd, rfl⟩ := hx
      refine ⟨-d, fun i => by rw [Pi.neg_apply, norm_neg]; exact hd i, ?_⟩
      funext v
      simp [neg_mul, Finset.sum_neg_distrib]
  · rintro ⟨d, hd, rfl⟩
    have key : ∀ x ∈ Submodule.span ℤ {p | ∃ f : ι → MvPolynomial (Fin n × Fin n) ℤ,
        (∀ τ, f τ ∈ delSq ℤ n (lam τ)) ∧ p = Formalism.MainNotions.flipTwoThree.ten f}, ∀ a : ℂ_[p], ‖a‖ ≤ 1 →
        (fun y => a * evM (MvPolynomial.map (Int.castRingHom ℂ_[p]) x) y) ∈
          WeylLatticeDuality.DelW p ι n (fun τ => (lam τ).natW) := by
      intro x hx a ha
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨f, hf, rfl⟩ := hx
        refine AddSubgroup.subset_closure ⟨a, f, ha, fun τ => hf τ, ?_⟩
        funext y
        rw [prod_eval_eq_evM]
      | zero =>
        have e : (fun y : ι → Matrix (Fin n) (Fin n) ℂ_[p] =>
            a * evM (MvPolynomial.map (Int.castRingHom ℂ_[p]) 0) y) = 0 := by
          funext y
          simp [evM]
        rw [e]
        exact zero_mem _
      | add x y _ _ hx hy =>
        have e : (fun v : ι → Matrix (Fin n) (Fin n) ℂ_[p] =>
            a * evM (MvPolynomial.map (Int.castRingHom ℂ_[p]) (x + y)) v) =
            (fun v => a * evM (MvPolynomial.map (Int.castRingHom ℂ_[p]) x) v) +
              (fun v => a * evM (MvPolynomial.map (Int.castRingHom ℂ_[p]) y) v) := by
          funext v
          simp [evM, mul_add]
        rw [e]
        exact add_mem hx hy
      | smul z x _ hx =>
        have e : (fun v : ι → Matrix (Fin n) (Fin n) ℂ_[p] =>
            a * evM (MvPolynomial.map (Int.castRingHom ℂ_[p]) (z • x)) v) =
            z • (fun v => a * evM (MvPolynomial.map (Int.castRingHom ℂ_[p]) x) v) := by
          funext v
          simp only [evM, map_zsmul, zsmul_eq_mul, map_mul, map_intCast, Pi.smul_apply, smul_eq_mul]
          ring
        rw [e]
        exact zsmul_mem hx z
    have e : (fun y => ∑ i, d i * evM (MvPolynomial.map (Int.castRingHom ℂ_[p]) (Z.bZ i)) y) =
        ∑ i, (fun y => d i * evM (MvPolynomial.map (Int.castRingHom ℂ_[p]) (Z.bZ i)) y) := by
      funext y
      simp [Finset.sum_apply]
    rw [e]
    refine sum_mem fun i _ => key _ ?_ _ (hd i)
    rw [← Z.span_eq]
    exact Submodule.subset_span ⟨i, rfl⟩

theorem map_mem_vlIntSpan_iff_delW : ∀ {K ι : Type} [Field K] [NumberField K] [Fintype ι] (σ : K →+* ℂ) (Pl : Rows.Places K) (w : Pl.Pl) {p : ℕ} [Fact p.Prime] (φ : K →+* ℂ_[p]), (∀ x, x ∈ intW Pl w ↔ ‖φ x‖ ≤ 1) → ∀ {n : ℕ} (lam : ι → DomWeight n) (G : MvPolynomial (ι × Fin n × Fin n) K), G ∈ Formalism.L2.DIV.VV K lam → (MvPolynomial.map σ G ∈ vlIntSpan σ Pl w lam ↔ (fun y : ι → Matrix (Fin n) (Fin n) ℂ_[p] => MvPolynomial.eval (fun k : ι × Fin n × Fin n => y k.1 k.2.1 k.2.2) (MvPolynomial.map φ G)) ∈ WeylLatticeDuality.DelW p ι n (fun τ => (lam τ).natW)) := by
  classical
  intro K ι _ _ _ σ Pl w p _ φ hφ n lam G hG
  choose r e hr using fun τ => exists_weylBasis n (lam τ).natW (natW_anti (lam τ))
  set Z := zOf lam e with hZ
  have hG' : G ∈ Submodule.span K (Set.range fun i => MvPolynomial.map (Int.castRingHom K) (Z.bZ i)) := by
    rw [Z.span_F K]
    exact hG
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hG'
  have hmap : ∀ (L : Type) [Field L] (s : K →+* L), MvPolynomial.map s G =
      ∑ i, s (c i) • MvPolynomial.map (Int.castRingHom L) (Z.bZ i) := by
    intro L _ s
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hc, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, MvPolynomial.map_map, ← MvPolynomial.smul_eq_C_mul]
    have h : s.comp (Int.castRingHom K) = Int.castRingHom L := RingHom.ext_int _ _
    rw [h]
  show _ ↔ evM (MvPolynomial.map φ G) ∈ _
  rw [mem_vlIntSpan_iff σ Pl w lam Z, mem_delW_iff lam Z]
  constructor
  · rintro ⟨c', hc', he⟩
    have hcc : c = c' := by
      rw [hmap ℂ σ] at he
      have h0 : ∑ i, (σ (c i) - σ (c' i)) • MvPolynomial.map (Int.castRingHom ℂ) (Z.bZ i) = 0 := by
        simp only [sub_smul, Finset.sum_sub_distrib, he, sub_self]
      funext i
      exact σ.injective (sub_eq_zero.1 (Fintype.linearIndependent_iff.1 (Z.li ℂ) _ h0 i))
    subst hcc
    refine ⟨fun i => φ (c i), fun i => (hφ _).1 (hc' i), ?_⟩
    funext y
    rw [hmap ℂ_[p] φ]
    simp [evM, MvPolynomial.smul_eval]
  · rintro ⟨d, hd, he⟩
    have hpoly : MvPolynomial.map φ G = ∑ i, d i • MvPolynomial.map (Int.castRingHom ℂ_[p]) (Z.bZ i) := by
      apply MvPolynomial.funext
      intro x
      have h1 := congrFun he (fun τ a b => x (τ, a, b))
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      simp only [MvPolynomial.smul_eval]
      exact h1
    rw [hmap ℂ_[p] φ] at hpoly
    have hcd : ∀ i, φ (c i) = d i := by
      have h0 : ∑ i, (φ (c i) - d i) • MvPolynomial.map (Int.castRingHom ℂ_[p]) (Z.bZ i) = 0 := by
        simp only [sub_smul, Finset.sum_sub_distrib, hpoly, sub_self]
      exact fun i => sub_eq_zero.1 (Fintype.linearIndependent_iff.1 (Z.li ℂ_[p]) _ h0 i)
    exact ⟨c, fun i => (hφ _).2 ((hcd i).symm ▸ hd i), hmap ℂ σ⟩

end GlobalTheory.Mem.IntSpanDelW
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowFiniteTypePartsSpanAndOrthogonal
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw

noncomputable section

namespace GlobalTheory.Mem.R3.Rw.TypesRows

theorem parts_span_orth : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), Inputs D → Pins R F cG → Holds R F → ∀ (y : Hd R.toRealDat) (Φ : Type) (rep : Φ → Formalism.L2.NG.FinTyp D.host.E D.R.r), Reps y F.lv2 rep → ∀ b : Bool, (⨆ π, y.prtE F.lv2 b (rep π)) = (y.C F.lv2).EEc b ∧ ∀ π π', π ≠ π' → ∀ x ∈ y.prtE F.lv2 b (rep π), ∀ x' ∈ y.prtE F.lv2 b (rep π'), (y.C F.lv2).ipE b x x' = 0 := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG hI hP hH y Φ rep hR b
  have hB := hP.char.base
  have h0 := hB.models.ν0
  have hs := GlobalTheory.HilbertLevels.scaled (inv_pos.2 (GlobalTheory.HilbertLevels.nP_pos F.lv2 b)) h0.1.1 h0.2
  obtain ⟨s, c, hsG, he⟩ : ∃ (s : Finset (GA D (Yc D 0))) (c : GA D (Yc D 0) → ℂ), (∀ g ∈ s, g ∈ GfC (Yc D 0)) ∧
      R.e0 = ∑ g ∈ s, c g • principalLevelFrame.rtA g :=
    GlobalTheory.Mem.R3.IsotIndep.gaL_finSum (Yc D 0) (R.βY 0) (R.dat0 R.triv) R.eG _
  have key := GlobalTheory.FinTypesRows.isotL_span_orth D (Yc D 0) _ R.θ (R.MY 0) y.PY y.hF (R.βY 0) (R.dat0 (R.levR F.lv2 b)) R.e0
    (ENNReal.ofReal (RealDat.nP F.lv2 b)⁻¹ • R.ν0) R.fd0 hI (D.sp.Y_sig _) hB.models.inf y.stdPsi.1 hs.1 hs.2 ⟨s, c, hsG, he⟩

  set J := levS _ (R.βY 0) (R.dat0 (R.levR F.lv2 b)) with hJ
  set χ := levChi _ (R.βY 0) (R.dat0 (R.levR F.lv2 b)) with hχ

  have hcc : ∀ ρ : Formalism.L2.NG.FinTyp D.host.E D.R.r, (principalLevelFrame.FinTyp.conjT (principalLevelFrame.FinTyp.conjT ρ)).Iso ρ := by
    intro ρ
    unfold Formalism.L2.NG.FinTyp.Iso
    rw [principalLevelFrame.conjT_S, principalLevelFrame.conjT_S, principalLevelFrame.conjSub_conjSub]
    exact Formalism.L2.NG.IsoRep.refl _
  have hspan : (⨆ π, principalLevelFrame.isotE R.θ y.PY (R.MY 0) J χ R.e0 (rep π)) = Mult.goodPart R.θ (R.MY 0) J χ R.e0 := by
    refine le_antisymm (iSup_le fun π => inf_le_left) ?_
    rw [← key.1]
    refine iSup_le fun ρ => ?_
    by_cases h0 : principalLevelFrame.isotL R.θ y.PY (R.MY 0) J χ R.e0 ρ = ⊥
    · rw [h0]
      exact bot_le
    · have he1 : principalLevelFrame.isotE R.θ y.PY (R.MY 0) J χ R.e0 (principalLevelFrame.FinTyp.conjT ρ) = principalLevelFrame.isotL R.θ y.PY (R.MY 0) J χ R.e0 ρ :=
        principalLevelFrame.isotL_iso R.θ y.PY (R.MY 0) J χ R.e0 (hcc ρ)
      have hocc : principalLevelFrame.FinTyp.conjT ρ ∈ y.occ F.lv2 := ⟨b, by rw [he1]; exact h0⟩
      obtain ⟨π, hπ⟩ := hR.all _ hocc
      have he2 : principalLevelFrame.isotE R.θ y.PY (R.MY 0) J χ R.e0 (rep π) = principalLevelFrame.isotL R.θ y.PY (R.MY 0) J χ R.e0 ρ := by
        rw [← he1]
        exact principalLevelFrame.isotL_iso R.θ y.PY (R.MY 0) J χ R.e0 (principalLevelFrame.conjT_iso hπ)
      exact le_iSup_of_le π (le_of_eq he2.symm)
  refine ⟨?_, ?_⟩
  · unfold Hd.prtE
    show (⨆ π, (principalLevelFrame.isotE R.θ y.PY (R.MY 0) J χ R.e0 (rep π)).map
        (PiTensorProduct.lift : Mult.MMap (R.MY 0) ≃ₗ[ℂ] _).toLinearMap) =
      (Mult.goodPart R.θ (R.MY 0) J χ R.e0).map (PiTensorProduct.lift : Mult.MMap (R.MY 0) ≃ₗ[ℂ] _).toLinearMap
    rw [← hspan, Submodule.map_iSup]
  · intro π π' hne x hx x' hx'
    obtain ⟨u, hu, rfl⟩ := hx
    obtain ⟨u', hu', rfl⟩ := hx'
    have hni : ¬ (principalLevelFrame.FinTyp.conjT (rep π)).Iso (principalLevelFrame.FinTyp.conjT (rep π')) :=
      principalLevelFrame.not_iso_conjT fun h => hne (hR.inj π π' h)
    have := key.2 _ _ hni u hu u' hu'
    show ipMT (R.MY 0) (ENNReal.ofReal (RealDat.nP F.lv2 b)⁻¹ • R.ν0) R.fd0 _ _ = 0
    unfold ipMT
    convert this using 2 <;> exact LinearEquiv.symm_apply_apply _ _

end GlobalTheory.Mem.R3.Rw.TypesRows
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SectionPolynomialEqOfFunctionEqCoefficient
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.PolyId

theorem shiftOf_lamT_succ {R : Ranks} {ι : Type} [Fintype ι] {hc : ι → HCParam R} (C : ColumnChain R ι hc) (i : ℕ)
    (hi : i < R.m) (τ : ι) : shiftOf (Col2.lamT hc (i + 1)) τ = -C.sDiv i τ := by
  have hN : R.N (i + 1) = R.k + (i + 1) * (R.t + 1) := rfl
  have h1 : 1 ≤ (i + 1) * (R.t + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hpos : 0 < R.N (i + 1) := by rw [hN]; omega
  have hk : ¬ (R.N (i + 1) - 1 < R.k) := by rw [hN]; omega
  have hq : (R.N (i + 1) - 1 - R.k) / (R.t + 1) = i := by
    rw [hN]
    have hm : (i + 1) * (R.t + 1) = i * (R.t + 1) + R.t + 1 := by ring
    rw [hm, show R.k + (i * (R.t + 1) + R.t + 1) - 1 - R.k = R.t + i * (R.t + 1) by omega,
      Nat.add_mul_div_right _ _ (Nat.succ_pos _), Nat.div_eq_of_lt (Nat.lt_succ_self _), zero_add]
  have h2 := C.sDiv_eq i hi τ
  obtain ⟨c, hc'⟩ := R.t_odd
  have hcq : (R.t : ℚ) = 2 * c + 1 := by exact_mod_cast hc'
  have e2 : (R.t + 1) / 2 = c + 1 := by omega
  simp only [shiftOf, DomWeight.detShift, dif_pos hpos, Col2.lamT, Col2.shW, Examples₂.lamOf, dif_pos (show i + 1 ≤ R.m by omega), Examples₂.wtQ, dif_neg hk]
  simp only [hq, e2]
  have hw : -wG R ((hc τ).e ⟨i, hi⟩) (i + 1) = ((-C.sDiv i τ + ((i + 1) * (c + 1) : ℕ) : ℤ) : ℚ) := by
    push_cast
    rw [h2]
    simp only [wG, sExp, Ranks.N, Nat.add_sub_cancel]
    push_cast
    rw [hcq]
    ring
  rw [hw, Int.floor_intCast]
  push_cast
  ring

theorem secC_eq_of_evC_eq_evV : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (Qp : I.ι → Finset ℕ) (O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)), I.StdO l Z Qp O → ∀ (u : B.Word) (μ : I.ι) (i : ℕ), i < (I.rec7 l Z).R.m → ∀ (z : VV B.LL (lamT (B.hcW u) (i + 1))) (v' : ValQ O u μ (i + 1)), evC O u μ (i + 1) v' = evV B.fields.emb (1 : Matrix (Fin (B.R.N (i + 1))) (Fin (B.R.N (i + 1))) B.fields.E) (lamT (B.hcW u) (i + 1)) B.embLL z → ((secC O u μ (i + 1) v' : MvPolynomial (GL3Theta.FrV (I.rec7 l Z) ((I.rec7 l Z).R.N (i + 1))) (I.rec7 l Z).what₂.LL)) = (show MvPolynomial (GL3Theta.FrV (I.rec7 l Z) ((I.rec7 l Z).R.N (i + 1))) (I.rec7 l Z).what₂.LL from z.1) := by
  intro B X I hOk hP l Z Qp O hStd u μ i hi z v' h
  have hfun : fnOf (gramC (1 : Matrix (Fin (B.R.N (i + 1))) (Fin (B.R.N (i + 1))) B.fields.E) (embAt B.embLL B.fields.emb))
      (shiftOf (Col2.lamT (B.hcW u) (i + 1))) 1
      (MvPolynomial.map B.embLL ((secC O u μ (i + 1) v' : MvPolynomial (GL3Theta.FrV (I.rec7 l Z) ((I.rec7 l Z).R.N (i + 1))) (I.rec7 l Z).what₂.LL))) =
      fnOf (gramC (1 : Matrix (Fin (B.R.N (i + 1))) (Fin (B.R.N (i + 1))) B.fields.E) (embAt B.embLL B.fields.emb))
      (shiftOf (Col2.lamT (B.hcW u) (i + 1))) 1 (MvPolynomial.map B.embLL z.1) := by
    rw [← evV_apply]
    rw [← h]
    refine Eq.trans ?_ (evC_sec O u μ (i + 1) v').symm
    funext y
    have hfr := hStd.frm u μ (i + 1) y
    show _ = (∏ τ, (((I.rec7 l Z).chTw u μ).de (i + 1) y τ) ^ (-(((I.rec7 l Z).chTw u μ).sDiv i τ))) *
      GL3Theta.evFr (I.rec7 l Z) (MvPolynomial.map (I.rec7 l Z).what₂.embLL ((secC O u μ (i + 1) v' : MvPolynomial (GL3Theta.FrV (I.rec7 l Z) ((I.rec7 l Z).R.N (i + 1))) (I.rec7 l Z).what₂.LL))) ((O u μ).frm (i + 1) y)
    rw [hfr]
    simp only [fnOf, LinearMap.coe_mk, AddHom.coe_mk, GL3Theta.evFr]
    congr 1
    · refine Finset.prod_congr rfl fun τ _ => ?_
      have hs : shiftOf (Col2.lamT (B.hcW u) (i + 1)) τ = -((I.rec7 l Z).chTw u μ).sDiv i τ :=
        shiftOf_lamT_succ ((I.rec7 l Z).chTw u μ) i hi τ
      rw [hs, Pi.one_apply, Matrix.one_mul]
      rfl
    · simp only [Pi.one_apply, Matrix.one_mul]
      rfl
  have h2 := fnOf_injective _ _ 1 (fun _ => by simp) (stdFrC (n := B.R.N (i + 1)) (embAt B.embLL B.fields.emb)) hfun
  exact MvPolynomial.map_injective _ B.embLL.injective h2

end GlobalTheory.Mem.Col2.PolyId
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SupportDegreeEqOfMemWeightPolynomials
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.WtHomog

open MvPolynomial

theorem coeff_aeval_diag {K : Type} [Field K] {σ : Type} (c : σ → K) (Q : MvPolynomial σ K)
    (e : σ →₀ ℕ) :
    AddMonoidAlgebra.coeff (aeval (fun v => C (c v) * X v) Q : MvPolynomial σ K) e
      = (e.prod fun v k => c v ^ k) * AddMonoidAlgebra.coeff Q e := by
  classical
  induction Q using MvPolynomial.induction_on' generalizing e with
  | monomial u a =>
    have h : (aeval (fun v => C (c v) * X v) (monomial u a) : MvPolynomial σ K)
        = monomial u ((u.prod fun v k => c v ^ k) * a) := by
      rw [aeval_monomial]
      simp only [mul_pow, Finsupp.prod_mul, ← map_pow]
      rw [show (u.prod fun v k => (C (c v ^ k) : MvPolynomial σ K))
            = C (u.prod fun v k => c v ^ k) from (map_finsuppProd C _ _).symm]
      rw [show (u.prod fun v k => (X v : MvPolynomial σ K) ^ k) = monomial u 1 from
        (monomial_eq (s := u) (a := (1 : K))).symm ▸ by simp]
      rw [algebraMap_eq, ← mul_assoc, ← C_mul, C_mul_monomial]
      simp [mul_comm]
    rw [h, coeff_monomial, coeff_monomial]
    by_cases hue : u = e
    · subst hue; simp
    · simp [hue]
  | add p q hp hq =>
    rw [map_add (f := _), MvPolynomial.coeff_add, MvPolynomial.coeff_add, hp, hq, mul_add]

theorem deg_eq_of_mem_wtPol : ∀ {K : Type} [Field K] [CharZero K] {ι : Type} [Fintype ι] {n : ℕ} (ν : ι → Fin n → ℕ)
    (Q : MvPolynomial (ι × Fin n × Fin n) K) (hQ : Q ∈ WtPol K ν), ∀ e ∈ Q.support, ∀ τ, ∑ α, ∑ s, e (τ, α, s) = ∑ r, ν τ r := by
  intro K _ _ ι _ n ν Q hQ e he τ
  classical
  set c : ι → K := fun σ => if σ = τ then 2 else 1 with hc
  set β : ι → Matrix (Fin n) (Fin n) K := fun σ => c σ • (1 : Matrix (Fin n) (Fin n) K) with hβ
  have hc0 : ∀ σ, c σ ≠ 0 := by
    intro σ; simp only [hc]; split_ifs <;> norm_num
  have hbor : IsBor β := by
    intro σ
    refine ⟨fun r s hsr => ?_, fun r => ?_⟩
    · simp [hβ, Matrix.one_apply, (ne_of_lt hsr).symm]
    · simpa [hβ] using hc0 σ
  have hsub : colSub β = aeval (fun v : ι × Fin n × Fin n => C (c v.1) * X v) := by
    unfold colSub
    congr 1
    funext v
    obtain ⟨σ, α, s⟩ := v
    simp only [hβ, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_eq_single s]
    · simp
    · intro b _ hb; simp [hb]
    · simp
  have hw := hQ β hbor
  rw [hsub] at hw
  have hcoef := congrArg (AddMonoidAlgebra.coeff · e) hw
  rw [coeff_aeval_diag, coeff_smul] at hcoef
  have hne : AddMonoidAlgebra.coeff Q e ≠ 0 := mem_support_iff.mp he
  have hL : (e.prod fun v k => c v.1 ^ k) = (2 : K) ^ (∑ α, ∑ s, e (τ, α, s)) := by
    rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fintype.prod_prod_type,
      Finset.prod_eq_single τ]
    · rw [Fintype.prod_prod_type]
      simp only [hc, if_true, Finset.prod_pow_eq_pow_sum]
    · intro σ _ hσ
      simp [hc, hσ]
    · simp
  have hR : (∏ σ, ∏ r, β σ r r ^ ν σ r) = (2 : K) ^ (∑ r, ν τ r) := by
    rw [Finset.prod_eq_single τ]
    · simp [hβ, hc, Finset.prod_pow_eq_pow_sum]
    · intro σ _ hσ
      simp [hβ, hc, hσ]
    · simp
  rw [hL, hR, smul_eq_mul] at hcoef
  have heq := mul_right_cancel₀ hne hcoef
  have h2 : ((2 : ℕ) ^ (∑ α, ∑ s, e (τ, α, s))) = (2 : ℕ) ^ (∑ r, ν τ r) := by
    exact_mod_cast heq
  exact Nat.pow_right_injective (le_refl 2) h2

end GlobalTheory.Mem.WtHomog
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistLocalConditionConjIffFrameChangeTrivialStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TC.ChTw GlobalTheory.Mem.Col2.TC.ChTw.Match Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistLocalCondition_conj_iff_frameChange_trivial : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (u : B.Word) (a : I.ι)
    (Q : Finset (HeightOneSpectrum (𝓞 B.host.F))), (∀ v, v ∈ Q ↔ I.UnderQ a v) → ∀ (n : ℕ) (t s : GA B n) (θ : GLQ B.fields.E n (I.Q a)),
    (∀ v : HeightOneSpectrum (𝓞 B.host.F), ((B.T u : 𝓞 B.host.F) ∈ v.asIdeal ∨ ∀ j, (B.host.g j : 𝓞 B.host.F) ∉ v.asIdeal) →
      bc (prV (E := B.host.E) v) t = 1) →
    (∀ v ∈ Q, bc (prV (E := B.host.E) v) s = 1) →
    (LocCQ (I.Q a) n (t⁻¹ * s * t) θ ↔ θ = 1) := by
  first | exact @GlobalTheory.Mem.Col2.TC.ChTw.Match.locCQ_conj_iff_eq_one | exact GlobalTheory.Mem.Col2.TC.ChTw.Match.locCQ_conj_iff_eq_one | (intros; apply GlobalTheory.Mem.Col2.TC.ChTw.Match.locCQ_conj_iff_eq_one <;> assumption)
end

