module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
public import Formalism.LocalToGlobal.Divisibility.NumbersLemmas
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.DepthCond
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0313
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0305
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemRangeSrcForm
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0309
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0475
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0137
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0115
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1246
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1665
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1531
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1502
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallySelfDualLatticeIndicatorIsVacuum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1566
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1667
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1580
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1586
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1613
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualLocalSubgroupFirstProjEqAnnihilator
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0143
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1671

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodLiftOntoOfBase
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Module
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links
open Formalism.IndefR.Cx Formalism.IndefR.FWT Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.FormTies GlobalTheory.BigOn
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TraceIncl

namespace GlobalTheory.BaseTwistIncl

section Rank

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A)

theorem ws_le_base (hX : ∀ χ ∈ A.X, IsAbsIrrChar χ) (h5 : (R.toCx F).H5 F.cr false) (i : Fin D.R.m) (t : T0)
    (N : Submodule ℂ (R.HW i (sg0 D A)).H) (hN : ∀ x, R.thG i t (jVx R i t (OnTies.srcForm A i t F.P0 F.ψ0⁻¹ x)) ∈ N) :
    R.WS F false i (sg0 D A) ≤ N := by
  intro w h1
  obtain ⟨c, hc⟩ := exists_w0C_eq R F i h1
  have h0 : ∀ y, (R.toCx F).θ' i t ((R.toCx F).jL i t (F.cr.toL (R.toCx F).zs false i t y)) ∈
      Tw.sub (twAt D.what₂.embLL A.v0) N := by
    intro y
    obtain ⟨x, hx⟩ := exists_srcForm_eq F hX i t ((R.toCx F).zs.Zl i t) y
    have k5 : ∀ u u' : A.fam.amb.FL i t, u = u' → R.thG i t (jVx R i t u) ∈ N → R.thG i t (jVx R i t u') ∈ N :=
      fun u u' h hu => h ▸ hu
    have k4 := k5 _ _ hx (hN x)
    have k3 := out_lift_toL R F i t y
    exact (congrArg (fun u : (R.HW i (sg0 D A)).H => u ∈ N) k3).mpr k4
  have h2 := goodFormsCoordinateMap_mem_of_lifts_mem (R.toCx F) F.cr false h5 i t _ h0 c
  exact (congrArg (· ∈ N) hc).mp h2

theorem goodLiftOnto_of_base (hX : ∀ χ ∈ A.X, IsAbsIrrChar χ) (hW : R.models_HW) (hG : R.thP_thG) (hU : R.LUnif)
    (h5 : (R.toCx F).H5 F.cr false) (i : Fin D.R.m) (t : T0) (ph : ℂ) (hph : ph ≠ 0) :
    GoodLiftOnto R i t F.P0 F.ψ0⁻¹ ph := by
  intro θ hθ z hz
  refine mem_of_mem_span_image ((R.FW i).j (sg0 D A)) (hU i _).1 _ ?_
  have h1 : (R.FW i).j (sg0 D A) z ∈
      Submodule.span ℂ (Set.range fun x => R.thG i t (jVx R i t (OnTies.srcForm A i t F.P0 F.ψ0⁻¹ x))) := by
    refine ws_le_base R F hX h5 i t _ (fun x => Submodule.subset_span (Set.mem_range_self x)) ?_
    rw [GlobalTheory.LevelForms.ws_eq_span]
    exact Submodule.subset_span ⟨z, hz, rfl⟩
  refine Submodule.span_le.2 ?_ h1
  rintro _ ⟨x, rfl⟩
  refine (Submodule.smul_mem_iff _ hph).1 ?_
  exact Submodule.subset_span ⟨_, ⟨x, rfl⟩, j_eOp_of_adForm R hW hG hU i t ph _ _ (hθ x)⟩

end Rank

attribute [local instance] GlobalTheory.BigOn.runAlg'

theorem leafTW2_of_isRec : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (J : CoreJ D) [Algebra J.Q.c.F D.what₂.LL] (R : RealDat D A J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie J R κ v₀) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (EX : ErrX D) (r : TwoRuns J G) (c : OnConst) (O : OnObj ((R.toCx F).data F.cr false) (Mir R) c), IsRec Tp hK EX F fw r O → ∀ s : ℕ, A.fam.Ok s → R.Char F → R.LUnif → BaseLinks R F → TwistedRational R F (fun _ => 1) → LeafTW2 O := by
  intro D G _ _ Pl0 T0 A J inst R F κ v₀ fw L Pm Tp hK EX r c O hrec s hOk hC hU hB hrat
  obtain ⟨hc, hinj, z, act, y, ht⟩ := hrec.tied
  have hinc : F.P0 ≤ (mirIncl R).range := fun g hg => by
    obtain ⟨u, -, e⟩ := (mem_base_iff hC.grp.levels g).1 hg
    exact ⟨u, e⟩
  have main : ∀ v, (∀ j, ClassSumRational R j (R.mu v) F.P0 F.ψ0⁻¹ 1) →
      ∀ j, IsLatIn (O.Zg j) (O.X₃ v j) ∧ IsLatIn (O.Zg j) (O.Im v j) ∧
        Formalism.HermitianLatticesTheory.localization₂ v.asIdeal (O.X₃ v j) ≤ Formalism.HermitianLatticesTheory.localization₂ v.asIdeal (O.Im v j) := by
    intro v h3 j
    have := lattices_of_tie (T := (r.used v).full) (inst := inst) (R := R)
      (ht v j).1 (ht v j).2 hinc (chi_eq_one_of_mem_base R F hC.grp j)
      ⟨hC.lev, hC.grp.red_L, hC.fam.tie, hC.models, hC.thP, hU, ⟨_, (fw.hv₀ j _).1⟩, (hOk.lifts _ _).act,
        _root_.GlobalTheory.VecInv.omega_lifts_vP R hC.lev hC.models.inf hC.thP.ωP hC.thP.vP j (R.mu v)⟩
      (hOk.lifts _ _).good hOk.irr (h3 j)
      (goodLiftOnto_of_base R F hOk.irr hC.models.HW hC.thP.thG hU hB.1 _ _ _ one_ne_zero)
    exact ⟨this.1, this.2.1, Formalism.L2.DIV.localization_mono _ this.2.2⟩
  intro w hw
  exact ⟨main w (hrat w hw), main _ (by rw [hC.tup.mu_conj w]; exact hrat w hw)⟩

end GlobalTheory.BaseTwistIncl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasIndexBoundOfRuns
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Module
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links
open Formalism.IndefR.Cx Formalism.IndefR.FWT Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.FormTies GlobalTheory.BigOn
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

namespace GlobalTheory.BigOn

theorem isLattice_of_spanK {F K : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K] {C : Type}
    [AddCommGroup C] [Module F C] [Module (𝓞 F) C] [IsScalarTower (𝓞 F) F C] {n : ℕ}
    (z : (Fin n → K) ≃ₗ[K] K ⊗[F] C) (M : Submodule (𝓞 F) C) (h : IsLatIn ⊤ (spanK z (M : Set C))) :
    Submodule.IsFullLattice F M := by
  have hinj : Function.Injective (coordMap z) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    have h1 : z.symm ((1 : K) ⊗ₜ[F] x) = 0 := hx
    rw [LinearEquiv.map_eq_zero_iff] at h1
    exact (Module.FaithfullyFlat.one_tmul_eq_zero_iff F C x).1 h1
  have hfg : M.FG := by
    have h1 : ((spanK z (M : Set C)).restrictScalars (𝓞 F)).FG := h.1.restrictScalars
    have h2 : M.map ((coordMap z).restrictScalars (𝓞 F)) ≤ (spanK z (M : Set C)).restrictScalars (𝓞 F) := by
      rintro _ ⟨x, hx, rfl⟩
      exact mem_spanK z hx
    exact Submodule.fg_of_fg_map_injective ((coordMap z).restrictScalars (𝓞 F)) hinj (h1.of_le h2)
  letI := Submodule.IsLattice.of_fg F hfg
  refine ⟨?_⟩
  · refine Submodule.baseChange_injective (A := K) ?_
    rw [Submodule.baseChange_top, Submodule.baseChange_span, eq_top_iff]
    intro y _
    have h2 := h.2
    unfold spanK at h2
    rw [Submodule.span_span_of_tower] at h2
    have h3 : z.symm y ∈ Submodule.span K ((fun f : C => z.symm (1 ⊗ₜ[F] f)) '' (M : Set C)) := h2 ▸ Submodule.mem_top
    have h4 := Submodule.mem_map_of_mem (f := z.toLinearMap) h3
    rw [Submodule.map_span, ← Set.image_comp] at h4
    simp only [Function.comp_def, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at h4
    exact h4

theorem exists_rem_of_concl {D : D7} {B : WeightFamilies.Prov D} {P6 : ModuliIntegralCharts.Prov D} {j : ℕ} (X : WeightAlgebra.PJ D B P6 j) (S : WeightAlgebra.Scal B)
    (ka wL wF : WeightFamilies.Wt D j) (T : ℕ) (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ) (a b c d : ℝ)
    {K : Type} [Field K] [NumberField K] [StarRing K] [Algebra B.KO K] {n : ℕ}
    (z : (Fin n → K) ≃ₗ[K] K ⊗[B.KO] B.Cusp j ka) (hM : IsLatIn ⊤ (spanK z (B.Mlat j ka : Set _)))
    (hC : WeightAlgebra.Concl X S ka wL wF T nus (X.rk ka (B.Mlat j ka) * a * b * c * d)) :
    ∃ r : HeightOneSpectrum (𝓞 K) → ℝ, (∀ v, 0 ≤ r v) ∧
      (∀ S' : Finset (HeightOneSpectrum (𝓞 K)), ∑ v ∈ S', Formalism.DivisionValues.lw v * r v ≤ (n : ℝ) * (a * b * c * d)) ∧
      ∀ (v : HeightOneSpectrum (𝓞 K)) (e : ℕ), (T : ℝ) * nus (placeBelow (K := B.KO) v) ≤ e →
        ∀ W : Submodule K (Fin n → K),
          (lix v (cut W (spanK z (B.Mlat j ka : Set _))) (cut W (spanK z {F | X.inc ka F ∈ X.Theta S ka wL wF T})) : ℝ) ≤
            ((ramOver (K := B.KO) v * e : ℕ) : ℝ) * (Module.finrank K W : ℝ) + r v := by
  have hM' := isLattice_of_spanK z _ hM
  letI := hM'
  have hn : X.rk ka (B.Mlat j ka) = n := by
    unfold WeightAlgebra.PJ.rk
    rw [Submodule.IsFullLattice.span_eq_top, finrank_top]
    have := z.finrank_eq
    rw [Module.finrank_baseChange, Module.finrank_fin_fun] at this
    exact this.symm
  let Q : Formalism.MainNotions.Gaps.LocalGlobalPassage.Run D B P6 := ⟨j, X, S, ka, wL, wF, T, nus, X.rk ka (B.Mlat j ka) * a * b * c * d⟩
  letI : Submodule.IsFullLattice B.KO Q.M0 := hM'
  obtain ⟨r, h0, h1, h2, h3⟩ := Formalism.MainNotions.Gaps.LocalGlobalPassage.l2 Q (fun la => Formalism.MainNotions.Gaps.LocalGlobalPassage.l1 la)
    (fun la => Formalism.MainNotions.Gaps.LocalGlobalPassage.l1b la) (fun la => Formalism.MainNotions.Gaps.LocalGlobalPassage.l1c la) (by first | exact hM' | exact hM'.toIsLattice) hC
  have hβ : Q.β = (n : ℝ) * (a * b * c * d) := by
    change (X.rk ka (B.Mlat j ka) : ℝ) * a * b * c * d = _
    rw [hn]
    ring
  refine ⟨fun v => (v.asIdeal.ramificationIdx (𝓞 B.KO) : ℝ) * r (v.under (𝓞 B.KO)),
    fun v => mul_nonneg (Nat.cast_nonneg _) (h0 _),
    fun S' => (Formalism.MainNotions.Gaps.LocalGlobalPassage.l4 r h0 h1 S').trans (h2.trans hβ.le), ?_⟩
  intro v e he W
  have hpl : placeBelow (K := B.KO) v = v.under (𝓞 B.KO) := rfl
  have hram : ramOver (K := B.KO) v = v.asIdeal.ramificationIdx (𝓞 B.KO) := Formalism.MainNotions.Gaps.LocalGlobalPassage.ram_eq v
  obtain ⟨h4, h5⟩ := h3 (v.under (𝓞 B.KO))
  have hTh : Formalism.MainNotions.Gaps.LocalGlobalPassage.up (coordMap z) (Q.M0 ⊓ Q.Th0) ≤ spanK z {F | X.inc ka F ∈ X.Theta S ka wL wF T} :=
    Submodule.span_mono (Set.image_mono fun f hf => hf.2)
  exact Formalism.MainNotions.Gaps.LocalGlobalPassage.l5 (coordMap z) (coordMap_linearIndependent z) (coordMap_span z) Q.M0 (Q.M0 ⊓ Q.Th0) (Submodule.IsLattice.fg B.KO (B.Mlat j ka))
    Submodule.IsFullLattice.span_eq_top h4 inf_le_left v e (r (v.under (𝓞 B.KO))) (ramOver (K := B.KO) v * e)
    (by rw [hram]; push_cast; rfl) (h5 e (by rw [Int.cast_natCast, ← hpl]; exact he)) _ hTh W

theorem starRing_eq {R : Type} [CommRing R] (s t : StarRing R) (h : ∀ a : R, s.star a = t.star a) : s = t := by
  obtain @⟨@⟨@⟨⟨f⟩, _⟩, _⟩, _⟩ := s
  obtain @⟨@⟨@⟨⟨g⟩, _⟩, _⟩, _⟩ := t
  obtain rfl : f = g := funext h
  rfl

theorem exists_rem_of_tie {D : D7} {B : WeightFamilies.Prov D} {P6 : ModuliIntegralCharts.Prov D} {j : ℕ} {X : WeightAlgebra.PJ D B P6 j}
    {hinj : Function.Injective D.what₂.OtoLL} {EX : ErrX D} {p : ℕ} {ka wL wF : WeightFamilies.Wt D j} {T : ℕ}
    {nus : HeightOneSpectrum (𝓞 B.KO) → ℝ} {a b c d : ℝ}
    {K : Type} [Field K] [NumberField K] [StarRing K] [Algebra B.KO K]
    {Bs : DefBase K} {Df : DefSide Bs} {S : IndefData Df} {P : Type} [Group P] [Finite P] {oc : OnConst}
    {O : OnObj S P oc} {v₁ : HeightOneSpectrum (𝓞 K)} {i : Bs.J}
    {z : (Fin (O.nZ i) → K) ≃ₗ[K] K ⊗[B.KO] B.Cusp j ka} {act : P → B.Cusp j ka → B.Cusp j ka}
    (ht : FormTieK X hinj EX p ka wL wF T O v₁ i z act) (hM : IsLatIn ⊤ (O.Ms i))
    (hC : WeightAlgebra.Concl X (scalOfP B hinj EX p ka wL wF T) ka wL wF T nus (X.rk ka (B.Mlat j ka) * a * b * c * d)) :
    ∃ r : HeightOneSpectrum (𝓞 K) → ℝ, (∀ v, 0 ≤ r v) ∧
      (∀ S' : Finset (HeightOneSpectrum (𝓞 K)), ∑ v ∈ S', Formalism.DivisionValues.lw v * r v ≤ (O.nZ i : ℝ) * (a * b * c * d)) ∧
      ∀ (v : HeightOneSpectrum (𝓞 K)), FormTieK X hinj EX p ka wL wF T O v i z act →
        ∀ e : ℕ, (T : ℝ) * nus (placeBelow (K := B.KO) v) ≤ e → ∀ W : Submodule K (Fin (O.nZ i) → K),
          (lix v (cut W (O.Ms i)) (cut W (O.Th v i)) : ℝ) ≤
            ((ramOver (K := B.KO) v * e : ℕ) : ℝ) * (Module.finrank K W : ℝ) + r v := by
  obtain ⟨ρ, h0, h1, h2⟩ := exists_rem_of_concl X _ ka wL wF T nus a b c d z (ht.Ms_eq ▸ hM) hC
  refine ⟨ρ, h0, h1, fun v hv e he W => ?_⟩
  rw [hv.Ms_eq, hv.Th_eq]
  exact h2 v e he W

theorem nusR_le_eLam {D : D7} {L : SizeData₂ D} {Pm : ParameterChoice' D L} (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (EX : ErrX D)
    (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (la : HeightOneSpectrum (𝓞 T.Q.c.F)) :
    letI := T.Q.H.starRing
    (Tp.TO : ℝ) * GlobalTheory.RunJoin.nusR h j (lR Tp hK j) la ≤
      ((GlobalTheory.RunDepth.depOf T.toCore EX Tp hK).Q.eLam (ramOverZ la)
        (nuStarAt (Xo := T.Q.Xo j) (c := T.Q.c) (GlobalTheory.RunDepth.depOf T.toCore EX Tp hK) la j) (resCharOf la) : ℝ) := by
  have hn := GlobalTheory.RunDepthScale.nusOf_eq_ram_mul_nuStarAt D L Pm Tp hK T h EX j hj la
  refine le_trans (le_of_eq ?_) (DepPage.le_eLam _ _ _ _)
  refine (congrArg (fun t => (Tp.TO : ℝ) * t) hn).trans ?_
  rw [← mul_assoc, mul_comm (Tp.TO : ℝ)]
  rfl


set_option maxHeartbeats 1000000 in
theorem hasIndexBound_of_runs : ∀ CK : ℝ, ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (J : CoreJ D) [Algebra J.Q.c.F D.what₂.LL] (R : RealDat D A J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie J R κ v₀) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (EX : ErrX D) (r : TwoRuns J G) (c : OnConst) (O : OnObj ((R.toCx F).data F.cr false) (Mir R) c), IsRec Tp hK EX F fw r O → CoreTies L EX J R → OwnPin r → RunsHold Tp hK EX CK r → LeafSup O → LeafSpan O → O.b = L.sc.b → HasIndexBound O := by
  intro CK D G _ _ Pl0 T0 A J inst R F κ v₀ fw L Pm Tp hK EX r c O hO _ _ hR hS hSp hb
  obtain rfl : κ = fun i : Fin D.R.m => kaR Tp hK ((i : ℕ) + 1) := funext hO.kap
  obtain ⟨hc, hinj, z, act, y, ht⟩ := hO.tied
  obtain ⟨st, hd⟩ := hO.depth
  let _ := hostAlg D
  obtain rfl : st = J.toCore.Q.H.starRing := starRing_eq _ _ hd.star_eq
  let _ := J.toCore.Q.H.starRing
  let _ : ∀ s : RunData J, Algebra s.full.J.Q.c.F D.what₂.LL := fun _ => inst
  let _ : ∀ (s : RunData J) (h : LawsP s.full.toTop), Algebra (recB h.toLawsCore).KO D.what₂.LL := fun _ _ => inst
  have key : ∀ (q : Prop) (i : Fin D.R.m), ∃ ρ : HeightOneSpectrum (𝓞 D.what₂.LL) → ℝ, (∀ v, 0 ≤ ρ v) ∧
      (∀ S' : Finset (HeightOneSpectrum (𝓞 D.what₂.LL)),
        ∑ v ∈ S', Formalism.DivisionValues.lw v * ρ v ≤ (O.nZ i : ℝ) * (D.R.f * D.R.m * L.sc.b * L.de2)) ∧
      ∀ v, (Formalism.EigenvalueLevelCeiling.plc v = D.host.pde ↔ q) → ∀ W : Submodule D.what₂.LL (Fin (O.nZ i) → D.what₂.LL),
        (lix v (cut W (O.Ms i)) (cut W (O.Th v i)) : ℝ) ≤ (O.E v i : ℝ) * (finrank D.what₂.LL W : ℝ) + ρ v := by
    intro q i
    by_cases hq : ∃ v₁ : HeightOneSpectrum (𝓞 D.what₂.LL), (Formalism.EigenvalueLevelCeiling.plc v₁ = D.host.pde ↔ q)
    · obtain ⟨v₁, hv₁⟩ := hq
      obtain ⟨ρ, h0, h1, h2⟩ := @exists_rem_of_tie D (recB hc) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ inst _ _ _ _ _ _ _ _ _ _ _ _ (ht v₁ i).1.toFormTieK (hS i).1
        (hR v₁ (hO.ok.laws v₁).p hinj ((i : ℕ) + 1) (inR_succ i)).2
      refine ⟨ρ, h0, h1, fun v hv W => ?_⟩
      have e1 : r.used v = r.used v₁ := by
        unfold TwoRuns.used
        exact if_congr (hv.trans hv₁.symm) rfl rfl
      have e2 : ownAt D v = ownAt D v₁ := by
        unfold ownAt
        exact if_congr (hv.trans hv₁.symm) rfl rfl
      have h3 := (ht v i).1.toFormTieK
      have h4 := (hO.ok.laws v).p
      rw [hd.E_eq v i]
      refine h2 v ?_ _ (nusR_le_eLam Tp hK EX (r.used v₁).full.toTop (hO.ok.laws v₁).p _ (inR_succ i) _) W
      have h5 : ∀ (s : RunData J) (h' : LawsP s.full.toTop) (p' : ℕ), s = r.used v₁ → p' = ownAt D v₁ →
          letI : Algebra (recB h'.toLawsCore).KO D.what₂.LL := inst
          FormTieK (recPJ h' ((i : ℕ) + 1) (inR_succ i)) hinj EX p' (kaR Tp hK ((i : ℕ) + 1)) (lR Tp hK ((i : ℕ) + 1))
            (fR Tp hK ((i : ℕ) + 1)) Tp.TO O v i (z i) (act i) →
          letI : Algebra (recB (hO.ok.laws v₁).p.toLawsCore).KO D.what₂.LL := inst
          FormTieK (recPJ (hO.ok.laws v₁).p ((i : ℕ) + 1) (inR_succ i)) hinj EX (ownAt D v₁) (kaR Tp hK ((i : ℕ) + 1))
            (lR Tp hK ((i : ℕ) + 1)) (fR Tp hK ((i : ℕ) + 1)) Tp.TO O v i (z i) (act i) := by
        rintro _ _ _ rfl rfl h
        exact h
      exact h5 _ h4 _ e1 e2 h3
    · refine ⟨fun _ => 0, fun _ => le_rfl, fun S' => ?_, fun v hv => absurd ⟨v, hv⟩ hq⟩
      have h1 := L.thickDensity_pos
      have h2 : 0 < L.sc.b := Real.exp_pos _
      simp only [mul_zero, Finset.sum_const_zero]
      positivity
  choose ρ h0 h1 h2 using key
  rw [← hd.f_eq, ← hd.m_eq, ← hb] at h1
  choose a ha using fun (v : HeightOneSpectrum (𝓞 D.what₂.LL)) (i : Fin D.R.m) => Formalism.MainNotions.Gaps.LocalGlobalPassage.exists_vw_eq v (O.E v i)
  refine ⟨O.Th, a, fun v i => ρ False i v, fun v i => ρ True i v, L.de2, ?_, L.thickDensity_pos.le, L.thickDensity_le_one,
    fun v i => ⟨h0 _ i v, h0 _ i v⟩, fun i S' => ⟨h1 _ i S', h1 _ i S'⟩⟩
  have hloc : ∀ v (i : Fin D.R.m) (W : Submodule D.what₂.LL (Fin (O.nZ i) → D.what₂.LL)),
      (lix v (cut W (O.Ms i)) (cut W (O.Th v i)) : ℝ) ≤ (O.E v i : ℝ) * (finrank D.what₂.LL W : ℝ) +
        (if Formalism.EigenvalueLevelCeiling.plc v = O.pde then ρ True i v else ρ False i v) := by
    intro v i W
    rw [hO.pde_eq]
    split_ifs with hv
    · exact h2 True i v (iff_true_intro hv) W
    · exact h2 False i v (iff_false_intro hv) W
  intro w hw
  exact ⟨fun i => ⟨((hSp w hw).1 i).1, le_rfl, (ha _ i).1, (ha _ i).2, hloc _ i⟩,
    fun i => ⟨((hSp w hw).2 i).1, le_rfl, (ha _ i).1, (ha _ i).2, hloc _ i⟩⟩

end GlobalTheory.BigOn

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergInvariantFormCompLocalWeilOperator
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.InertVacEquiv

theorem acts_schr_of_ref {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (v : Pl (F := F)) (ψ : AddChar (AF F) ℂ)
    (w : (κ → AF F) × (κ → AF F)) (h₁ : At (evFin F v) w.1) (h₂ : At (evFin F v) w.2)
    (R : (κ → AF F) → ℂ) (hR0 : R 0 ≠ 0) (hR : ∀ x z, At (evFin F v) z → R (x + z) = R x)
    (φ φ₁ : (κ → Fv F v) → ℂ) (h : schr ψ w (tens (evFin F v) φ R) = tens (evFin F v) φ₁ R) :
    Acts (evFin F v) (schr ψ w) φ φ₁ := by
  intro r hr
  funext x
  set y : κ → AF F := fun i => GlobalTheory.LatVac.liftV v (evFin F v (x i)) with hyD
  have hev : ∀ i, evFin F v (y i) = evFin F v (x i) := fun i => GlobalTheory.LatVac.evFin_liftV v _
  have hy : At (evFin F v) y := by
    intro u hu
    funext i
    exact GlobalTheory.LatVac.at_liftV v _ u hu
  have hRy : R y = R 0 := by simpa using hR 0 y hy
  have hRyw : R (y + w.1) = R y := hR y w.1 h₁
  have hrx : r (x + w.1) = r x := hr.1 x w.1 h₁
  have hdot : x ⬝ᵥ w.2 = y ⬝ᵥ w.2 := by
    unfold dotProduct
    refine Finset.sum_congr rfl fun i _ => ?_
    have hz : evFin F v (x i - y i) = 0 := by rw [map_sub, hev, sub_self]
    have h0 := congrFun (h₂ (x i - y i) hz) i
    simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h0
    rw [← sub_eq_zero, ← sub_mul, h0]
  have hφ : (fun i => evFin F v ((x + w.1) i)) = (fun i => evFin F v ((y + w.1) i)) := by
    funext i
    simp only [Pi.add_apply, map_add (f := _), hev]
  have hφ₁ : (fun i => evFin F v (x i)) = (fun i => evFin F v (y i)) := by
    funext i
    exact (hev i).symm
  have key := congrFun h y
  simp only [schr, tens] at key ⊢
  rw [hRyw, hRy] at key
  rw [hdot, hrx, hφ₁]
  have hcanc : ψ (y ⬝ᵥ w.2 + ⅟(2 : AF F) * (w.1 ⬝ᵥ w.2)) * φ (fun i => evFin F v ((x + w.1) i)) =
      φ₁ (fun i => evFin F v (y i)) := by
    apply mul_right_cancel₀ hR0
    rw [hφ, ← key, mul_assoc]
  rw [← mul_assoc, hcanc]

theorem heisInv_comp : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (m : ℕ) (C : Matrix (Fin (a + a')) (Fin m) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))),
    ∀ l : ((Fin a' × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] ℂ, GlobalTheory.InertVacLag.HeisInv G.M' B.ψ v C l →
    ∀ g ∈ UAt σ G.V' (evFin F v),
    ∀ S : ((Fin a' × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] ((Fin a' × Fin (a + a') → Fv F v) → ℂ),
      (∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), S φ ∈ SB (Fin a' × Fin (a + a') → Fv F v) ∧
        Acts (evFin F v) (om' (g, 1)) φ (S φ)) →
      GlobalTheory.InertVacLag.HeisInv G.M' B.ψ v C (l ∘ₗ S) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v m C l hl g _ S hS u hu φ hφ φ₁ hφ₁ hA
  obtain ⟨R, hR0, hRest⟩ := GlobalTheory.RestWitness.exists_rest (Fin a' × Fin (a + a')) v
  have hsp := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hT.weil'
  set u' := GlobalTheory.WeilM.actAB (cA σ) ((g, 1) : UA σ G.V'.J × UA σ G.W.J) u with hu'D
  have hu'eq : u' = mat g * u := by
    simp [hu'D, GlobalTheory.WeilM.actAB, mat]
  obtain ⟨huAt, z, hz⟩ := hu
  have hAt' : At (evFin F v) u' := by
    intro c hc
    rw [hu'eq, ← Matrix.mul_smul, huAt c hc, Matrix.mul_zero]
  have hlag : u' ∈ GlobalTheory.InertVacLag.lagAt v C := ⟨hAt', mat g * z, by rw [hu'eq, hz, Matrix.mul_assoc]⟩
  have hco1 : At (evFin F v) (G.M'.co.e u').1 := by
    intro c hc
    rw [← Prod.smul_fst, ← map_smul, hAt' c hc, map_zero, Prod.fst_zero]
  have hco2 : At (evFin F v) (G.M'.co.e u').2 := by
    intro c hc
    rw [← Prod.smul_snd, ← map_smul, hAt' c hc, map_zero, Prod.snd_zero]
  have hRinv := (hRest 0 (Submodule.zero_mem _)).1
  have hact : Acts (evFin F v) (G.M'.co.rho B.ψ u') (S φ) (S φ₁) := by
    apply acts_schr_of_ref v B.ψ (G.M'.co.e u') hco1 hco2 R hR0 hRinv
    have e1 := (hS φ hφ).2 R (hRest φ hφ)
    have e2 := (hS φ₁ hφ₁).2 R (hRest φ₁ hφ₁)
    have e3 := hA R (hRest φ hφ)
    have e4 := hsp.impl ((g, 1) : UA σ G.V'.J × UA σ G.W.J) u (tens (evFin F v) φ R) (hRest φ hφ).2
    show G.M'.co.rho B.ψ u' (tens (evFin F v) (S φ) R) = tens (evFin F v) (S φ₁) R
    rw [← e1, ← e2, ← e3, hu'D]
    exact e4.symm
  exact hl u' hlag (S φ) (hS φ hφ).1 (S φ₁) (hS φ₁ hφ₁).1 hact

end GlobalTheory.InertVacEquiv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergLatticeVacuumUniqueUpToScalar
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.LatVacUniq

theorem vacuum_unique : ∀ {D : D7} {a a' : ℕ} (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig a a')
    (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F)) (L₁ : Submodule (𝓞 D.host.E) (Fin a' → D.host.E))
    (L₂ : Submodule (𝓞 D.host.E) (Fin (a + a') → D.host.E)) (θ : 𝓞 D.host.E),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PsiUnr Bs.ψ v → L₁.IsLattice D.host.E → L₂.IsLattice D.host.E →
    (∀ z : Matrix (Fin a') (Fin (a + a')) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := D.host.F) (E := D.host.E)), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin D.host.F v) z →
      (z ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV {Γ.V' with L := L₁} {Γ.W with L := L₂} v ↔
        ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV {Γ.V' with L := L₁} {Γ.W with L := L₂} v,
          Bs.ψ (symp (R := AF D.host.F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (-1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.V'.J)
            (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J) z γ) = 1)) →
    (θ : D.host.E) + D.sp.cm.sig θ = 1 →
    ∀ φ₀ ψ₀ : (Fin a' × Fin (a + a') → Fv D.host.F v) → ℂ, φ₀ ∈ GlobalTheory.WeilM.SB _ → φ₀ ≠ 0 → (∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV {Γ.V' with L := L₁} {Γ.W with L := L₂} v,
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (evFin D.host.F v) (Γ.M'.co.rho Bs.ψ γ) φ₀
            (Bs.ψ (⅟(2 : AF D.host.F) * symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (inclR (F := D.host.F) (AF D.host.F) (θ : D.host.E))
              (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.V'.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J) γ γ) • φ₀)) →
      ψ₀ ∈ GlobalTheory.WeilM.SB _ → (∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV {Γ.V' with L := L₁} {Γ.W with L := L₂} v,
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (evFin D.host.F v) (Γ.M'.co.rho Bs.ψ γ) ψ₀
            (Bs.ψ (⅟(2 : AF D.host.F) * symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (inclR (F := D.host.F) (AF D.host.F) (θ : D.host.E))
              (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.V'.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J) γ γ) • ψ₀)) → ∃ c : ℂ, ψ₀ = c • φ₀ := by
  intro D a a' Bs Γ v L₁ L₂ θ hψ hL₁ hL₂ hsd hθ φ₀ ψ₀ hφSB hφ0 hφ hψSB hψ'
  set Λ := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV {Γ.V' with L := L₁} {Γ.W with L := L₂} v with hΛ
  set co := Γ.M'.co with hco
  have hAt : ∀ γ ∈ Λ, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin D.host.F v) γ :=
    (GlobalTheory.LatVac.latAtV_at_stable {Γ.V' with L := L₁} {Γ.W with L := L₂} v).1
  classical
  let χ : (Fin a' × Fin (a + a') → Fv D.host.F v) × (Fin a' × Fin (a + a') → Fv D.host.F v) → ℂ := fun l =>
    if h : ∃ γ ∈ Λ, GlobalTheory.LatVac.locCo co v γ = l then
      Bs.ψ (⅟(2 : AF D.host.F) * symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (inclR (F := D.host.F) (AF D.host.F) (θ : D.host.E))
        (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.V'.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J) h.choose h.choose) else 0
  have loc : ∀ f : (Fin a' × Fin (a + a') → Fv D.host.F v) → ℂ, f ∈ GlobalTheory.WeilM.SB _ →
      (∀ γ ∈ Λ, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (evFin D.host.F v) (co.rho Bs.ψ γ) f
        (Bs.ψ (⅟(2 : AF D.host.F) * symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (inclR (F := D.host.F) (AF D.host.F) (θ : D.host.E))
          (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.V'.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J) γ γ) • f)) →
      ∀ l ∈ Λ.map (GlobalTheory.LatVac.locCo co v), ∀ ξ,
        GlobalTheory.LatVac.psiAt Bs.ψ v (ξ ⬝ᵥ l.2 + (2 : Fv D.host.F v)⁻¹ * (l.1 ⬝ᵥ l.2)) * f (ξ + l.1) = χ l * f ξ := by
    intro f hf hA l hl ξ
    have h : ∃ γ ∈ Λ, GlobalTheory.LatVac.locCo co v γ = l := AddSubgroup.mem_map.mp hl
    obtain ⟨r, hr, x₀, hx₀⟩ := _root_.GlobalTheory.RestComplement.exists_rest_ne_zero v f hf
    have key := _root_.GlobalTheory.LatVac.heis_at_local_identity v co Bs.ψ h.choose f _ (hAt _ h.choose_spec.1) (hA _ h.choose_spec.1) r hr x₀ hx₀ ξ
    simp only [χ, dif_pos h]
    rw [h.choose_spec.2] at key
    exact key
  obtain ⟨c, hc0, hcb⟩ := GlobalTheory.T.tensorLattice_localDarbouxCoords_bounded {Γ.V' with L := L₁} {Γ.W with L := L₂} v co hL₁ hL₂
  have hsd' := _root_.GlobalTheory.LatVac.DualLoc.map_selfDual v co Bs.ψ Λ hAt hsd
  have hfill := _root_.GlobalTheory.SelfDualFirstProj.exists_pair_of_annihilator v (GlobalTheory.LatVac.psiAt Bs.ψ v) (Λ.map (GlobalTheory.LatVac.locCo co v)) c hc0 (fun x => hψ x) hsd'
    (fun l hl i => by
      obtain ⟨γ, hγ, rfl⟩ := AddSubgroup.mem_map.mp hl
      exact hcb γ hγ i)
  exact _root_.GlobalTheory.heisenbergEigen_proportional (GlobalTheory.LatVac.psiAt Bs.ψ v) (Λ.map (GlobalTheory.LatVac.locCo co v)) χ φ₀ ψ₀ (loc φ₀ hφSB hφ) (loc ψ₀ hψSB hψ')
    hφ0 hfill

end GlobalTheory.LatVacUniq
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemAllGaussianWidthsOfFourierStableSchwartz
section
open FourierTransform MeasureTheory Filter Topology

theorem GlobalTheory.GaussWidths.all_widths : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (M : Submodule ℂ (SchwartzMap E ℂ)), IsClosed (M : Set (SchwartzMap E ℂ)) →
    (∀ (ℓ : E →L[ℝ] ℝ) (f f₁ : SchwartzMap E ℂ), f ∈ M → (∀ x, f₁ x = (ℓ x : ℂ) * f x) → f₁ ∈ M) →
    (∀ f ∈ M, 𝓕 f ∈ M) →
    ∀ G : SchwartzMap E ℂ, (∀ y, G y = Complex.exp (-((Real.pi * ‖y‖ ^ 2 : ℝ) : ℂ))) → G ∈ M →
    ∀ (c : ℝ), 0 < c → ∀ g : SchwartzMap E ℂ, (∀ y, g y = Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ))) → g ∈ M :=
  GlobalTheory.GaussWidths.all_widths_of_conv _root_.GlobalTheory.ConvSeries.mem_of_conv_gaussian
end

