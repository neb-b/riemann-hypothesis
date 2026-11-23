module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EntriesWellDefined
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdempotentMulEntryEqZeroOfCutInverse
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0333
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0339
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0362
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ProdDat
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0322
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0337
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0364
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0338
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0312
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0354
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0331
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0300
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0092
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HasConductorMulShift
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0373
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0316
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0289
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1206
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIsometrySignFirst
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0317
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0351
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SemicharacterSqEqOneOnHalfA
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0355

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FixLevCompactOpen
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.FixLev
variable {D : D7}

theorem continuous_mt (V : HSp D) : Continuous (mt V) :=
  Units.continuous_val.comp continuous_subtype_val

section Local
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {Y : Type} [Fintype Y] [DecidableEq Y]

theorem map_mt_mul (q : SplitPt D k) (V : HSp D) (g h : GA D V) :
    (mt V (g * h)).map q.pr = (mt V g).map q.pr * (mt V h).map q.pr := by
  rw [GlobalTheory.SplitCut.mt_mul, Matrix.map_mul]

theorem frame_mul {N : ℕ} (F : GlobalTheory.LocMod.Frame k N Y) (A B : Matrix (Fin N) (Fin N) k) :
    F.γ * A * F.β * (F.γ * B * F.β) = F.γ * (A * B) * F.β := by
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc F.β F.γ, F.βγ, Matrix.one_mul]

theorem frame_cancel {N : ℕ} (F : GlobalTheory.LocMod.Frame k N Y) {A B : Matrix Y Y k}
    (h : F.β * A * F.γ = F.β * B * F.γ) : A = B := by
  have := congrArg (fun M => F.γ * M * F.β) h
  simp only [Matrix.mul_assoc] at this
  simpa [← Matrix.mul_assoc, F.γβ] using this

theorem frame_conj {N : ℕ} (F : GlobalTheory.LocMod.Frame k N Y) (A : Matrix (Fin N) (Fin N) k) :
    F.β * (F.γ * A * F.β) * F.γ = A := by
  simp only [← Matrix.mul_assoc, F.βγ, Matrix.one_mul]
  rw [Matrix.mul_assoc, F.βγ, Matrix.mul_one]

def locHom (q : SplitPt D k) (V : HSp D) (F : GlobalTheory.LocMod.Frame k V.rank Y) : GA D V →* GL Y k where
  toFun g := ⟨F.γ * (mt V g).map q.pr * F.β, F.γ * (mt V g⁻¹).map q.pr * F.β,
    by rw [frame_mul, ← map_mt_mul, mul_inv_cancel, GlobalTheory.SplitCut.mt_one,
      Matrix.map_one _ (map_zero q.pr) (map_one q.pr), Matrix.mul_one, F.γβ],
    by rw [frame_mul, ← map_mt_mul, inv_mul_cancel, GlobalTheory.SplitCut.mt_one,
      Matrix.map_one _ (map_zero q.pr) (map_one q.pr), Matrix.mul_one, F.γβ]⟩
  map_one' := Units.ext (by
    change F.γ * (mt V 1).map q.pr * F.β = 1
    rw [GlobalTheory.SplitCut.mt_one, Matrix.map_one _ (map_zero q.pr) (map_one q.pr), Matrix.mul_one, F.γβ])
  map_mul' g h := Units.ext (by
    change F.γ * (mt V (g * h)).map q.pr * F.β = F.γ * (mt V g).map q.pr * F.β * (F.γ * (mt V h).map q.pr * F.β)
    rw [frame_mul, map_mt_mul])

theorem locHom_val (q : SplitPt D k) (V : HSp D) (F : GlobalTheory.LocMod.Frame k V.rank Y) (g : GA D V) :
    (locHom q V F g).val = F.γ * (mt V g).map q.pr * F.β := rfl

theorem locHom_spec (q : SplitPt D k) (V : HSp D) (F : GlobalTheory.LocMod.Frame k V.rank Y) (g : GA D V) :
    (mt V g).map q.pr = F.β * (locHom q V F g).val * F.γ := by
  rw [locHom_val, frame_conj]

theorem continuous_locHom (q : SplitPt D k) (V : HSp D) (F : GlobalTheory.LocMod.Frame k V.rank Y) :
    Continuous (locHom q V F) := by
  have h1 : Continuous fun g : GA D V => F.γ * (mt V g).map q.pr * F.β :=
    (continuous_const.matrix_mul ((continuous_mt V).matrix_map q.cont_pr)).matrix_mul continuous_const
  refine Units.continuous_iff.2 ⟨h1, ?_⟩
  refine (h1.comp continuous_inv).congr fun g => ?_
  change F.γ * (mt V g⁻¹).map q.pr * F.β = ((locHom q V F g)⁻¹ : GL Y k).val
  rw [← map_inv, locHom_val]

end Local

theorem list_prod_single {M : Type} [Monoid M] {ι : Type} [DecidableEq ι] (f : ι → M) (i : ι)
    (hf : ∀ i', i' ≠ i → f i' = 1) : ∀ l : List ι, l.Nodup → i ∈ l → (l.map f).prod = f i := by
  intro l hl hi
  rw [List.prod_map_eq_pow_single i f (fun i' hne _ => hf i' hne),
    List.count_eq_one_of_mem hl hi, pow_one]

theorem map_mt_list_prod {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : SplitPt D k) (V : HSp D) (l : List (GA D V)) : (mt V l.prod).map q.pr = (l.map fun g => (mt V g).map q.pr).prod := by
  induction l with
  | nil => simp [GlobalTheory.SplitCut.mt_one]
  | cons a l ih => rw [List.prod_cons, map_mt_mul, ih, List.map_cons, List.prod_cons]

theorem exists_section (V : HSp D) {n : ℕ} (k : Fin n → Type) [∀ i, Field (k i)] [∀ i, ValuativeRel (k i)]
    [∀ i, TopologicalSpace (k i)] [∀ i, IsNonarchimedeanLocalField (k i)] (q : ∀ i, SplitPt D (k i))
    (hq : Function.Injective fun i => (q i).v) (Y : Fin n → Type) [∀ i, Fintype (Y i)] [∀ i, DecidableEq (Y i)]
    (F : ∀ i, GlobalTheory.LocMod.Frame (k i) V.rank (Y i)) :
    ∃ Ψ : (∀ i, GL (Y i) (k i)) → GA D V, Continuous Ψ ∧ (∀ x, Ψ x ∈ grpAt V (fun p => ∃ i, p = (q i).v)) ∧
      (∀ x i, (mt V (Ψ x)).map (q i).pr = (F i).β * (x i).val * (F i).γ) ∧
      ∀ g ∈ grpAt V (fun p => ∃ i, p = (q i).v), ∀ x,
        (∀ i, (mt V g).map (q i).pr = (F i).β * (x i).val * (F i).γ) → Ψ x = g := by
  choose gl hgc hgl hgu using fun i => _root_.GlobalTheory.LocEmb.exists_gl D (k i) (q i) V (Y i) (F i)
  have hmat : ∀ (h : Fin n → GA D V), (∀ i, SuppAt (q i).e V (h i)) → ∀ i,
      (mt V ((List.finRange n).map h).prod).map (q i).pr = (mt V (h i)).map (q i).pr := fun h hh i => by
    rw [map_mt_list_prod, List.map_map]
    exact list_prod_single (fun i' => (mt V (h i')).map (q i).pr) i
      (fun i' hi' => _root_.GlobalTheory.OtherPlace.mt_map_pr_eq_one D (k i) (k i') (q i) (q i') V (h i') (fun e => hi' (hq e).symm) (hh i'))
      _ (List.nodup_finRange n) (List.mem_finRange i)
  refine ⟨fun x => ((List.finRange n).map fun i => gl i (x i)).prod, ?_, fun x => ?_, fun x i => ?_, fun g hg x hx => ?_⟩
  · exact continuous_list_prod _ fun i _ => (hgc i).comp (continuous_apply i)
  · refine Subgroup.list_prod_mem (K := grpAt V (fun p => ∃ i, p = (q i).v)) fun y hy => ?_
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hy
    exact _root_.GlobalTheory.SuppGrp.mem_grpAt_of_suppAt D (k i) (q i) V _ (hgl i (x i)).1 _ ⟨i, rfl⟩
  · rw [hmat (fun i => gl i (x i)) (fun i => (hgl i (x i)).1) i]
    exact (hgl i (x i)).2
  · obtain ⟨h, hh, rfl⟩ := GlobalTheory.T.unitarySupported_splitPlaces_eq_prod_local_parts D V n k q hq g hg
    show ((List.finRange n).map fun i => gl i (x i)).prod = _
    congr 1
    refine List.map_congr_left fun i _ => (hgu i (h i) (x i) (hh i) ((hmat h hh i).symm.trans (hx i))).symm


open GlobalTheory.SeeSaw GlobalTheory.StepData in
theorem fixLev_compact_open : ∀ (D : D7) (c : Comm D) (v : VCom c) (n : ℕ) (G : Fin n → GLoc v), GPin G → ∀ j, j < D.R.m →
    v.JG j ≤ grpAt (c.V j) (· ∈ v.gP) ∧ IsCompact (v.JG j : Set (GA D (c.V j))) ∧
    IsOpen (((v.JG j).subgroupOf (grpAt (c.V j) (· ∈ v.gP)) : Subgroup _) : Set (grpAt (c.V j) (· ∈ v.gP))) := by
  intro D c v n G hG j hj
  have ha : ∀ i, j + ((G i).s + 1 - j) = (G i).s + 1 := fun i => by have := (G i).hs; omega
  set V := c.V j
  have hP : (· ∈ v.gP) = fun p => ∃ i, p = (G i).q.v := funext fun p => propext (hG.places p)
  have hMat : ∀ i a ha g x, (G i).Mat j a ha g x ↔ x = locHom (G i).q V ((G i).FY j a ha) g := fun i a ha g x => by
    constructor
    · intro h
      exact Units.ext (frame_cancel ((G i).FY j a ha) (h.symm.trans (locHom_spec _ _ _ g)))
    · rintro rfl
      exact locHom_spec _ _ _ g
  let Js : ∀ i, Subgroup (GL (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin ((G i).s + 1 - j)) (G i).k) := fun i =>
    (((G i).S.T (Fin D.R.t)).lev j _ (ha i)).J
  have hJ : ∀ i, GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsCO (Js i) := fun i =>
    GlobalTheory.UnfoldedEntries.isCO_lev (T := (G i).S.T (Fin D.R.t)) (GlobalTheory.StepData.Chain.ofType_regular _ _ _ _ _) j _ (ha i)
  have hmem : ∀ g, g ∈ v.JG j ↔ g ∈ grpAt V (· ∈ v.gP) ∧ ∀ i, locHom (G i).q V ((G i).FY j _ (ha i)) g ∈ Js i := by
    intro g
    rw [hG.lev j hj g]
    refine and_congr_right fun _ => ⟨fun H i => H i _ (ha i) _ ((hMat _ _ _ _ _).2 rfl), fun H i a ha' x hx => ?_⟩
    have e : a = (G i).s + 1 - j := by omega
    subst e
    rw [(hMat _ _ _ _ _).1 hx]
    exact H i
  refine ⟨fun g hg => ((hmem g).1 hg).1, ?_, ?_⟩
  · obtain ⟨Ψ, hc, hin, hloc, huniq⟩ := exists_section V (fun i => (G i).k) (fun i => (G i).q) hG.inj
      (fun i => XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin ((G i).s + 1 - j)) (fun i => (G i).FY j _ (ha i))
    have himg : (v.JG j : Set (GA D V)) = Ψ '' Set.pi Set.univ fun i => (Js i : Set _) := by
      ext g
      constructor
      · intro hg
        obtain ⟨h1, h2⟩ := (hmem g).1 hg
        refine ⟨fun i => locHom (G i).q V ((G i).FY j _ (ha i)) g, fun i _ => h2 i, huniq g (hP ▸ h1) _ fun i => ?_⟩
        exact locHom_spec _ _ _ g
      · rintro ⟨x, hx, rfl⟩
        refine (hmem _).2 ⟨hP ▸ hin x, fun i => ?_⟩
        have e : locHom (G i).q V ((G i).FY j _ (ha i)) (Ψ x) = x i :=
          Units.ext (frame_cancel ((G i).FY j _ (ha i)) ((locHom_spec _ _ _ _).symm.trans (hloc x i)))
        rw [e]
        exact hx i (Set.mem_univ _)
    rw [himg]
    exact (isCompact_univ_pi fun i => (hJ i).2).image hc
  · have hset : (((v.JG j).subgroupOf (grpAt V (· ∈ v.gP)) : Subgroup _) : Set (grpAt V (· ∈ v.gP))) =
        ⋂ i, (fun g : grpAt V (· ∈ v.gP) => locHom (G i).q V ((G i).FY j _ (ha i)) g.1) ⁻¹' (Js i : Set _) := by
      ext g
      simp only [SetLike.mem_coe, Subgroup.mem_subgroupOf, Set.mem_iInter, Set.mem_preimage]
      exact ((hmem g.1).trans (and_iff_right g.2))
    rw [hset]
    exact isOpen_iInter_of_finite fun i =>
      (hJ i).1.preimage ((continuous_locHom _ _ _).comp continuous_subtype_val)

end GlobalTheory.FixLev
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FoldrSplitPlaceSecondCombinationsVacuumNeZero
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam

noncomputable section
namespace GlobalTheory.VacComb

variable {D : D7}

theorem isThetaFunO_zero (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) : IsThetaFunO ψ S T 0 := {
  quasi _ _ := by simp
  level := ⟨⊤, isOpen_univ, fun _ _ _ => funext fun _ => by simp [heisO]⟩
  cont := continuous_const
  smooth _ _ _ _ _ := by simpa using (contDiff_const : ContDiff ℝ _ fun _ : Fin _ → ℝ => (0 : ℂ)) }

theorem heisO_zero (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (u : WO S T) : heisO ψ S T u 0 = 0 :=
  funext fun _ => by simp [heisO]

theorem isModel_zero {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y']
    [DecidableEq Y'] (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) :
    p.IsModel ψ FS FT (0 : SB (Matrix Y Y' k) →ₗ[ℂ] (WO S T → ℂ)) := {
  theta _ := isThetaFunO_zero ψ S T
  trans _ _ _ _ := by simp [heisO_zero]
  modul _ _ _ _ _ := by simp [heisO_zero] }

theorem model_ne_zero {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D} {Y Y' : Type} [Fintype Y]
    [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] {FS : Frame k S.rank Y'} {FT : Frame k T.rank Y} {Tm}
    (hTm : p.IsModel ψ FS FT Tm) {Φ₀ : SB (Matrix Y Y' k)} (h₀ : Tm Φ₀ ≠ 0) {O : SB (Matrix Y Y' k)} (hO : O ≠ 0) :
    Tm O ≠ 0 := by
  intro h
  have := (_root_.GlobalTheory.LocModU.localModel_uniq_transport_exist D k p Y Y' S T FS FT ψ hψ).1 Tm 0 hTm (isModel_zero p ψ FS FT) O hO (by simpa using h)
  exact h₀ (by rw [this]; rfl)

end GlobalTheory.VacComb

namespace GlobalTheory.VacComb

theorem exists_adapted_frame : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (S : HSp D) (M : GlobalTheory.FinPl.Lat S), IsSelfDualC S M → ∀ (Y : Type) [Fintype Y] [DecidableEq Y] (F : Frame k S.rank Y), ∃ G : Frame k S.rank Y, ∀ y : Y → k, (∀ i, y i ∈ 𝒪[k]) ↔ (fun i => q.sec ((G.β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV S M (· = q.v) := by
  intro D k _ _ _ _ q S M hM Y _ _ F
  obtain ⟨gl, h1, h2⟩ := _root_.GlobalTheory.GlEmbed.exists_gl D k q S Y F.β F.γ F.βγ F.γβ
  let α : GlobalTheory.FinPl.Frame q S Y := ⟨F.β, F.γ, F.βγ, F.γβ, gl, h1, h2⟩
  obtain ⟨Λ, hΛ, hα, -⟩ := GlobalTheory.FinPl.FrameLat.exists_lat D k q S Y α M hM
  have : Λ.IsFullLattice k := by
    refine { toIsLattice := hΛ, span_eq_top := eq_top_iff.mpr fun x _ => ?_ }
    obtain ⟨m, s, c, hs, hc, -⟩ := GlobalTheory.FinPl.FrameLat.exists_gen (p := q) hM
    have hx := congrArg (F.γ *ᵥ ·) (hc (F.β *ᵥ x))
    simp only [Matrix.mulVec_mulVec, F.γβ, Matrix.one_mulVec, Matrix.mulVec_sum,
      Matrix.mulVec_smul] at hx
    rw [hx]
    refine Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    apply (hα _).2
    change (fun i => q.sec ((F.β *ᵥ (F.γ *ᵥ fun a => q.pr (incA D (s l a)))) i)) ∈ _
    rw [Matrix.mulVec_mulVec, F.βγ, Matrix.one_mulVec]
    exact GlobalTheory.FinPl.FrameLat.sec_inc_mem (p := q) (hs l)
  obtain ⟨g, hg⟩ := GlobalTheory.LatPair.exists_smul_lat (GlobalTheory.LatPair.stdLat k Y) Λ
  have hgg : g.1 * (g⁻¹).1 = 1 := by rw [← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel, Matrix.GeneralLinearGroup.coe_one]
  have hgg' : (g⁻¹).1 * g.1 = 1 := by rw [← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel, Matrix.GeneralLinearGroup.coe_one]
  refine ⟨⟨F.β * g.1, (g⁻¹).1 * F.γ, ?_, ?_⟩, fun y => ?_⟩
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc g.1, hgg, Matrix.one_mul, F.βγ]
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc F.γ, F.γβ, Matrix.one_mul, hgg']
  · have e1 : (∀ i, y i ∈ 𝒪[k]) ↔ g • y ∈ Λ := by
      rw [← hg, GlobalTheory.LatPair.mem_smul_iff, inv_smul_smul, GlobalTheory.LatPair.mem_stdLat]
    rw [e1, hα (g • y)]
    show _ ∈ _ ↔ _ ∈ _
    have e2 : F.β *ᵥ (g • y) = (F.β * g.1) *ᵥ y := by
      rw [← Matrix.mulVec_mulVec]; rfl
    change (fun i => q.sec ((F.β *ᵥ (g • y)) i)) ∈ _ ↔ _
    rw [e2]

end GlobalTheory.VacComb

namespace GlobalTheory.VacComb

variable {D : D7}

theorem down_up {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) {S T : HSp D} {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']
    (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (x : Matrix Y Y' k) : p.down FS FT (p.up FS FT x) = x := by
  unfold Place.down Place.up
  have h : ((FT.β * x * FS.γ).map p.ι : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map p.π = FT.β * x * FS.γ := by
    ext i j; simp [p.π_ι]
  rw [h, Matrix.mul_assoc FT.β, ← Matrix.mul_assoc FT.γ, FT.γβ, Matrix.one_mul, Matrix.mul_assoc, FS.γβ, Matrix.mul_one]

theorem exists_model_vac : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k), q.UnitAA → ∀ (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (S T : HSp D) (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (M : GlobalTheory.FinPl.Lat S) (M' : GlobalTheory.FinPl.Lat T), IsSelfDualC S M → IsSelfDualC T M' → ∀ G, GlobalTheory.FinPl.Vac ψ S T M M' (· = q.v) G → ∃ Tm, (ofSplit q).IsModel ψ FS FT Tm ∧ ∀ Φ₀ : SB (Matrix Y Y' k), Φ₀.1 = Set.indicator {x | (ofSplit q).up FS FT x ∈ latO S T (M : Set (Fin S.rank → D.host.E)) (M' : Set (Fin T.rank → D.host.E)) (· = q.v)} (fun _ => 1) → Tm Φ₀ = G := by
  intro D k _ _ _ _ q hU Y Y' _ _ _ _ S T FS FT ψ hψ M M' hM hM' G hG
  obtain ⟨GS, hGS⟩ := exists_adapted_frame D k q S M hM Y' FS
  obtain ⟨GT, hGT⟩ := exists_adapted_frame D k q T M' hM' Y FT
  obtain ⟨ψk, hch, hcond⟩ := GlobalTheory.SplitWeilChar.weil_char_conductor_one D k q ψ hψ hU
  obtain ⟨Tm', hTm', hO'⟩ := (_root_.GlobalTheory.LocMod.indicator_vac D k q hU Y Y' S T GS GT ψ ψk hψ hch hcond M M' hM hM' hGS hGT).2 G hG
  obtain ⟨Tm, hTm, hrel⟩ := GlobalTheory.LocMod.Place.exists_isModel_chg D k (ofSplit q) Y Y' S T GS GT Y Y' FS FT ψ Tm' hTm'
  obtain ⟨O, hO, -⟩ := GlobalTheory.LocMod.PinModel.exists_isOne (k := k) (Y := Y) (Y' := Y')
  refine ⟨Tm, hTm, fun Φ₀ h₀ => ?_⟩
  rw [hrel O Φ₀ ?_, hO' O hO]
  intro x
  have hup : (ofSplit q).up FS FT (FT.γ * GT.β * x * (GS.γ * FS.β)) = (ofSplit q).up GS GT x :=
    GlobalTheory.LocMod.Place.up_chg (ofSplit q) GS GT FS FT x
  rw [hO, h₀]
  by_cases hx : ∀ r s, x r s ∈ 𝒪[k]
  · rw [Set.indicator_of_mem (show x ∈ {x : Matrix Y Y' k | ∀ r s, x r s ∈ 𝒪[k]} from hx), Set.indicator_of_mem]
    show (ofSplit q).up FS FT (FT.γ * GT.β * x * (GS.γ * FS.β)) ∈ latO S T (M : Set (Fin S.rank → D.host.E)) (M' : Set (Fin T.rank → D.host.E)) (· = q.v)
    rw [hup]
    exact _root_.GlobalTheory.UpMem.up_mem_latO D k q hU Y Y' S T GS GT M M' hM hM' hGS hGT x hx
  · rw [Set.indicator_of_notMem (show x ∉ {x : Matrix Y Y' k | ∀ r s, x r s ∈ 𝒪[k]} from hx), Set.indicator_of_notMem]
    intro hmem
    change (ofSplit q).up FS FT (FT.γ * GT.β * x * (GS.γ * FS.β)) ∈ latO S T (M : Set (Fin S.rank → D.host.E)) (M' : Set (Fin T.rank → D.host.E)) (· = q.v) at hmem
    rw [hup] at hmem
    obtain ⟨x', hx', he⟩ := _root_.GlobalTheory.HalfIntUp.exists_int_up D k q hU Y Y' S T GS GT M M' hM hM' hGS hGT _ hmem
      (GlobalTheory.LocMod.Witness.up_half (ofSplit q) GS GT x)
    have : x = x' := by rw [← down_up (ofSplit q) GS GT x, he, down_up]
    exact hx (this ▸ hx')

end GlobalTheory.VacComb

namespace GlobalTheory.VacComb

variable {D : D7}

theorem comb_o_ne_zero {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D}
    {M : GlobalTheory.FinPl.Lat S} {M' : GlobalTheory.FinPl.Lat T} (hM : IsSelfDualC S M) (hM' : IsSelfDualC T M')
    (L : LocPl ψ S T M M') {G : WO S T → ℂ} (hG : GlobalTheory.FinPl.Vac ψ S T M M' (· = L.q.v) G) (hG0 : G ≠ 0) :
    comb ψ S T L.o G ≠ 0 := by
  obtain ⟨Tm, hTm, hTG⟩ := exists_model_vac D L.k L.q L.unit L.Y L.Y' S T L.FS L.FT ψ hψ M M' hM hM' G hG
  obtain ⟨Φ₀, h₀⟩ := GlobalTheory.SeeSaw.LocPlModel.exists_latInd L.q L.unit L.FS L.FT hM hM'
  obtain ⟨O, hO, hO0⟩ := GlobalTheory.LocMod.PinModel.exists_isOne (k := L.k) (Y := L.Y) (Y' := L.Y')
  have hO' : O ≠ 0 := by rintro rfl; simp at hO0
  rw [← hTG Φ₀ h₀, ← L.o_is Tm hTm Φ₀ O hO h₀]
  exact model_ne_zero _ hψ hTm (by rwa [hTG Φ₀ h₀]) hO'

theorem combAt_o {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {M : GlobalTheory.FinPl.Lat S} {M' : GlobalTheory.FinPl.Lat T}
    (L : LocPl ψ S T M M') : GlobalTheory.FinPl.CombAt (· = L.q.v) L.o := fun u hu r c =>
  (GlobalTheory.FinPl.FrameLat.idem_iff L.q _).2 (L.o_at u hu r c)

theorem foldr_comb_ne_zero : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (M : GlobalTheory.FinPl.Lat S) (M' : GlobalTheory.FinPl.Lat T), IsSelfDualC S M → IsSelfDualC T M' → ∀ (n : ℕ) (L : Fin n → GlobalTheory.SeeSaw.LocPl ψ S T M M'), (Function.Injective fun i => (L i).q.v) → ∀ F, GlobalTheory.FinPl.Vac ψ S T M M' (fun _ => True) F → F ≠ 0 → (List.finRange n).foldr (fun i g => comb ψ S T (L i).o g) F ≠ 0 := by
  intro D ψ hψ S T M M' hM hM' n L hL F hF hF0
  have hI := fun P P' hd => _root_.GlobalTheory.DisjComb.main D ψ hψ S T P P' hd
  let g : Fin n → (WO S T → ℂ) → (WO S T → ℂ) := fun i f => comb ψ S T (L i).o f
  have key : ∀ l : List (Fin n), l.Nodup → l.foldr g F ≠ 0 ∧
      ∀ j, j ∉ l → GlobalTheory.FinPl.Vac ψ S T M M' (· = (L j).q.v) (l.foldr g F) := by
    intro l
    induction l with
    | nil =>
      intro _
      exact ⟨hF0, fun j _ => GlobalTheory.GSuppComb.vac_mono (fun _ _ => trivial) hF⟩
    | cons a l ih =>
      intro hl
      obtain ⟨ha, hl'⟩ := List.nodup_cons.1 hl
      obtain ⟨h0, hv⟩ := ih hl'
      have hdisj : ∀ j, j ≠ a → ∀ p, p = (L a).q.v → ¬ p = (L j).q.v := fun j hj p hp hq =>
        hj (hL (hq.symm.trans hp))
      refine ⟨comb_o_ne_zero hψ hM hM' (L a) (hv a ha) h0, fun j hj => ?_⟩
      have hja : j ≠ a := fun h => hj (h ▸ List.mem_cons_self)
      have hjl : j ∉ l := fun h => hj (List.mem_cons_of_mem _ h)
      exact ((hI _ _ (hdisj j hja)).2.1 _ (combAt_o (L a))).2 M M' _ (hv j hjl)
  exact (key _ (List.nodup_finRange n)).1

end GlobalTheory.VacComb
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombAwayFromPlaceKeepsVacuum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.QVal GlobalTheory.FinPl

noncomputable section

namespace GlobalTheory.VacAway

variable {D : D7}

def combL (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (c : WO S T →₀ ℂ) : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ) where
  toFun := comb ψ S T c
  map_add' f g := by
    funext w
    simp only [comb, heisO, Finset.sum_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib]
  map_smul' a f := by
    funext w
    simp only [comb, heisO, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun u _ => by ring

theorem comb_single_one (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (y : WO S T) (f : WO S T → ℂ) :
    comb ψ S T (Finsupp.single y 1) f = heisO ψ S T y f := by
  unfold comb
  rw [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.sum_singleton, Finsupp.single_eq_same, one_smul]

theorem vac_comb : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (σ : ℕ) (S : Dbl2 ψ σ) (Q₀ : QStep S) (c₁ : WO S.B.V S.J.W →₀ ℂ) (c₂ : WO S.J.W S.B'.V →₀ ℂ), IsFinComb c₁ → IsFinComb c₂ → Q₀.Away c₁ → Q₀.Away c₂ → ∀ f₁ f₂, IsThetaFunO ψ _ _ f₁ → IsThetaFunO ψ _ _ f₂ → Q₀.Vac f₁ f₂ → Q₀.Vac (comb ψ _ _ c₁ f₁) (comb ψ _ _ c₂ f₂) := by
  intro D ψ hψ σ S Q₀ c₁ c₂ hc₁ hc₂ ha₁ ha₂ f₁ f₂ _ _ hv
  obtain ⟨hee, hec, -⟩ := Q₀.q.split
  have hce : cA D Q₀.q.e * Q₀.q.e = 0 := by rw [mul_comm, hec]
  have hcc : cA D Q₀.q.e * cA D Q₀.q.e = cA D Q₀.q.e := by rw [← map_mul, hee]
  have hreal : cA D (Q₀.q.e + cA D Q₀.q.e) = Q₀.q.e + cA D Q₀.q.e := by
    rw [map_add (f := _), Formalism.L2.Theta.cA_cA, add_comm]
  have hidem : (Q₀.q.e + cA D Q₀.q.e) * (Q₀.q.e + cA D Q₀.q.e) = Q₀.q.e + cA D Q₀.q.e := by
    rw [add_mul, mul_add, mul_add, hee, hec, hce, hcc, add_zero, zero_add]
  have horth : (Q₀.q.e + cA D Q₀.q.e) * (1 - (Q₀.q.e + cA D Q₀.q.e)) = 0 := by
    rw [mul_sub, mul_one, hidem, sub_self]
  have comm : ∀ {A B : HSp D} (c : WO A B →₀ ℂ), Q₀.Away c → ∀ (f : WO A B → ℂ) (y : WO A B),
      IsHalf (Q₀.q.e + cA D Q₀.q.e) y → comb ψ A B c (heisO ψ A B y f) = heisO ψ A B y (comb ψ A B c f) := by
    intro A B c ha f y hy
    have h := (GlobalTheory.HeisComb.main D ψ A B).2.1 (Finsupp.single y 1) c (fun x hx u hu => by
      have hxy : x = y := Finset.mem_singleton.1 (Finsupp.support_single_subset hx)
      subst hxy
      exact GlobalTheory.HeisComb.symplO_half A B _ _ x u hreal horth hy (ha u hu)) f
    rw [comb_single_one, comb_single_one] at h
    exact h.symm
  obtain ⟨⟨T₁, O₁, hT₁, hO₁, rfl⟩, ⟨T₂, O₂, hT₂, hO₂, rfl⟩⟩ := hv
  refine ⟨⟨combL ψ _ _ c₁ ∘ₗ T₁, O₁, ?_, hO₁, rfl⟩, ⟨combL ψ _ _ c₂ ∘ₗ T₂, O₂, ?_, hO₂, rfl⟩⟩
  · exact (GlobalTheory.LocModU.localModel_uniq_transport_exist D Q₀.k (ofSplit Q₀.q) _ _ _ _ Q₀.F.G₀ Q₀.F.G₁ ψ hψ).2.1 T₁ hT₁
      (combL ψ _ _ c₁) (fun f hf => (GlobalTheory.HeisComb.main D ψ _ _).2.2.1 c₁ f hf hc₁ hψ)
      (fun f _ y hy => comm c₁ ha₁ f y hy)
  · exact (GlobalTheory.LocModU.localModel_uniq_transport_exist D Q₀.k (ofSplit Q₀.q) _ _ _ _ Q₀.F.G₁ Q₀.F.G₂ ψ hψ).2.1 T₂ hT₂
      (combL ψ _ _ c₂) (fun f hf => (GlobalTheory.HeisComb.main D ψ _ _).2.2.1 c₂ f hf hc₂ hψ)
      (fun f _ y hy => comm c₂ ha₂ f y hy)

end GlobalTheory.VacAway

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergOperatorHalfComponentOnVacuumTranslate
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.AdForm.HalfHeis.heisO_halfA_eq : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (a b : ℕ) (hS : S.rank = a) (hT : T.rank = b) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ (e : AE D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → ∀ (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)) (c : ℕ), 0 < c → Odd c → (∀ Q ∈ SS, ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal) → LaFacts (tauE D) δ D.host.d sc (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N' → ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → (ΛS : Set (Fin S.rank → D.host.E)) = latFr S hS N → (ΛT : Set (Fin T.rank → D.host.E)) = latFr T hT N' → ∀ f₀, IsVacO ψ θ S T (fun _ => 1) (fun _ => 1) (latFr S hS N) (latFr T hT N') f₀ → ∀ x' ∈ halfAO SS (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') c, ∀ y' ∈ halfBO SS (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') c, heisO ψ S T (((LinearMap.toMatrix' (x')).reindex (finCongr hT.symm) (finCongr hS.symm)).map fun r => e * incA D r) (heisO ψ S T (GlobalTheory.VacUnique.finRat S T ((LinearMap.toMatrix' (y')).reindex (finCongr hT.symm) (finCongr hS.symm))) f₀) = alV D.host.d sc (embH (tauE D) δ x') • heisO ψ S T (GlobalTheory.VacUnique.finRat S T ((LinearMap.toMatrix' (x')).reindex (finCongr hT.symm) (finCongr hS.symm))) (heisO ψ S T (GlobalTheory.VacUnique.finRat S T ((LinearMap.toMatrix' (y')).reindex (finCongr hT.symm) (finCongr hS.symm))) f₀) := by
  intro D ψ θ S T a b hS hT δ sc hP e SS hE N N' c hc hcP h2 _ ΛS ΛT dS dT eS eT f₀ hV x' hx y' hy
  subst hS hT
  obtain rfl : ΛS = N := SetLike.coe_injective eS
  obtain rfl : ΛT = N' := SetLike.coe_injective eT
  rw [← eS, ← eT] at hV
  change heisO ψ S T ((LinearMap.toMatrix' x').map fun r => e * incA D r)
      (heisO ψ S T (GlobalTheory.VacUnique.finRat S T (LinearMap.toMatrix' y')) f₀) =
    alV D.host.d sc (embH (tauE D) δ x') • heisO ψ S T (GlobalTheory.VacUnique.finRat S T (LinearMap.toMatrix' x'))
      (heisO ψ S T (GlobalTheory.VacUnique.finRat S T (LinearMap.toMatrix' y')) f₀)
  set Xt : WO S T := (LinearMap.toMatrix' x').map fun r => e * incA D r with hXt
  set FX := GlobalTheory.VacUnique.finRat S T (LinearMap.toMatrix' x') with hFX
  set FY := GlobalTheory.VacUnique.finRat S T (LinearMap.toMatrix' y') with hFY
  set α := alV D.host.d sc (embH (tauE D) δ x') with hα
  have hact := _root_.GlobalTheory.HalfARest.heisO_rest_eq D ψ θ S T δ sc hP e SS hE h2 ΛS ΛT dS dT c hc hcP f₀ hV x' hx
  have hcomm := _root_.GlobalTheory.FinRestComm.char_sympl_rest_eq_one D ψ θ S T δ sc hP e SS hE h2 ΛS ΛT dS dT c hc hcP x' hx y' hy
  have hcoc := _root_.GlobalTheory.AdForm.CocycleSS.cocycle_trivial D ψ θ S T δ sc hP e SS hE h2 ΛS ΛT dS dT c hc hcP x' hx
  have hsq := _root_.GlobalTheory.AdForm.HalfASign.alV_mul_self_halfA D ψ θ S T δ sc hP e SS hE h2 ΛS ΛT dS dT c hc hcP x' hx
  have hZ : heisO ψ S T (FX - Xt) (heisO ψ S T FY f₀) = α • heisO ψ S T FY f₀ := by
    rw [GlobalTheory.SplitScalar.heisO_comm, hcomm, one_smul, hact, GlobalTheory.SplitScalar.heisO_smul]
  have hX := GlobalTheory.SplitScalar.heisO_heisO ψ S T Xt (FX - Xt) (heisO ψ S T FY f₀)
  rw [hcoc, one_smul, add_sub_cancel, hZ, GlobalTheory.SplitScalar.heisO_smul] at hX
  rw [← hX, smul_smul, hsq, one_smul]
end

