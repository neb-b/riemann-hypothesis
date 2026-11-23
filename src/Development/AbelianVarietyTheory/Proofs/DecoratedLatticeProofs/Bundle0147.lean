module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0226
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0283
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0174
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0245
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0221
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowestKTypesJointShapeBlockUnitary
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0535
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0264
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0141
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EntryAgree
public import Formalism.LocalToGlobal.Columns.ChainTw

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRealIntertwinerNeZeroKFiniteTensor
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Chain.IoLift.ItNe

open GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace

theorem exists_ne_zero_inclK : GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (V W : HSp D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S') (θ : InfFam D) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (pt : PolF D W.rank V.rank → (WO V W → ℂ)) (It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M), IsItW θ M M' ω pt It → ∀ h' : GlobalTheory.Chain.IoLift.KSm M', ∃ φ y, It φ (GlobalTheory.Chain.IoLift.inclK h' y) ≠ 0 := by
  classical
  intro hHC D V W S S' M M' θ ω pt It hIt h'
  apply Classical.byContradiction
  intro hcon
  push_neg at hcon
  apply hIt.ne
  have key : ∀ φ (w : ∀ τ, M.H τ) (s : Finset D.what₂.Tau) (v : M'.Vec),
      (∀ τ ∉ s, (v τ : M'.H τ) ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M' τ) →
      ellT M w (inclT M (It φ (PiTensorProduct.tprod ℂ v))) = 0 := by
    intro φ w s
    induction s using Finset.induction_on with
    | empty =>
      intro v hv
      have e : PiTensorProduct.tprod ℂ v =
          GlobalTheory.Chain.IoLift.inclK h' (PiTensorProduct.tprod ℂ fun τ => ⟨v τ, hv τ (by simp)⟩) := by
        rw [GlobalTheory.Chain.IoLift.inclK, PiTensorProduct.map_tprod]; rfl
      rw [e, hcon, map_zero, map_zero]
    | insert τ s hτ ih =>
      intro v hv
      obtain ⟨c, hc⟩ := hIt.bdd φ w
      let ℓ₀ : M'.sm τ →ₗ[ℂ] ℂ :=
        (ellT M w ∘ₗ inclT M ∘ₗ It φ) ∘ₗ (PiTensorProduct.tprod ℂ).toLinearMap v τ
      obtain ⟨ℓ, hℓ⟩ := LinearMap.exists_extend ℓ₀
      have hℓv : ∀ y : M'.sm τ, ℓ (y : M'.H τ) =
          ellT M w (inclT M (It φ (PiTensorProduct.tprod ℂ (Function.update v τ y)))) := fun y => by
        have := LinearMap.congr_fun hℓ y
        simpa [ℓ₀, MultilinearMap.toLinearMap_apply] using this
      have hsob : Formalism.L2.Theta.Sobolev₂ (lieAt W τ) (M'.rep τ) ℓ := by
        refine ⟨[[]], c * ∏ ρ ∈ Finset.univ.erase τ, ‖(v ρ : M'.H ρ)‖, by simp, fun u hu => ?_⟩
        have hy : u ∈ M'.sm τ := Submodule.subset_span hu
        have h1 := hc (Function.update v τ ⟨u, hy⟩)
        rw [← hℓv ⟨u, hy⟩] at h1
        have h2 : ∏ ρ, ‖((Function.update v τ ⟨u, hy⟩ ρ : M'.sm ρ) : M'.H ρ)‖ =
            ‖u‖ * ∏ ρ ∈ Finset.univ.erase τ, ‖(v ρ : M'.H ρ)‖ := by
          rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ τ), Function.update_self]
          congr 1
          refine Finset.prod_congr rfl fun ρ hρ => ?_
          rw [Function.update_of_ne (Finset.ne_of_mem_erase hρ)]
        rw [h2] at h1
        simp only [List.map_cons, List.map_nil, List.foldr_nil, List.sum_cons, List.sum_nil, add_zero]
        calc ‖ℓ u‖ ≤ c * (‖u‖ * ∏ ρ ∈ Finset.univ.erase τ, ‖(v ρ : M'.H ρ)‖) := h1
          _ = c * (∏ ρ ∈ Finset.univ.erase τ, ‖(v ρ : M'.H ρ)‖) * ‖u‖ := by ring
      have hk : ∀ u ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M' τ, ℓ u = 0 := by
        intro u hu
        have hy : u ∈ M'.sm τ := h' τ hu
        rw [show u = ((⟨u, hy⟩ : M'.sm τ) : M'.H τ) from rfl, hℓv]
        refine ih _ fun ρ hρ => ?_
        by_cases e : ρ = τ
        · subst e; rw [Function.update_self]; exact hu
        · rw [Function.update_of_ne e]; exact hv ρ (by simp [e, hρ])
      have h0 := GlobalTheory.KFiniteDense.eq_zero_of_kFin hHC D W S' M' τ ℓ hsob hk (v τ) (v τ).2
      rwa [hℓv, Function.update_eq_self] at h0
  refine LinearMap.ext fun φ => LinearMap.ext fun x => ?_
  simp only [LinearMap.zero_apply]
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r v =>
    rw [map_smul]
    have h0 : It φ (PiTensorProduct.tprod ℂ v) = 0 := by
      refine (tensorLaw D V S M).inj ?_
      rw [map_zero]
      exact (tensorLaw D V S M).sep _ fun w => key φ w Finset.univ v (by simp)
    rw [h0, smul_zero]
  | add a b ha hb => rw [map_add (f := _), ha, hb, add_zero]

end GlobalTheory.Chain.IoLift.ItNe
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FinitePartMemFrameStabilizerIffLocalStabilizer
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.ChainOnto.LStab
section General
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem col_mem_hatL {β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} {Λ : Submodule (𝓞 E) (Fin n → E)} (hβ : IsFrame β Λ)
    (j : Fin n) : β.1 *ᵥ Pi.single j 1 ∈ Formalism.L2.Herm.hatL (F := F) Λ := by
  rw [hβ]
  intro k
  rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec, Pi.single_apply]
  split_ifs
  · exact Subring.one_mem _
  · exact Subring.zero_mem _

theorem exists_fg_sub {β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} {Λ : Submodule (𝓞 E) (Fin n → E)} (hβ : IsFrame β Λ) :
    ∃ Λ₁ ≤ Λ, Λ₁.FG ∧ Formalism.L2.Herm.hatL (F := F) Λ₁ = Formalism.L2.Herm.hatL (F := F) Λ := by
  classical
  have hcol : ∀ j, ∃ T : Finset (Fin n → E ⊗[F] Formalism.L2.Herm.Af F),
      (T : Set (Fin n → E ⊗[F] Formalism.L2.Herm.Af F)) ⊆ (fun x : Fin n → E => fun i => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (x i)) '' (Λ : Set (Fin n → E)) ∧
      β.1 *ᵥ Pi.single j 1 ∈ Submodule.span (Formalism.L2.Herm.intAf F E) (T : Set (Fin n → E ⊗[F] Formalism.L2.Herm.Af F)) := fun j =>
    Submodule.mem_span_finite_of_mem_span (col_mem_hatL hβ j)
  choose T hT hmem using hcol
  let U : Finset (Fin n → E ⊗[F] Formalism.L2.Herm.Af F) := Finset.univ.biUnion T
  have hUsub : ∀ y ∈ U, ∃ x ∈ Λ, (fun i => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (x i)) = y := fun y hy => by
    obtain ⟨j, -, hj⟩ := Finset.mem_biUnion.1 hy
    obtain ⟨x, hx, e⟩ := hT j hj
    exact ⟨x, hx, e⟩
  choose! pre hpre hpref using hUsub
  have hle : Submodule.span (𝓞 E) (pre '' (U : Set (Fin n → E ⊗[F] Formalism.L2.Herm.Af F))) ≤ Λ := by
    rw [Submodule.span_le]
    rintro _ ⟨y, hy, rfl⟩
    exact hpre y hy
  refine ⟨Submodule.span (𝓞 E) (pre '' (U : Set (Fin n → E ⊗[F] Formalism.L2.Herm.Af F))), hle,
    Submodule.fg_def.2 ⟨_, (U.finite_toSet.image pre), rfl⟩, le_antisymm ?_ ?_⟩
  · refine Submodule.span_mono ?_
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, hle hx, rfl⟩
  · have hcolm : ∀ j, β.1 *ᵥ Pi.single j 1 ∈ Formalism.L2.Herm.hatL (F := F) (Submodule.span (𝓞 E) (pre '' (U : Set (Fin n → E ⊗[F] Formalism.L2.Herm.Af F)))) := by
      intro j
      refine Submodule.span_mono ?_ (hmem j)
      intro y hy
      have hyU : y ∈ U := Finset.mem_biUnion.2 ⟨j, Finset.mem_univ _, hy⟩
      exact ⟨pre y, Submodule.subset_span ⟨y, hyU, rfl⟩, hpref y hyU⟩
    intro y hy
    have hc := (hβ y).1 hy
    obtain ⟨c, hcdef⟩ : ∃ c, c = (β⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)).1 *ᵥ y := ⟨_, rfl⟩
    rw [← hcdef] at hc
    have ey : y = ∑ j, c j • (β.1 *ᵥ Pi.single j 1) := by
      have e1 : y = β.1 *ᵥ c := by
        rw [hcdef, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
      have e2 : c = ∑ j, c j • (Pi.single j 1 : Fin n → E ⊗[F] Formalism.L2.Herm.Af F) := by
        funext k
        simp [Finset.sum_apply, Pi.single_apply]
      rw [e1]
      conv_lhs => rw [e2]
      rw [Matrix.mulVec_sum]
      exact Finset.sum_congr rfl fun j _ => Matrix.mulVec_smul _ _ _
    rw [ey]
    refine Submodule.sum_mem _ fun j _ => ?_
    exact Submodule.smul_mem _ (⟨c j, hc j⟩ : Formalism.L2.Herm.intAf F E) (hcolm j)

theorem latLoc_eq {Λ₁ Λ : Submodule (𝓞 E) (Fin n → E)} (hle : Λ₁ ≤ Λ) (hfg : Λ₁.FG)
    (heq : Formalism.L2.Herm.hatL (F := F) Λ₁ = Formalism.L2.Herm.hatL (F := F) Λ) (v : HeightOneSpectrum (𝓞 F)) :
    GlobalTheory.AdelicU.latLoc F Λ₁ v = GlobalTheory.AdelicU.latLoc F Λ v := by
  apply le_antisymm
  · intro y hy
    exact GlobalTheory.AdelicU.latLoc_induction (fun a ha x hx => GlobalTheory.AdelicU.tmul_mem_latLoc ha (hle hx)) (zero_mem _)
      (fun _ _ h h' => add_mem h h') (fun _ h => neg_mem h) hy
  · intro y hy
    refine GlobalTheory.AdelicU.latLoc_induction (fun a ha x hx => ?_) (zero_mem _)
      (fun _ _ h h' => add_mem h h') (fun _ h => neg_mem h) hy
    have h1 : (fun i => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (x i)) ∈ Formalism.L2.Herm.hatL (F := F) Λ₁ :=
      heq ▸ Submodule.subset_span ⟨x, hx, rfl⟩
    have h2 : (fun i => (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) ⊗ₜ[F] x i) ∈ Formalism.MainNotions.StandardLattice.latHat F E (Λ₁ : Set (Fin n → E)) :=
      (GlobalTheory.LevSplit.latHat_iff Λ₁ _).2 h1
    have h3 := (GlobalTheory.AdelicU.mem_latHat_iff hfg _).1 h2 v
    have h4 : GlobalTheory.AdelicU.vecLoc v (fun i => (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) ⊗ₜ[F] x i) = fun i => (1 : Fv F v) ⊗ₜ[F] x i := by
      funext i
      simp [GlobalTheory.AdelicU.vecLoc]
    rw [h4] at h3
    have h5 := (GlobalTheory.AdelicU.latLoc F Λ₁ v).smul_mem
      ⟨a ⊗ₜ[F] ((1 : 𝓞 E) : E), GlobalTheory.AdelicU.tmul_mem_intLoc ha 1⟩ h3
    convert h5 using 1
    funext i
    show _ = (a ⊗ₜ[F] ((1 : 𝓞 E) : E)) * ((1 : Fv F v) ⊗ₜ[F] x i)
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    simp

end General

section Adelic
variable {D : D7}

theorem finE_mem_St_iff_of_fg (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (hfr : Formalism.L2.DIV.IsFrame β Λ) (hfg : Λ.FG) (g : GA D V) :
    Lev.finE V g ∈ Formalism.L2.DIV.St β ↔
      ∀ v, GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v g ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig V.gram Λ v := by
  have h1 := GlobalTheory.LevSplit.mem_St_iff β Λ hfr (Lev.finE V g)
  have h2 := GlobalTheory.LevSplit.stab_gen (GlobalTheory.LevSplit.swp D.host.F D.host.E) GlobalTheory.LevSplit.swp_bij.2 _ _
    (GlobalTheory.LevSplit.latHat_iff Λ) (finHom V g)
  have h3 := GlobalTheory.AdelicU.mem_levelOpen_iff_latHat D.sp.cm.sig V.gram hfg g
  have h4 := GlobalTheory.AdelicU.mem_levelOpen (σ := D.sp.cm.sig) (J := V.gram) (L := Λ) (g := g)
  exact h1.trans (h2.symm.trans (h3.symm.trans h4))

end Adelic

theorem finE_mem_St_iff_stabLoc : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), Formalism.L2.DIV.IsFrame β Λ → ∀ g : GA D V, Lev.finE V g ∈ Formalism.L2.DIV.St β ↔ ∀ v, GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v g ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig V.gram Λ v := by
  intro D V β Λ hfr g
  obtain ⟨Λ₁, hle, hfg, heq⟩ := exists_fg_sub hfr
  have hfr₁ : Formalism.L2.DIV.IsFrame β Λ₁ := fun x => by
    rw [heq]; exact hfr x
  rw [finE_mem_St_iff_of_fg V β Λ₁ hfr₁ hfg g]
  have hL : ∀ v, GlobalTheory.AdelicU.stabLoc D.sp.cm.sig V.gram Λ₁ v = GlobalTheory.AdelicU.stabLoc D.sp.cm.sig V.gram Λ v := fun v => by
    unfold GlobalTheory.AdelicU.stabLoc
    rw [latLoc_eq hle hfg heq v]
  simp only [hL]

end GlobalTheory.ChainOnto.LStab
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FirstOccurrenceRuleThetaChainStepBothDirections
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StepRule

theorem rulePar_of_pairPar {X : ProvA} (h3 : Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisUpDownLine X) (h4 : Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFourth X) (h5 : Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFifth X)
    {S S' : SPar} {aS aT : ℚ} (h : PairPar S S' aS aT) : RulePar X S S' aS aT := by
  have far : ∀ {t : ℕ} {al be ga de : List ℚ}, GlobalTheory.SignedHC.FarFrom aT (((t : ℚ) + 3) / 2) (signed (al ++ be) (ga ++ de) aT) →
      ¬ ∃ a, lamA al be ga de a = ((t : ℚ) + 1) / 2 := by
    rintro t al be ga de hF ⟨a, ha⟩
    have hm : (((t : ℚ) + 1) / 2, a.isLeft) ∈ GlobalTheory.SignedHC.ofIx (lamA al be ga de) :=
      Finset.mem_image.2 ⟨a, Finset.mem_univ _, by rw [ha]⟩
    rw [lamA, GlobalTheory.SignedHC.mem_ofIx_ofBlocks (by simp) (by simp)] at hm
    have : ∃ s, (((t : ℚ) + 1) / 2 + aT, s) ∈ signed (al ++ be) (ga ++ de) aT := by
      rcases hm with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact ⟨true, Finset.mem_union_left _ (List.mem_toFinset.2 (List.mem_map.2 ⟨_, h1, rfl⟩))⟩
      · exact ⟨false, Finset.mem_union_right _ (List.mem_toFinset.2 (List.mem_map.2 ⟨_, h1, rfl⟩))⟩
    have := hF _ (GlobalTheory.SignedHC.mem_entries.2 this)
    rw [add_sub_cancel_right, abs_of_nonneg (by positivity)] at this
    linarith
  have hb : ∀ t, (block t).length = t := fun t => by simp [block]
  obtain ⟨t, P, P', e, e', ⟨⟨al, be, ga, de, rfl, ⟨hd, rfl⟩ | ⟨hd, rfl⟩⟩, hF⟩ | ⟨al, be, ga, de, rfl, ⟨hd, rfl⟩ | ⟨hd, rfl⟩⟩⟩ := h
  all_goals
    have ht := hd.1.1
    have hn := hd.1.2.1
    obtain ⟨-, p1, p2, -⟩ := _root_.GlobalTheory.LowestTypes.lowest_types t al be ga de hd.1
    obtain ⟨-, p3, -⟩ := _root_.GlobalTheory.TypesMirror.types_mirror t al be ga de hd.1
  · exact ⟨_, _, _, _, _, _, _, _, by simp, by simp, by simp [hb]; omega, by simp,
      ⟨by omega, by omega, p1, p2, (h3.1 t al be ga de hd).2.1, (h3.1 t al be ga de hd).2.2,
        h5.1 t al be ga de hd (Or.inl (far hF))⟩, e, e'⟩
  · exact ⟨_, _, _, _, _, _, _, _, by simp, by simp, by simp, by simp [hb]; omega,
      ⟨by omega, by omega, p1, p3, (h3.2 t al be ga de hd).2.1, (h3.2 t al be ga de hd).2.2,
        h5.2 t al be ga de hd (Or.inl (far hF))⟩, e, e'⟩
  · have sw := GlobalTheory.T.realThetaRule_exchange_pair_members X _ _ _ _ (lamA al be ga de) (lamA' t al be ga de)
    exact ⟨_, _, _, _, _, _, _, _, by simp [hb]; omega, by simp, by simp, by simp,
      ⟨by omega, by omega, p2, p1, sw.1 (h3.1 t al be ga de hd).1, sw.2.1 (h3.1 t al be ga de hd).2.2,
        sw.2.2 (h4.1 t al be ga de hd)⟩, e, e'⟩
  · have sw := GlobalTheory.T.realThetaRule_exchange_pair_members X _ _ _ _ (lamA al be ga de) (lamM' t al be ga de)
    exact ⟨_, _, _, _, _, _, _, _, by simp, by simp [hb]; omega, by simp, by simp,
      ⟨by omega, by omega, p3, p1, sw.1 (h3.2 t al be ga de hd).1, sw.2.1 (h3.2 t al be ga de hd).2.2,
        sw.2.2 (h4.2 t al be ga de hd)⟩, e, e'⟩

theorem rulePar_step : ∀ (D : D7) (X : ProvA), Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisUpDownLine X → Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFourth X → Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFifth X →
    ∀ k : Fin D.R.m, ChainPar D k → ∀ τ, RulePar X (parB (Ptw D) k τ) (parB (Ptw D) (k + 1) τ) (expS D k τ) (expT D k τ) ∧
      RulePar X (parB (Ptw D) (k + 1) τ) (parB (Ptw D) k τ) (expT D k τ) (expS D k τ) := by
  intro D X h3 h4 h5 k hk τ
  obtain ⟨al, be, ga, de, hd, hfar, e0, e1⟩ := hk τ
  have hT : ThetaPar D.R.t (parA (Ptw D) k τ) (parA (Ptw D) (k + 1) τ) (expT D k τ) (expS D k τ) :=
    ⟨al, be, ga, de, e0, Or.inl ⟨hd, e1⟩⟩
  have hF : GlobalTheory.SignedHC.FarFrom (expT D k τ) (((D.R.t : ℚ) + 3) / 2) (parA (Ptw D) k τ) := by
    intro x hx
    obtain ⟨s, hs⟩ := GlobalTheory.SignedHC.mem_entries.1 hx
    rw [e0] at hs
    have : ∃ y ∈ al ++ be ++ ga ++ de, x = y + expT D k τ := by
      rcases Finset.mem_union.1 hs with h | h
      · obtain ⟨y, hy, hy'⟩ := List.mem_map.1 (List.mem_toFinset.1 h)
        exact ⟨y, by simp only [List.mem_append] at hy ⊢; tauto, (congrArg Prod.fst hy').symm⟩
      · obtain ⟨y, hy, hy'⟩ := List.mem_map.1 (List.mem_toFinset.1 h)
        exact ⟨y, by simp only [List.mem_append] at hy ⊢; tauto, (congrArg Prod.fst hy').symm⟩
    obtain ⟨y, hy, rfl⟩ := this
    rw [add_sub_cancel_right]
    exact hfar y hy
  exact ⟨rulePar_of_pairPar h3 h4 h5 ⟨D.R.t, _, _, rfl, rfl, Or.inl ⟨hT, hF⟩⟩,
    rulePar_of_pairPar h3 h4 h5 ⟨D.R.t, _, _, rfl, rfl, Or.inr hT⟩⟩

end GlobalTheory.StepRule

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FockSignTransposeExchangesLocalGlActions
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Chain.RealIt.SwapFock

open MvPolynomial

lemma sg_mul_self (e : Bool) : GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.sgn e * GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.sgn e = 1 := by
  cases e <;> simp [GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.sgn]

lemma conj_sg (e : Bool) : starRingEnd ℂ (GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.sgn e) = GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.sgn e := by
  cases e <;> simp [GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.sgn]

variable {a b : ℕ}

def swSign (ε : Fin a → Bool) (ε' : Fin b → Bool) (n : Fin b × Fin a) : ℂ :=
  GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.sgn (ε' n.1) * GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.sgn (ε n.2)

variable (ε : Fin a → Bool) (ε' : Fin b → Bool)

lemma swSign_mul_self (n : Fin b × Fin a) : swSign ε ε' n * swSign ε ε' n = 1 := by
  unfold swSign
  rw [mul_mul_mul_comm, sg_mul_self, sg_mul_self, one_mul]

lemma conj_swSign (n : Fin b × Fin a) : starRingEnd ℂ (swSign ε ε' n) = swSign ε ε' n := by
  unfold swSign
  rw [map_mul, conj_sg, conj_sg]

lemma swSign_swap (n : Fin b × Fin a) : swSign ε' ε n.swap = swSign ε ε' n := by
  unfold swSign
  exact mul_comm _ _

lemma C_swSign_mul_self {σ : Type*} (n : Fin b × Fin a) :
    (C (swSign ε ε' n) : MvPolynomial σ ℂ) * C (swSign ε ε' n) = 1 := by
  rw [← map_mul, swSign_mul_self, map_one]

lemma C_sg_mul_self {σ : Type*} (e : Bool) :
    (C (GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.sgn e) : MvPolynomial σ ℂ) * C (GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.sgn e) = 1 := by
  rw [← map_mul, sg_mul_self, map_one]

def swapHom : LPol b a →+* LPol a b :=
  eval₂Hom ((C : ℂ →+* LPol a b).comp (starRingEnd ℂ)) fun n => C (swSign ε ε' n) * X n.swap

@[simp] lemma swapHom_C (c : ℂ) : swapHom ε ε' (C c) = C (starRingEnd ℂ c) := by
  simp [swapHom]

@[simp] lemma swapHom_X (n : Fin b × Fin a) : swapHom ε ε' (X n) = C (swSign ε ε' n) * X n.swap := by
  simp [swapHom]

lemma swapHom_smul (c : ℂ) (P : LPol b a) : swapHom ε ε' (c • P) = starRingEnd ℂ c • swapHom ε ε' P := by
  rw [smul_eq_C_mul, map_mul, swapHom_C, smul_eq_C_mul]

lemma swapHom_comp : (swapHom ε' ε).comp (swapHom ε ε') = RingHom.id _ := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp
  · intro n
    rw [RingHom.comp_apply, swapHom_X, map_mul, swapHom_C, swapHom_X, conj_swSign, swSign_swap,
      Prod.swap_swap, ← mul_assoc, C_swSign_mul_self, one_mul, RingHom.id_apply]

lemma swapHom_pderiv (n : Fin b × Fin a) (Q : LPol b a) :
    swapHom ε ε' (pderiv n Q) = C (swSign ε ε' n) * pderiv n.swap (swapHom ε ε' Q) := by
  induction Q using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), hp, hq, map_add (f := _), map_add (f := _), mul_add]
  | mul_X p m hp =>
    have hs := C_swSign_mul_self (σ := Fin a × Fin b) ε ε' n
    by_cases h : n = m
    · subst h
      simp only [pderiv_mul, pderiv_X_self, map_add (f := _), map_mul, hp, swapHom_X, pderiv_C, mul_one, zero_mul, zero_add]
      linear_combination (-(swapHom ε ε' p)) * hs
    · have h' : m.swap ≠ n.swap := fun e => h (Prod.swap_injective e).symm
      simp only [pderiv_mul, pderiv_X_of_ne (Ne.symm h), pderiv_X_of_ne h', map_mul, hp, swapHom_X,
        pderiv_C, mul_zero, zero_mul, add_zero, zero_add]
      ring

lemma swapHom_rai (i : Fin b) (j : Fin a) (Q : LPol b a) :
    swapHom ε ε' (rai ε ε' i j Q) = rai ε' ε j i (swapHom ε ε' Q) := by
  unfold rai
  have hs := C_sg_mul_self (σ := Fin a × Fin b) (ε j)
  by_cases h : ε' i = ε j
  · rw [if_pos h, if_pos h.symm]
    simp only [LinearMap.smul_apply, LinearMap.mulLeft_apply, swapHom_smul, swapHom_C, map_mul, swapHom_X, conj_sg,
      swSign, smul_eq_C_mul, Prod.swap_prod_mk]
    linear_combination (C (GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.sgn (ε' i)) * X (j, i) * swapHom ε ε' Q) * hs
  · rw [if_neg h, if_neg (Ne.symm h)]
    simp only [LinearMap.smul_apply, LinearMap.neg_apply, Derivation.coeFn_coe, map_neg, swapHom_smul, swapHom_C,
      swapHom_pderiv, map_mul, conj_sg, swSign, smul_eq_C_mul, Prod.swap_prod_mk]
    linear_combination (-(C (GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.sgn (ε' i)) * pderiv (j, i) (swapHom ε ε' Q))) * hs

lemma swapHom_low (i : Fin b) (j : Fin a) (Q : LPol b a) :
    swapHom ε ε' (low ε ε' i j Q) = low ε' ε j i (swapHom ε ε' Q) := by
  unfold low
  have hs := C_sg_mul_self (σ := Fin a × Fin b) (ε j)
  by_cases h : ε' i = ε j
  · rw [if_pos h, if_pos h.symm]
    simp only [LinearMap.smul_apply, Derivation.coeFn_coe, swapHom_smul, swapHom_C, swapHom_pderiv, map_mul, conj_sg,
      swSign, smul_eq_C_mul, Prod.swap_prod_mk]
    linear_combination (C (GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.sgn (ε' i)) * pderiv (j, i) (swapHom ε ε' Q)) * hs
  · rw [if_neg h, if_neg (Ne.symm h)]
    simp only [LinearMap.smul_apply, LinearMap.mulLeft_apply, swapHom_smul, swapHom_C, map_mul, swapHom_X, conj_sg,
      swSign, smul_eq_C_mul, Prod.swap_prod_mk]
    linear_combination (C (GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.sgn (ε' i)) * X (j, i) * swapHom ε ε' Q) * hs

lemma swapHom_half (c : Prop) [Decidable c] (Q : LPol b a) :
    swapHom ε ε' ((if c then (1 / 2 : ℂ) • (1 : Module.End ℂ (LPol b a)) else 0) Q) =
      (if c then (1 / 2 : ℂ) • (1 : Module.End ℂ (LPol a b)) else 0) (swapHom ε ε' Q) := by
  split_ifs
  · rw [LinearMap.smul_apply, LinearMap.smul_apply, Module.End.one_apply, Module.End.one_apply, swapHom_smul]
    rw [map_div₀, map_one, map_ofNat]
  · rw [LinearMap.zero_apply, LinearMap.zero_apply, map_zero]

lemma swapHom_termT (i l : Fin b) (j : Fin a) (Q : LPol b a) :
    swapHom ε ε' ((rai ε ε' i j * low ε ε' l j + if i = l then (1 / 2 : ℂ) • 1 else 0) Q) =
      (rai ε' ε j i * low ε' ε j l + if i = l then (1 / 2 : ℂ) • 1 else 0) (swapHom ε ε' Q) := by
  rw [LinearMap.add_apply, LinearMap.add_apply, map_add (f := _), Module.End.mul_apply, Module.End.mul_apply, swapHom_rai,
    swapHom_low, swapHom_half]

lemma swapHom_termS (i : Fin b) (j k : Fin a) (Q : LPol b a) :
    swapHom ε ε' ((rai ε ε' i j * low ε ε' i k + if j = k then (1 / 2 : ℂ) • 1 else 0) Q) =
      (rai ε' ε j i * low ε' ε k i + if j = k then (1 / 2 : ℂ) • 1 else 0) (swapHom ε ε' Q) := by
  rw [LinearMap.add_apply, LinearMap.add_apply, map_add (f := _), Module.End.mul_apply, Module.End.mul_apply, swapHom_rai,
    swapHom_low, swapHom_half]

def swapEquiv : LPol b a ≃+ LPol a b :=
  { toFun := swapHom ε ε'
    invFun := swapHom ε' ε
    left_inv := fun P => RingHom.congr_fun (swapHom_comp ε ε') P
    right_inv := fun P => RingHom.congr_fun (swapHom_comp ε' ε) P
    map_add' := map_add _ }

lemma swapEquiv_apply (P : LPol b a) : swapEquiv ε ε' P = swapHom ε ε' P := rfl

theorem locS_locT_exchange : ∀ (a b : ℕ) (ε : Fin a → Bool) (ε' : Fin b → Bool), ∃ j : LPol b a ≃+ LPol a b,
    (∀ (c : ℂ) P, j (c • P) = conj c • j P) ∧ ∀ P : LPol b a,
      (∀ Y : Matrix (Fin b) (Fin b) ℂ, j (locT ε ε' Y P) = locS ε' ε (Y.map (starRingEnd ℂ)) (j P)) ∧
        ∀ X : Matrix (Fin a) (Fin a) ℂ, j (locS ε ε' (X.map (starRingEnd ℂ)) P) = locT ε' ε X (j P) := by
  intro a b ε ε'
  refine ⟨swapEquiv ε ε', fun c P => ?_, fun P => ⟨fun Y => ?_, fun X => ?_⟩⟩
  · rw [swapEquiv_apply, swapEquiv_apply, swapHom_smul]
  · rw [swapEquiv_apply, swapEquiv_apply]
    unfold locT locS
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, swapHom_smul, swapHom_termT, Matrix.map_apply]
  · rw [swapEquiv_apply, swapEquiv_apply]
    unfold locT locS
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, swapHom_smul, swapHom_termS, Matrix.map_apply,
      starRingEnd_self_apply]

end GlobalTheory.Chain.RealIt.SwapFock

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierTransformCosetIndicatorEqFiniteColumnTranStatement
section
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge GlobalTheory.SymBridge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourierTransform_cosetIndicator_eq_finiteColumnTransform : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (s : ℕ) (W : TwData k) [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → cst.Ok → AtTwist (R := R) sel mu cst σ₀ P ι s W → 2 * cst.M ≤ cst.D P →
  ∀ (e' : XIx (Fin R.k) (Fin R.t) (s + 1) ≃ Fin (R.N (s + 1))) (e : Ix (Fin R.k ⊕ Fin (s + 1)) (Fin R.t) (s + 2) ⊕ Unit ≃ Fin (R.N R.m)),
    IsOrd xPos e' → IsOrd (Sum.elim zPos fun _ => R.N R.m - 1) e →
    ∀ (y : HomE X.E (R.N (s + 1)) (R.N R.m)) (y' : Sp X.E (R.N (s + 1))), (∀ l, IntAt P.1 ((qOf P.1 : X.E) ^ cst.M * y' l)) →
      hat W.ψ ν (-1) (cosetInd (box _ (W.ϖ ^ cst.M)) (Submodule.Quotient.mk fun a => ι (y' (e' a)))) ((toLoc ι e e' y) (Sum.inr ())) =
        σ₀ (ftY sel mu cst P (atNL X.E (R.N R.m) (R.N R.m - 1) ∘ₗ y) y') := by
  first | exact @GlobalTheory.TwBridge.TopHat.hat_coset_eq_ftY | exact GlobalTheory.TwBridge.TopHat.hat_coset_eq_ftY | (intros; apply GlobalTheory.TwBridge.TopHat.hat_coset_eq_ftY <;> assumption)
end

