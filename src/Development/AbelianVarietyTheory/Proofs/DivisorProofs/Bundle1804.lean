module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1219
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsJointShapeGenerated
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0981
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0545
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0518
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1786
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1788
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1245
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1502
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1592
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomSuppSplit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1796
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1715
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1645
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1656
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1775
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1665
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1630
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1246
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1682
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1531
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1783
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1028
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
public import Formalism.GradedWeylDivisibility.FinalC
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FirstIndexEqOfUnfolded
public import Formalism.LocalToGlobal.ProjectiveLattices.UnFree

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockCoinvariantsHighestWeightCyclicMultiplicityOne
section
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

noncomputable section

namespace GlobalTheory.HoweR.Cyc

theorem coinv_eq_rel (P Q R S : ℕ) (x : ℚ) : coinv P Q R S (x : ℂ) = GlobalTheory.FockQuot.rel P Q R S x := rfl

theorem fockAct2_good (P Q R S : ℕ) : Good (fockAct2 P Q R S) :=
  ⟨(fock_lie_and_commute P Q R S).2.2.1, fun v => ((GlobalTheory.FockPolGK.pol_locFin_weights P Q R S).2 v).2,
    _root_.GlobalTheory.HoweR.fock_locU P Q R S⟩

theorem rel_stab (P Q R S : ℕ) (x : ℚ) (Y : Mat R S) (y : Pol P Q R S) (hy : y ∈ GlobalTheory.FockQuot.rel P Q R S x) :
    fockAct2 P Q R S Y y ∈ GlobalTheory.FockQuot.rel P Q R S x := by
  have h := GlobalTheory.FockQuot.fockTraceCharacterRelations_le_comap_secondAction P Q R S x 0 Y hy
  rw [Submodule.mem_comap, GlobalTheory.FockQuot.fockSecondActionTraceShift_apply] at h
  simpa using h

theorem actQ_zero_mk (P Q R S : ℕ) (x : ℚ) (Y : Mat R S) (f : Pol P Q R S) :
    GlobalTheory.FockQuot.actQ P Q R S x 0 Y (Submodule.Quotient.mk f) =
      Submodule.Quotient.mk (fockAct2 P Q R S Y f) := by
  rw [GlobalTheory.FockQuot.actQ_mk, GlobalTheory.FockQuot.fockSecondActionTraceShift_apply]; simp

theorem genSub_stable {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V)
    (T : Set V) (Z : Mat p q) (y : V) (hy : y ∈ genSub act T) : act Z y ∈ genSub act T := by
  unfold genSub at hy ⊢
  rw [Submodule.mem_sInf] at hy ⊢
  intro N hN
  exact hN.2 Z y (hy N hN)

theorem mem_genSub_self {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V)
    (v : V) : v ∈ genSub act {v} := by
  unfold genSub
  rw [Submodule.mem_sInf]
  intro N hN
  exact hN.1 rfl

theorem cycMod_rel (P Q R S : ℕ) (x : ℚ) (hne : GlobalTheory.FockQuot.rel P Q R S x ≠ ⊤) :
    CycMod (fockAct2 P Q R S) (GlobalTheory.FockQuot.rel P Q R S x) := by
  set C := GlobalTheory.FockQuot.rel P Q R S x with hC
  have hnt : Nontrivial (GlobalTheory.FockQuot.gkQ P Q R S x 0).V := by
    show Nontrivial (Pol P Q R S ⧸ C)
    exact Submodule.Quotient.nontrivial_iff.2 hne
  have hlift : IsLift x 0 (GlobalTheory.FockQuot.gkQ P Q R S x 0) C.mkQ := by
    refine ⟨Submodule.mkQ_surjective _, fun X f => GlobalTheory.FockQuot.mk_fockFirstAction_eq_trace_smul P Q R S x X f, fun Y f => ?_⟩
    show GlobalTheory.FockQuot.actQ P Q R S x 0 Y (Submodule.Quotient.mk f) = _
    rw [GlobalTheory.FockQuot.actQ_mk, GlobalTheory.FockQuot.fockSecondActionTraceShift_apply]; rfl
  obtain ⟨μ', hJ, w, ⟨hw0, hwhw⟩, hgen⟩ :=
    GlobalTheory.RealLift.GenLift.genBy_of_isLift P Q R S x 0 _ _ hlift hnt
  change w ∈ hwSub (GlobalTheory.FockQuot.actQ P Q R S x 0) _ at hwhw
  change genSub (GlobalTheory.FockQuot.actQ P Q R S x 0) {w} = ⊤ at hgen
  obtain ⟨f₁, rfl⟩ := Submodule.Quotient.mk_surjective C w
  change (Submodule.Quotient.mk f₁ : Pol P Q R S ⧸ C) ≠ 0 at hw0
  have hwhw' : (Submodule.Quotient.mk f₁ : Pol P Q R S ⧸ C) ∈
      hwSub (GlobalTheory.FockQuot.actQ P Q R S x 0) (fun c => μ' c + 0) := hwhw
  obtain ⟨hwt0, hpos0⟩ := Submodule.mem_inf.1 hwhw'
  have hwt : ∀ c, GlobalTheory.FockQuot.actQ P Q R S x 0 (Eab c c) (Submodule.Quotient.mk f₁ : Pol P Q R S ⧸ C) =
      (((μ' c + 0 : ℚ)) : ℂ) • (Submodule.Quotient.mk f₁ : Pol P Q R S ⧸ C) := fun c => by
    unfold wtSub at hwt0
    have h := (Submodule.mem_iInf _).1 hwt0 c
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at h
    simpa using h
  have hpos : ∀ c d, posC c d →
      GlobalTheory.FockQuot.actQ P Q R S x 0 (Eab c d) (Submodule.Quotient.mk f₁ : Pol P Q R S ⧸ C) = 0 := fun c d hcd => by
    have h := (Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hpos0 c) d) hcd
    exact h
  have hKC : KStable (fockAct2 P Q R S) C := fun X _ y hy => rel_stab P Q R S x X y hy
  have hKT : KStable (fockAct2 P Q R S) (⊤ : Submodule ℂ (Pol P Q R S)) := fun _ _ _ _ => Submodule.mem_top
  have h1 : ∀ c, fockAct2 P Q R S (Eab c c) f₁ - ((μ' c : ℚ) : ℂ) • f₁ ∈ C := by
    intro c
    rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub, Submodule.Quotient.mk_smul,
      ← actQ_zero_mk, hwt c]
    simp
  have h2 : ∀ c d, posC c d → fockAct2 P Q R S (Eab c d) f₁ ∈ C := by
    intro c d hcd
    rw [← Submodule.Quotient.mk_eq_zero, ← actQ_zero_mk]
    exact hpos c d hcd
  obtain ⟨v, -, hv, hfv⟩ :=
    _root_.GlobalTheory.HoweR.LiftMod.lift_mod R S (Pol P Q R S) (fockAct2 P Q R S) (fockAct2_good P Q R S) C ⊤ hKC hKT μ' f₁
      Submodule.mem_top h1 h2
  have hmk : (Submodule.Quotient.mk v : Pol P Q R S ⧸ C) = Submodule.Quotient.mk f₁ :=
    ((Submodule.Quotient.eq C).2 hfv).symm
  refine ⟨μ', v, hv, ?_, ?_⟩
  ·
    set N := genSub (fockAct2 P Q R S) {v} ⊔ C with hN
    have hNst : ∀ Z, ∀ y ∈ N, fockAct2 P Q R S Z y ∈ N := by
      intro Z y hy
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hy
      rw [map_add (f := _)]
      exact N.add_mem (Submodule.mem_sup_left (genSub_stable _ _ Z a ha))
        (Submodule.mem_sup_right (rel_stab P Q R S x Z b hb))
    have hle : genSub (GlobalTheory.FockQuot.actQ P Q R S x 0) {Submodule.Quotient.mk f₁} ≤ N.map C.mkQ := by
      refine sInf_le ⟨?_, ?_⟩
      · rw [Set.singleton_subset_iff, ← hmk]
        exact ⟨v, Submodule.mem_sup_left (mem_genSub_self _ v), rfl⟩
      · rintro Z _ ⟨n, hn, rfl⟩
        refine ⟨fockAct2 P Q R S Z n, hNst Z n hn, ?_⟩
        simp only [Submodule.mkQ_apply]
        rw [actQ_zero_mk]
    have hle2 : N.map C.mkQ = ⊤ := top_le_iff.1 (le_trans (le_of_eq hgen.symm) hle)
    rw [eq_top_iff]
    intro f _
    have hf : Submodule.Quotient.mk f ∈ N.map C.mkQ := by rw [hle2]; exact Submodule.mem_top
    obtain ⟨n, hn, hnf⟩ := hf
    have hd : n - f ∈ C := (Submodule.Quotient.eq C).1 hnf
    have : f = n - (n - f) := by abel
    rw [this]
    exact N.sub_mem hn (Submodule.mem_sup_right hd)
  ·
    obtain ⟨f₀, hf₀⟩ := _root_.GlobalTheory.HoweR.hw_le_span_sup_coinv P Q R S x μ' hJ
    rw [coinv_eq_rel] at hf₀
    obtain ⟨y, hy, c, hc, hyc⟩ := Submodule.mem_sup.1 (hf₀ hv)
    obtain ⟨z, rfl⟩ := Submodule.mem_span_singleton.1 hy
    have hz : z ≠ 0 := by
      rintro rfl
      apply hw0
      rw [← hmk, Submodule.Quotient.mk_eq_zero, ← hyc]
      simpa using hc
    have hf₀mem : f₀ ∈ Submodule.span ℂ {v} ⊔ C := by
      have : f₀ = z⁻¹ • v - z⁻¹ • c := by
        rw [← hyc, smul_add, smul_smul, inv_mul_cancel₀ hz, one_smul, add_sub_cancel_right]
      rw [this]
      exact Submodule.sub_mem _ (Submodule.mem_sup_left (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)))
        (Submodule.mem_sup_right (C.smul_mem _ hc))
    refine hf₀.trans (sup_le ?_ le_sup_right)
    rw [Submodule.span_le, Set.singleton_subset_iff]
    exact hf₀mem

end GlobalTheory.HoweR.Cyc

theorem GlobalTheory.HoweR.coinv_cycMod : ∀ (P Q R S : ℕ) (x : ℂ), CycMod (fockAct2 P Q R S) (coinv P Q R S x) := by
  intro P Q R S x
  rcases GlobalTheory.HoweR.coinv_top_or_rat P Q R S x with h | ⟨x', h⟩
  · rw [h]
    refine ⟨0, 0, Submodule.zero_mem _, by simp, by simp⟩
  · rw [h, GlobalTheory.HoweR.Cyc.coinv_eq_rel] at *
    by_cases hne : GlobalTheory.FockQuot.rel P Q R S x' = ⊤
    · rw [hne]
      exact ⟨0, 0, Submodule.zero_mem _, by simp, by simp⟩
    · exact GlobalTheory.HoweR.Cyc.cycMod_rel P Q R S x' hne
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodSplitPlaceTranslationActsThroughWeil
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

open scoped GlobalTheory.VacAny
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.LocWeilAct

theorem conjU_mul' {D : D7} (V : HSp D) {J : Matrix (Fin V.rank) (Fin V.rank) D.host.E} (c : D.host.E)
    (hc : J = c • V.gram) (a b : GA D V) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU V c hc (a * b) = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU V c hc a * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU V c hc b :=
  Subtype.ext (by simp [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU, map_mul])

theorem conjU_one' {D : D7} (V : HSp D) {J : Matrix (Fin V.rank) (Fin V.rank) D.host.E} (c : D.host.E)
    (hc : J = c • V.gram) : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU V c hc 1 = 1 :=
  Subtype.ext (by simp [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU, map_one])

theorem linear_of_acts {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))
    (T : Module.End ℂ ((κ → AF F) → ℂ)) (S : ((κ → Fv F v) → ℂ) → (κ → Fv F v) → ℂ)
    (hS : ∀ φ ∈ GlobalTheory.WeilM.SB (κ → Fv F v), S φ ∈ GlobalTheory.WeilM.SB _ ∧ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (evFin F v) T φ (S φ)) :
    ∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ φ' ∈ GlobalTheory.WeilM.SB _, ∀ c : ℂ, S (c • φ + φ') = c • S φ + S φ' := by
  intro φ hφ φ' hφ' c
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.RestWitness.exists_rest (F := F) κ v
  have hs := Submodule.add_mem _ (Submodule.smul_mem _ c hφ) hφ'
  have tl : ∀ f f' : (κ → Fv F v) → ℂ, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v) (c • f + f') R =
      c • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v) f R + GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v) f' R := by
    intro f f'; funext x; simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  have e : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v) (S (c • φ + φ')) R =
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v) (c • S φ + S φ') R := by
    rw [← (hS _ hs).2 R (hR _ hs), tl, tl, map_add (f := _), map_smul, (hS φ hφ).2 R (hR φ hφ), (hS φ' hφ').2 R (hR φ' hφ')]
  funext y
  have hx := congrFun e (fun k => GlobalTheory.LatVac.liftV v (y k))
  have hRx : R (fun k => GlobalTheory.LatVac.liftV v (y k)) = R 0 := by
    have := (hR φ hφ).1 0 (fun k => GlobalTheory.LatVac.liftV v (y k))
      (fun u hu => funext fun k => GlobalTheory.LatVac.at_liftV v (y k) u hu)
    rwa [zero_add] at this
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens, GlobalTheory.LatVac.evFin_liftV, hRx] at hx
  exact mul_right_cancel₀ hR0 hx

theorem act_omB : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (t : T) (i j : Fin D.R.m) (M : Vol G)
    (e : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Num G i j) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j)
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W)
    (h : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.IsTripleOf W M t i j e Bs Γ X) (hTr : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om'),
    ∃ ν α : (Fv D.host.F Bs.v₁)ˣ →* ℂˣ, (∀ x, ‖(ν x : ℂ)‖ = 1) ∧
      ∀ ι : ((Fin (G.V (.grid i j)).rank × Fin ((G.V (.grid (i + 1) (j + 1))).rank + (G.V (.grid i j)).rank) → Fv D.host.F Bs.v₁) → ℂ) →ₗ[ℂ]
              (Matrix (Fin (G.V (.grid i j)).rank) (Fin ((G.V (.grid (i + 1) (j + 1))).rank + (G.V (.grid i j)).rank)) (Fv D.host.F Bs.v₁) → ℂ),
      Γ.M'.IsLinBar Bs.ψ Bs.τ₁ 1 1 ι →
      ∀ g : GL (Fin (G.V (.grid i j)).rank) (Fv D.host.F Bs.v₁), ∃ k : GA D (G.V (.grid i j)),
        ∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ r, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (evFin D.host.F Bs.v₁) φ r → ∃ φ₁ ∈ GlobalTheory.WeilM.SB _,
          om' (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU _ (-1) h.JW₁ k, 1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin D.host.F Bs.v₁) φ r) =
            GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin D.host.F Bs.v₁) φ₁ r ∧ ι φ₁ = omB ν α g 1 (ι φ) := by
  intro D T L sc G W t i j M e Bs Γ X om om' h hTr
  obtain ⟨K, hK⟩ := GlobalTheory.SplitGLLift.exists_hom_supp_split W t i j M e Bs Γ X om om' h hTr
  let K' : GL (Fin (G.V (.grid i j)).rank) (Fv D.host.F Bs.v₁) →* GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA D.sp.cm.sig Γ.V'.J :=
    { toFun := fun g => GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU _ (-1) h.JW₁ (K g)
      map_one' := by simp only [map_one]; exact conjU_one' _ _ _
      map_mul' := fun g g' => by simp only [map_mul]; exact conjU_mul' _ _ _ _ _ }
  have hK' : ∀ g, K' g = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU _ (-1) h.JW₁ (K g) := fun _ => rfl
  have hB := fun g => GlobalTheory.T.weilRepresentationLocality_unitaryGroupV' Bs Γ X om om' hTr Bs.v₁ (K' g) (hK g).1
  choose S hS using hB
  have hSplit := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hTr.weil'
  have pres : ∀ p Φ, Φ ∈ GlobalTheory.WeilM.schA D.host.F _ → om' p Φ ∈ GlobalTheory.WeilM.schA D.host.F _ :=
    fun p Φ hΦ => hSplit.pres p Φ hΦ
  have restS : ∀ g φ r, φ ∈ GlobalTheory.WeilM.SB _ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (evFin D.host.F Bs.v₁) φ r →
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (evFin D.host.F Bs.v₁) (S g φ) r := fun g φ r hφ hr =>
    ⟨hr.1, by rw [← (hS g φ hφ).2 r hr]; exact pres _ _ hr.2⟩
  have h1 : ∀ g, ∀ φ ∈ GlobalTheory.WeilM.SB _, S g φ ∈ GlobalTheory.WeilM.SB _ := fun g φ hφ => (hS g φ hφ).1
  have h2 : ∀ g g', ∀ φ ∈ GlobalTheory.WeilM.SB _, S (g * g') φ = S g (S g' φ) := by
    intro g g' φ hφ
    refine GlobalTheory.TensUniq.eq_of_tens_eq Bs.v₁ φ _ _ hφ fun r hr => ?_
    have e1 : ((K' (g * g'), (1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA D.sp.cm.sig Γ.W.J))) =
        (K' g, 1) * (K' g', 1) := by rw [map_mul, Prod.mk_mul_mk, one_mul]
    rw [← (hS (g * g') φ hφ).2 r hr, e1, map_mul, Module.End.mul_apply, (hS g' φ hφ).2 r hr,
      (hS g (S g' φ) (h1 g' φ hφ)).2 r (restS g' φ r hφ hr)]
  have h3 : ∀ φ ∈ GlobalTheory.WeilM.SB _, S 1 φ = φ := by
    intro φ hφ
    refine GlobalTheory.TensUniq.eq_of_tens_eq Bs.v₁ φ _ _ hφ fun r hr => ?_
    have e1 : ((K' 1, (1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA D.sp.cm.sig Γ.W.J))) = 1 := by rw [map_one]; rfl
    rw [← (hS 1 φ hφ).2 r hr, e1, map_one, Module.End.one_apply]
  have hψ : Continuous Bs.ψ := hTr.base.std.1
  have atAct : ∀ g (γ : Matrix _ _ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := D.host.F) (E := D.host.E))),
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin D.host.F Bs.v₁) γ →
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin D.host.F Bs.v₁)
        (GlobalTheory.WeilM.actAB (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (K' g, (1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA D.sp.cm.sig Γ.W.J)) γ) := by
    intro g γ hγ u hu
    simp only [GlobalTheory.WeilM.actAB]
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, hγ u hu, Matrix.mul_zero, Matrix.zero_mul]
  have h4 : ∀ g (γ : Matrix _ _ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := D.host.F) (E := D.host.E))),
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin D.host.F Bs.v₁) γ → ∀ φ ∈ GlobalTheory.WeilM.SB _,
        S g (GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) (GlobalTheory.LatVac.locCo Γ.M'.co Bs.v₁ γ) φ) =
          GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁)
            (GlobalTheory.LatVac.locCo Γ.M'.co Bs.v₁ (GlobalTheory.WeilM.actAB (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig)
              (K' g, (1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA D.sp.cm.sig Γ.W.J)) γ)) (S g φ) := by
    intro g γ hγ φ hφ
    have hw := GlobalTheory.SchrSB.schr_mem_SB Bs.ψ hψ Bs.v₁ (GlobalTheory.LatVac.locCo Γ.M'.co Bs.v₁ γ) φ hφ
    refine GlobalTheory.TensUniq.eq_of_tens_eq Bs.v₁ φ _ _ hφ fun r hr => ?_
    have hb1 := GlobalTheory.VacBridge.rho_acts_locCo Γ.M'.co Bs.ψ Bs.v₁ γ hγ φ r hr
    have hRw : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (evFin D.host.F Bs.v₁)
        (GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) (GlobalTheory.LatVac.locCo Γ.M'.co Bs.v₁ γ) φ) r :=
      ⟨hr.1, by rw [← hb1]; exact GlobalTheory.HeisSchA.rho_mem_schA Γ.M' Bs.ψ hTr.base.std γ _ hr.2⟩
    rw [← (hS g _ hw).2 r hRw, ← hb1, hSplit.impl _ _ _ hr.2, (hS g φ hφ).2 r hr,
      GlobalTheory.VacBridge.rho_acts_locCo Γ.M'.co Bs.ψ Bs.v₁ _ (atAct g γ hγ) (S g φ) r (restS g φ r hφ hr)]
  have h5 : ∀ g, ∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ μ : @Measure (Fin (G.V (.grid i j)).rank × Fin ((G.V (.grid (i + 1) (j + 1))).rank + (G.V (.grid i j)).rank) → Fv D.host.F Bs.v₁) (borel _),
      @Measure.IsAddHaarMeasure _ _ _ (borel _) μ → ∫⁻ y, ‖S g φ y‖ₑ ^ 2 ∂μ = ∫⁻ y, ‖φ y‖ₑ ^ 2 ∂μ :=
    fun g φ hφ μ hμ => GlobalTheory.T.localWeilOperator_isometry_schwartzBruhat Bs Γ X om om' hTr Bs.v₁ (K' g) (hK g).1 φ (S g φ) hφ (h1 g φ hφ) (hS g φ hφ).2 μ hμ
  obtain ⟨ν, α, hν, hC⟩ := GlobalTheory.T.heisenbergIntertwiner_eq_twisted_weilOperator Bs Γ X om om' hTr K' (fun g => hK g) S h1
    (fun g => linear_of_acts Bs.v₁ (om' (K' g, 1)) (S g) (hS g)) h2 h3 h4 h5
  exact ⟨ν, α, hν, fun ι hι g => ⟨K g, fun φ hφ r hr =>
    ⟨S g φ, h1 g φ hφ, (hS g φ hφ).2 r hr, hC ι hι g φ hφ⟩⟩⟩

end GlobalTheory.LocWeilAct
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergInvariantFormVanishesLagrangianTestStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenberg_invariant_form_vanishes_lagrangian_test : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (v : Pl (F := F)), PsiUnr ψ v →
    ∀ (m : ℕ) (C : Matrix (Fin d) (Fin m) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))), GlobalTheory.InertVacLag.IsLagrAt σ W v C →
    ∃ φ₀ ∈ SB (Fin n × Fin d → Fv F v), ∀ l : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] ℂ,
      GlobalTheory.InertVacLag.HeisInv M ψ v C l → l φ₀ = 0 → ∀ φ ∈ SB (Fin n × Fin d → Fv F v), l φ = 0 := by
  first | exact @GlobalTheory.InertLagUniq.exists_test | exact GlobalTheory.InertLagUniq.exists_test | (intros; apply GlobalTheory.InertLagUniq.exists_test <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HighestWeightBaseChange
section
set_option autoImplicit false

noncomputable section

open MvPolynomial
open Formalism.GradedWeylDivisibility

namespace GlobalTheory.HighWt

theorem map_bidet {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {r n K : ℕ} (sz : Fin K → ℕ)
    (hsz : ∀ k, sz k ≤ n) (I : ∀ k, Fin (sz k) → Fin r) :
    MvPolynomial.map φ (bideterminant R sz hsz I) = bideterminant S sz hsz I := by
  unfold bideterminant initMinor
  rw [map_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [RingHom.map_det]
  congr 1
  ext p q
  simp [RingHom.mapMatrix_apply]

theorem baseChange_holds : BaseChange := by
  intro O _ _ _ ϖ hϖ N ν _
  have hmax : (Ideal.span {ϖ}).IsMaximal := by
    rw [← (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ]
    exact IsLocalRing.maximalIdeal.isMaximal O
  letI : Field (O ⧸ Ideal.span {ϖ}) := Ideal.Quotient.field _
  have hdom : IsDomain (O ⧸ Ideal.span {ϖ}) := Ideal.Quotient.isDomain _
  constructor
  · intro f hf
    rw [standardMonomialSpanDomain (O ⧸ Ideal.span {ϖ}) N N ν] at hf
    induction hf using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨K, sz, hsz, I, hsh, rfl⟩ := hx
      refine ⟨bideterminant O sz hsz I, ?_, map_bidet _ sz hsz I⟩
      rw [← hsh]
      exact bidetMem O N N K sz hsz I
    | zero => exact ⟨0, Submodule.zero_mem _, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha, rfl⟩ := hx
      obtain ⟨b, hb, rfl⟩ := hy
      exact ⟨a + b, Submodule.add_mem _ ha hb, by simp⟩
    | smul c x _ hx =>
      obtain ⟨a, ha, rfl⟩ := hx
      obtain ⟨c', rfl⟩ := Ideal.Quotient.mk_surjective c
      refine ⟨c' • a, Submodule.smul_mem _ c' ha, ?_⟩
      rw [smul_eq_C_mul, smul_eq_C_mul, map_mul, map_C]
  · intro g hg h0
    have hk : g ∈ RingHom.ker (MvPolynomial.map (Ideal.Quotient.mk (Ideal.span {ϖ}))) := h0
    rw [MvPolynomial.ker_map, Ideal.mk_ker, Ideal.map_span, Set.image_singleton,
      Ideal.mem_span_singleton'] at hk
    obtain ⟨h, hh⟩ := hk
    have hgh : g = ϖ • h := by rw [smul_eq_C_mul, ← hh, mul_comm]
    refine ⟨h, ?_, hgh⟩
    exact dualWeylSat O N N ν ϖ h hϖ.ne_zero (hgh ▸ hg)

end GlobalTheory.HighWt

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HoweHighestWeightSupStableLe
section
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory.HoweR

theorem isKC_Eab_of_posC {p q : ℕ} {c d : Ix p q} (h : posC c d) : IsKC (Eab c d) := by
  intro a b hab
  have hcd : sameBlock c d := by
    cases c <;> cases d <;> simp_all [posC, sameBlock]
  simp only [Eab, Matrix.single_apply]
  split_ifs with h1
  · obtain ⟨rfl, rfl⟩ := h1
    exact absurd hcd hab
  · rfl

theorem sameBlock_refl {p q : ℕ} (a : Ix p q) : sameBlock a a := by
  cases a <;> trivial

theorem isKC_Eab_diag {p q : ℕ} (c : Ix p q) : IsKC (Eab c c) := by
  intro a b hab
  simp only [Eab, Matrix.single_apply]
  split_ifs with h1
  · rcases h1 with ⟨rfl, rfl⟩
    exact absurd (sameBlock_refl _) hab
  · rfl

theorem mem_hwSub_iff {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (μ : Ix p q → ℚ) (v : V) :
    v ∈ hwSub act μ ↔ (∀ c, act (Eab c c) v = ((μ c : ℚ) : ℂ) • v) ∧ ∀ c d, posC c d → act (Eab c d) v = 0 := by
  simp [hwSub, wtSub, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, sub_eq_zero]

theorem hw_sup_le (p q : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V)
    (hG : Good act) (N N' : Submodule ℂ V) (hN : KStable act N) (hN' : KStable act N') (μ : Ix p q → ℚ) :
    (N ⊔ N') ⊓ hwSub act μ ≤ (N ⊓ hwSub act μ) ⊔ (N' ⊓ hwSub act μ) := by
  intro v hv
  obtain ⟨hvs, hvh⟩ := Submodule.mem_inf.1 hv
  obtain ⟨n, hn, n', hn', rfl⟩ := Submodule.mem_sup.1 hvs
  rw [mem_hwSub_iff] at hvh
  obtain ⟨hw, hpos⟩ := hvh
  have hI : KStable act (N ⊓ N') := fun X hX w hw' =>
    Submodule.mem_inf.2 ⟨hN X hX w (Submodule.mem_inf.1 hw').1, hN' X hX w (Submodule.mem_inf.1 hw').2⟩
  have h1 : ∀ c, act (Eab c c) n - ((μ c : ℚ) : ℂ) • n ∈ N ⊓ N' := by
    intro c
    refine Submodule.mem_inf.2 ⟨N.sub_mem (hN _ (isKC_Eab_diag c) n hn) (N.smul_mem _ hn), ?_⟩
    have e : act (Eab c c) n - ((μ c : ℚ) : ℂ) • n = -(act (Eab c c) n' - ((μ c : ℚ) : ℂ) • n') := by
      have := hw c
      rw [map_add (f := _), smul_add] at this
      rw [neg_sub, sub_eq_sub_iff_add_eq_add, this, add_comm]
    rw [e]
    exact N'.neg_mem (N'.sub_mem (hN' _ (isKC_Eab_diag c) n' hn') (N'.smul_mem _ hn'))
  have h2 : ∀ c d, posC c d → act (Eab c d) n ∈ N ⊓ N' := by
    intro c d hcd
    refine Submodule.mem_inf.2 ⟨hN _ (isKC_Eab_of_posC hcd) n hn, ?_⟩
    have e : act (Eab c d) n = -(act (Eab c d) n') := by
      have := hpos c d hcd
      rw [map_add (f := _)] at this
      exact eq_neg_of_add_eq_zero_left this
    rw [e]
    exact N'.neg_mem (hN' _ (isKC_Eab_of_posC hcd) n' hn')
  obtain ⟨n1, hn1N, hn1h, hd⟩ := _root_.GlobalTheory.HoweR.LiftMod.lift_mod p q V act hG (N ⊓ N') N hI hN μ n hn h1 h2
  have hdN' : n + n' - n1 ∈ N' := by
    have : n + n' - n1 = (n - n1) + n' := by abel
    rw [this]
    exact N'.add_mem (Submodule.mem_inf.1 hd).2 hn'
  have hvH : n + n' ∈ hwSub act μ := (mem_hwSub_iff act μ _).2 ⟨hw, hpos⟩
  have : n + n' = n1 + (n + n' - n1) := by abel
  rw [this]
  exact Submodule.add_mem_sup (Submodule.mem_inf.2 ⟨hn1N, hn1h⟩)
    (Submodule.mem_inf.2 ⟨hdN', (hwSub act μ).sub_mem hvH hn1h⟩)

end GlobalTheory.HoweR
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSelfDualTr
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.EqCovol

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def IsLevGrp {H : Host E} (l : Level H) {r : ℕ} (Y : Data E r) : Prop :=
  ∀ γ : GL (Fin r) E, γ ∈ Y.Γ ↔ IsUStab Y.Gm Y.Λ γ ∧
    (∀ x ∈ (l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) • Y.Λ, ∃ y ∈ Y.Λ,
      (γ : Matrix (Fin r) (Fin r) E).mulVec x - x = l.M • y) ∧
    (∀ x ∈ Y.Λ, ∃ y ∈ Y.Λ, (γ : Matrix (Fin r) (Fin r) E).mulVec x - x = l.A • y)

def IsSelfDualTr {r : ℕ} (Y : Data E r) : Prop :=
  ∀ x : Fin r → E, x ∈ Y.Λ ↔ ∀ y ∈ Y.Λ, ∃ n : ℤ, Algebra.trace ℚ E (-Y.ξ0 * herm Y.Gm x y) = n

end GlobalTheory.EqCovol
end
end

