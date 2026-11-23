module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1710
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1713
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1502
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1617
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1714
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1531
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1544
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1592
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1645
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallySelfDualLatticeIndicatorIsVacuum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1561
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1558
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0091
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0902
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1678
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0303
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1656
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0027
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1696
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0291
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1207
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1718
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnitaryDualGLOfTwo
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0720
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0032
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NontrivialOfIrreducible
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1582
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1717

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatPtLeClosureAndSelfDual
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.VacAny
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU GlobalTheory.WeilM
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At latAtV realAd evI)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.BigDat

namespace GlobalTheory.BigDatLat

open GlobalTheory.LatVac

variable {D : D7}

theorem smul_eq_of_at {M : Type} [AddCommGroup M] [Module (AF D.host.F) M] {v : Pl D.host.F} {z : M}
    (h : At (evFin D.host.F v) z) : liftV v (1 : Fv D.host.F v) • z = z := by
  have h1 := h (1 - liftV v 1) (by rw [map_sub, map_one, evFin_liftV, sub_self])
  rw [sub_smul, one_smul, sub_eq_zero] at h1
  exact h1.symm

theorem at_smul {M : Type} [AddCommGroup M] [Module (AF D.host.F) M] (v : Pl D.host.F) (z : M) :
    At (evFin D.host.F v) (liftV v (1 : Fv D.host.F v) • z) := fun u hu => by
  rw [smul_smul, ← smul_eq_mul u, at_liftV v 1 u hu, zero_smul]

theorem cA_smul (c : AF D.host.F) (z : AE D) : cA D (c • z) = c • cA D z :=
  map_smul (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) c z

theorem symplO_swap (S T : HSp D) (c : AF D.host.F) (x y : WO S T) : symplO S T x (c • y) = symplO S T (c • x) y := by
  have h : hO S T x (c • y) = hO S T (c • x) y := by
    unfold hO
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => ?_
    rw [Matrix.smul_apply, Matrix.smul_apply, cA_smul, mul_smul_comm, smul_mul_assoc, smul_mul_assoc, mul_smul_comm]
  unfold symplO
  rw [h]

theorem infPart_smul (v : Pl D.host.F) (z : AE D) : infPart D (liftV v (1 : Fv D.host.F v) • z) = 0 := by
  rw [Algebra.smul_def, RingHom.map_mul]
  have : infPart D (algebraMap (AF D.host.F) (AE D) (liftV v (1 : Fv D.host.F v))) = 0 := infPart_pair _ _
  rw [this, zero_mul]

theorem smul_mem {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)} (v : Pl D.host.F)
    {u : WO S T} (hu : u ∈ latO S T LS LT fun _ => True) :
    liftV v (1 : Fv D.host.F v) • u ∈ latO S T LS LT fun _ => True := by
  refine latO_induction (p := fun u => liftV v (1 : Fv D.host.F v) • u ∈ latO S T LS LT fun _ => True) ?_ ?_ ?_ ?_ hu
  · intro α hα M hM
    have h : liftV v (1 : Fv D.host.F v) • finTens α M = finTens (singleFin v 1 * α) M := by
      ext i j
      change (pairA D.host.F 0 (singleFin v 1) * pairA D.host.F 0 α) ⊗ₜ[D.host.F] M i j = _
      rw [pair_mul]
      rfl
    rw [h]
    refine finTens_mem_latO (mul_mem_intAf (fun w => ?_) hα) hM
    by_cases hw : w = v
    · subst hw
      rw [evalV_singleFin_self]
      exact one_mem _
    · rw [evalV_singleFin_ne hw]
      exact zero_mem _
  · rw [smul_zero]; exact zero_mem _
  · intro x y hx hy; rw [smul_add]; exact add_mem hx hy
  · intro x hx; rw [smul_neg]; exact neg_mem hx

theorem isHalf_smul {m n : ℕ} {ε : AE D} (c : AF D.host.F) {u : Mx D m n} (hu : IsHalf ε u) : IsHalf ε (c • u) :=
  fun i j => by rw [Matrix.smul_apply, mul_smul_comm, hu]

theorem isHalf_zero {m n : ℕ} (ε : AE D) : IsHalf ε (0 : Mx D m n) := fun _ _ => mul_zero _

section Pair

variable {S T S' T' : HSp D} {P : Type} [AddCommGroup P] [Module (AF D.host.F) P]
  (m : P ≃ₗ[AF D.host.F] WO S T × WO S' T') (v : Pl D.host.F) (Λ : AddSubgroup P)

theorem le_of_gen {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}
    {LS' : Set (Fin S'.rank → D.host.E)} {LT' : Set (Fin T'.rank → D.host.E)}
    (hΛ : ∀ u, u ∈ Λ ↔ At (evFin D.host.F v) u ∧ (m u).1 ∈ latO S T LS LT (fun _ => True) ∧
      (m u).2 ∈ latO S' T' LS' LT' fun _ => True) (H : AddSubgroup P) (h2 : ∀ u ∈ Λ, 2 • u ∈ H)
    (hh : ∀ ε, IsSplitIdem D ε → ∀ u ∈ Λ, IsHalf ε (m u).1 → IsHalf ε (m u).2 → u ∈ H) : Λ ≤ H := by
  let f : WO S T × WO S' T' →ₗ[AF D.host.F] P := liftV v (1 : Fv D.host.F v) • m.symm.toLinearMap
  have hf : ∀ x, f x = liftV v (1 : Fv D.host.F v) • m.symm x := fun _ => rfl
  have hm : ∀ x, m (f x) = liftV v (1 : Fv D.host.F v) • x := fun x => by rw [hf, map_smul, m.apply_symm_apply]
  have hin : ∀ x : WO S T × WO S' T', x.1 ∈ latO S T LS LT (fun _ => True) →
      x.2 ∈ latO S' T' LS' LT' (fun _ => True) → f x ∈ Λ := fun x h1 h2 =>
    (hΛ _).2 ⟨at_smul v _, by rw [hm]; exact smul_mem v h1, by rw [hm]; exact smul_mem v h2⟩
  intro u hu
  obtain ⟨ha, h1, h1'⟩ := (hΛ u).1 hu
  have e : u = f ((m u).1, 0) + f (0, (m u).2) := by
    rw [← map_add (f := _), Prod.mk_add_mk, add_zero, zero_add, hf, Prod.mk.eta, m.symm_apply_apply, smul_eq_of_at ha]
  rw [e]
  refine add_mem ?_ ?_
  · refine le_of_two_of_half (H.comap (f ∘ₗ LinearMap.inl _ _ _).toAddMonoidHom) (fun x hx => ?_) (fun ε hε x hx hx' => ?_) h1
    · rw [AddSubgroup.mem_comap, map_nsmul]
      exact h2 _ (hin (x, 0) hx (zero_mem _))
    · exact hh ε hε (f (x, 0)) (hin (x, 0) hx (zero_mem _)) (by rw [hm]; exact isHalf_smul _ hx')
        (by rw [hm]; exact isHalf_smul _ (isHalf_zero ε))
  · refine le_of_two_of_half (H.comap (f ∘ₗ LinearMap.inr _ _ _).toAddMonoidHom) (fun x hx => ?_) (fun ε hε x hx hx' => ?_) h1'
    · rw [AddSubgroup.mem_comap, map_nsmul]
      exact h2 _ (hin (0, x) (zero_mem _) hx)
    · exact hh ε hε (f (0, x)) (hin (0, x) (zero_mem _) hx) (by rw [hm]; exact isHalf_smul _ (isHalf_zero ε))
        (by rw [hm]; exact isHalf_smul _ hx')

theorem mem_iff_char {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    {ΛS' : Submodule (𝓞 D.host.E) (Fin S'.rank → D.host.E)} {ΛT' : Submodule (𝓞 D.host.E) (Fin T'.rank → D.host.E)}
    (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) (hS' : IsSelfDualC S' ΛS') (hT' : IsSelfDualC T' ΛT')
    (hΛ : ∀ u, u ∈ Λ ↔ At (evFin D.host.F v) u ∧ (m u).1 ∈ latO S T ΛS ΛT (fun _ => True) ∧
      (m u).2 ∈ latO S' T' ΛS' ΛT' fun _ => True) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1))
    (B : P → P → AF D.host.F) (hB : ∀ x y, B x y = symplO S T (m x).1 (m y).1 + symplO S' T' (m x).2 (m y).2)
    {z : P} (hz : At (evFin D.host.F v) z) : z ∈ Λ ↔ ∀ γ ∈ Λ, ψ (B z γ) = 1 := by
  constructor
  · intro h γ hγ
    obtain ⟨-, a, b⟩ := (hΛ z).1 h
    obtain ⟨-, a', b'⟩ := (hΛ γ).1 hγ
    rw [hB, AddChar.map_add_eq_mul, char_sympl_eq_one hψ hS hT a a', char_sympl_eq_one hψ hS' hT' b b', one_mul]
  · intro h
    have hm : ∀ x, m (liftV v (1 : Fv D.host.F v) • m.symm x) = liftV v (1 : Fv D.host.F v) • x := fun x => by
      rw [map_smul, m.apply_symm_apply]
    have hz' : liftV v (1 : Fv D.host.F v) • m z = m z := by rw [← map_smul, smul_eq_of_at hz]
    have hz1 : liftV v (1 : Fv D.host.F v) • (m z).1 = (m z).1 := congrArg Prod.fst hz'
    have hz2 : liftV v (1 : Fv D.host.F v) • (m z).2 = (m z).2 := congrArg Prod.snd hz'
    have key : ∀ x : WO S T × WO S' T', x.1 ∈ latO S T ΛS ΛT (fun _ => True) →
        x.2 ∈ latO S' T' ΛS' ΛT' (fun _ => True) → ψ (symplO S T (m z).1 x.1 + symplO S' T' (m z).2 x.2) = 1 := fun x h1 h2 => by
      have := h _ ((hΛ (liftV v (1 : Fv D.host.F v) • m.symm x)).2
        ⟨at_smul v _, by rw [hm]; exact smul_mem v h1, by rw [hm]; exact smul_mem v h2⟩)
      rwa [hB, hm, Prod.smul_fst, Prod.smul_snd, symplO_swap, symplO_swap, hz1, hz2] at this
    refine (hΛ z).2 ⟨hz, mem_of_char hψ hS hT ?_ fun x hx => ?_, mem_of_char hψ hS' hT' ?_ fun x hx => ?_⟩
    · rw [← hz1]
      exact Matrix.ext fun _ _ => infPart_smul v _
    · have h0 : symplO S' T' (m z).2 0 = 0 := (symplHom S' T' (m z).2).map_zero
      have := key (x, 0) hx (zero_mem _)
      rwa [h0, add_zero] at this
    · rw [← hz2]
      exact Matrix.ext fun _ _ => infPart_smul v _
    · have h0 : symplO S T (m z).1 0 = 0 := (symplHom S T (m z).1).map_zero
      have := key (0, x) (zero_mem _) hx
      rwa [h0, zero_add] at this

end Pair

theorem latPt_le_closure_and_selfDual : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ (W : G.Weil) (i j : Fin D.R.m) (e : Num G i j) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j),
    Γ.V.J = (1 : D.host.E) • (spW G i j).gram → Γ.W.J = skewGram (spV G i j) (spV₁ G i j) e → ∀ v : Pl D.host.F, latPt e v ≤ AddSubgroup.closure (genPt e v) ∧
      ∀ z : Pt G i j, At (evFin D.host.F v) z → (z ∈ latPt e v ↔ ∀ γ ∈ latPt e v, W.ψ (sympPt Γ z γ) = 1) := by
  intro D T L sc G μ₀ hL W i j e Γ hW hWW v
  have a := (node_isV G hL (X := .grid (i + 1) (j + 1)) ⟨i.2, j.2⟩).sd
  refine ⟨le_of_gen (maps e) v _ (fun _ => Iff.rfl) _ (fun u hu => AddSubgroup.subset_closure (Or.inl ⟨u, hu, rfl⟩))
    fun ε hε u hu h1 h2 => AddSubgroup.subset_closure (Or.inr ⟨hu, ε, hε, h1, h2⟩), fun z hz => ?_⟩
  exact mem_iff_char (maps e) v _ (isSelfDualC_neg a) (node_isV G hL (X := .grid i (j + 1)) ⟨i.2.le, j.2⟩).sd
    (node_isV G hL (X := .grid (i + 1) j) ⟨i.2, j.2.le⟩).sd a (fun _ => Iff.rfl) W.ψ_std (sympPt Γ) (symp_eq e Γ hW hWW) hz

end GlobalTheory.BigDatLat

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearModelHeisenbergOperatorsTranslationCharStatement
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

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearModel_heisenbergOperators_translation_char : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V' Γ.W), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om' →
    ∀ (K : GL (Fin a') (Fv F Bs.v₁) →* GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ Γ.V'.J),
    (∀ g, K g ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ Γ.V' (evFin F Bs.v₁) ∧
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (K g)).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW Bs.τ₁) = g.val ∧
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (K g)).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW (Bs.τ₁.comp σ)) =
        (Γ.V'.J.map Bs.τ₁)⁻¹ * ((g⁻¹ : GL _ _).val)ᵀ * Γ.V'.J.map Bs.τ₁) →
    ∀ (S : GL (Fin a') (Fv F Bs.v₁) → ((Fin a' × Fin (a + a') → Fv F Bs.v₁) → ℂ) → (Fin a' × Fin (a + a') → Fv F Bs.v₁) → ℂ),
    (∀ g, ∀ φ ∈ GlobalTheory.WeilM.SB _, S g φ ∈ GlobalTheory.WeilM.SB _) →
    (∀ g (γ : Matrix (Fin a') (Fin (a + a')) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F Bs.v₁) γ →
      ∀ φ ∈ GlobalTheory.WeilM.SB _,
        S g (GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) (GlobalTheory.LatVac.locCo Γ.M'.co Bs.v₁ γ) φ) =
          GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁)
            (GlobalTheory.LatVac.locCo Γ.M'.co Bs.v₁ (GlobalTheory.WeilM.actAB (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (K g, (1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ Γ.W.J)) γ)) (S g φ)) →
    Continuous (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) ∧ GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁ ≠ 1 ∧
    ∃ (wT : Matrix (Fin a') (Fin (a + a')) (Fv F Bs.v₁) → (Fin a' × Fin (a + a') → Fv F Bs.v₁) × (Fin a' × Fin (a + a') → Fv F Bs.v₁))
      (wM : (Matrix (Fin a') (Fin (a + a')) (Fv F Bs.v₁) →ₗ[Fv F Bs.v₁] Fv F Bs.v₁) → (Fin a' × Fin (a + a') → Fv F Bs.v₁) × (Fin a' × Fin (a + a') → Fv F Bs.v₁)),
    ∀ ι, Γ.M'.IsLinBar Bs.ψ Bs.τ₁ 1 1 ι →
      (∀ C, ∀ φ ∈ GlobalTheory.WeilM.SB _, ι (GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) (wT C) φ) = fun Y => ι φ (Y + C)) ∧
      (∀ l, ∀ φ ∈ GlobalTheory.WeilM.SB _, ι (GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) (wM l) φ) = fun Y => GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁ (l Y) * ι φ Y) ∧
      (∀ g C, ∀ φ ∈ GlobalTheory.WeilM.SB _, ι (S g (GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) (wT C) φ)) =
        fun Y => ι (S g φ) (Y + ((g⁻¹ : GL (Fin a') (Fv F Bs.v₁)).val)ᵀ * C)) ∧
      (∀ g l, ∀ φ ∈ GlobalTheory.WeilM.SB _, ι (S g (GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) (wM l) φ)) =
        fun Y => GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁ (l (g.valᵀ * Y)) * ι (S g φ) Y) := by
  first | exact @GlobalTheory.LinBarOps.heis_ops | exact GlobalTheory.LinBarOps.heis_ops | (intros; apply GlobalTheory.LinBarOps.heis_ops <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalLatticeHermitianSkewStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped GlobalTheory.VacAny

noncomputable section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_lattice_hermitian_skew : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E},
    IsCMExt F E σ → ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (t : E →ₐ[F] Fv F v) {n d : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (K : Matrix (Fin d) (Fin d) E), (∀ i j, σ (J j i) = J i j) → (∀ i j, σ (K j i) = -K i j) →
    ∀ (x u : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) x →
    GlobalTheory.AdelicU.evFin F v (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (-1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F K) x u) =
      ∑ i, ∑ j, (x.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW t)) i j * (-(J.map t * u.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW (t.comp σ)) * (K.map t)ᵀ)) i j -
        ∑ i, ∑ j, (-(J.map t * x.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW (t.comp σ)) * (K.map t)ᵀ)) i j * (u.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW t)) i j := by
  first | exact @GlobalTheory.SplitTraceForm.splitTrace | exact GlobalTheory.SplitTraceForm.splitTrace | (intros; apply GlobalTheory.SplitTraceForm.splitTrace <;> assumption)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowestTypeEqualityOfEvaluationVector
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)

set_option autoImplicit false

noncomputable section

open Classical

namespace GlobalTheory.EvalLowType

theorem zero_of_span {ι : Type} [Fintype ι] [DecidableEq ι] {L : ι → Type} [∀ j, AddCommGroup (L j)] [∀ j, Module ℂ (L j)]
    {X : Type} [AddCommGroup X] [Module ℂ X] (F : (∀ j, L j) →ₘₗ[ℂ] X) (v₀ : ∀ j, L j) (P : ∀ j, L j → Prop)
    (hspan : ∀ j, Submodule.span ℂ {u | P j u} = ⊤)
    (hstep : ∀ (v : ∀ j, L j) (j : ι) (u : L j), v j = v₀ j → P j u → F v = 0 → F (Function.update v j u) = 0)
    (h0 : F v₀ = 0) : ∀ v, F v = 0 := by
  have key : ∀ s : Finset ι, ∀ v : ∀ j, L j, (∀ j ∉ s, v j = v₀ j) → F v = 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro v hv
      have : v = v₀ := funext fun j => hv j (Finset.notMem_empty j)
      rw [this]; exact h0
    | insert a s ha ih =>
      intro v hv
      have h1 : F (Function.update v a (v₀ a)) = 0 := ih _ fun j hj => by
        by_cases hja : j = a
        · subst hja; simp
        · rw [Function.update_of_ne hja]; exact hv j (by simp [hja, hj])
      have hmem : v a ∈ Submodule.span ℂ {u | P a u} := by rw [hspan a]; trivial
      have hall : ∀ u ∈ Submodule.span ℂ {u | P a u},
          F (Function.update (Function.update v a (v₀ a)) a u) = 0 := by
        intro u hu
        induction hu using Submodule.span_induction with
        | mem u hu => exact hstep _ a u (by simp) hu h1
        | zero => exact F.map_update_zero _ _
        | add x y _ _ hx hy => rw [F.map_update_add, hx, hy, add_zero]
        | smul c x _ hx => rw [F.map_update_smul, hx, smul_zero]
      have e : Function.update (Function.update v a (v₀ a)) a (v a) = v := by simp
      rw [← e]; exact hall _ hmem
  exact fun v => key Finset.univ v (fun j hj => absurd (Finset.mem_univ j) hj)

theorem adForm_lowT_equiv : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.models_HW → ∀ (i : Fin D.R.m) (x : Fin (R.nW i) → D.what₂.LL) (τ : D.what₂.Tau) (k : Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ), k ∈ Formalism.REAL.Kset ((R.MW i (sg0 D A)).ε τ) → ∀ (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (u : lowT (R.MW i (sg0 D A)) τ), ((u : (R.MW i (sg0 D A)).sm τ) : (R.MW i (sg0 D A)).H τ) = (R.MW i (sg0 D A)).σ τ k ((v τ : (R.MW i (sg0 D A)).sm τ) : (R.MW i (sg0 D A)).H τ) → adForm R i x (fun ρ => (Function.update v τ u ρ : (R.MW i (sg0 D A)).sm ρ)) = Formalism.L2.Theta.rTr (Wc D i) (atTau R.θ (Wc D i) τ (((R.MW i (sg0 D A)).fr τ)⁻¹ * k * (R.MW i (sg0 D A)).fr τ)) (adForm R i x (fun ρ => (v ρ : (R.MW i (sg0 D A)).sm ρ))) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R hHW i x τ k hk v u hu
  have hmem : adForm R i x ∈ R.Wall i (sg0 D A) := by
    rw [← (hHW i (sg0 D A)).2.1]
    exact LinearMap.mem_range_self _ _
  have hfr : IsUnit ((R.MW i (sg0 D A)).fr τ).det := (Matrix.isUnit_iff_isUnit_det _).1 ((R.MW i (sg0 D A)).fr_unit τ)
  have e1 : (R.MW i (sg0 D A)).fr τ * ((R.MW i (sg0 D A)).fr τ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hfr
  have e2 : ((R.MW i (sg0 D A)).fr τ)⁻¹ * (R.MW i (sg0 D A)).fr τ = 1 := Matrix.nonsing_inv_mul _ hfr
  have hkJ : kᴴ * Formalism.REAL.Jm ((R.MW i (sg0 D A)).ε τ) * k = Formalism.REAL.Jm ((R.MW i (sg0 D A)).ε τ) := by
    have hu1 : kᴴ * k = 1 := (Matrix.mem_unitaryGroup_iff').1 hk.1
    rw [Matrix.mul_assoc, ← hk.2, ← Matrix.mul_assoc, hu1, Matrix.one_mul]
  have hg : ((R.MW i (sg0 D A)).fr τ)⁻¹ * k * (R.MW i (sg0 D A)).fr τ ∈ Formalism.QuantumDeterminants.UH (gramAt D (Wc D i) τ) := by
    show _ = _
    rw [← (R.MW i (sg0 D A)).fr_gram τ]
    have e3 : (((R.MW i (sg0 D A)).fr τ)⁻¹)ᴴ * ((R.MW i (sg0 D A)).fr τ)ᴴ = 1 := by
      rw [← Matrix.conjTranspose_mul, e1, Matrix.conjTranspose_one]
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (((R.MW i (sg0 D A)).fr τ)⁻¹)ᴴ, e3, Matrix.one_mul,
      ← Matrix.mul_assoc ((R.MW i (sg0 D A)).fr τ) (((R.MW i (sg0 D A)).fr τ)⁻¹), e1, Matrix.one_mul]
    rw [← Matrix.mul_assoc kᴴ, ← Matrix.mul_assoc (kᴴ * _), hkJ]
  have hrep : (R.MW i (sg0 D A)).rep τ (((R.MW i (sg0 D A)).fr τ)⁻¹ * k * (R.MW i (sg0 D A)).fr τ) =
      (R.MW i (sg0 D A)).σ τ k := by
    unfold Formalism.IndefR.Mult.DSModel.rep
    congr 1
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, e1, Matrix.one_mul, Matrix.mul_assoc, e1, Matrix.mul_one]
  have hupd : (fun ρ => (Function.update v τ u ρ : (R.MW i (sg0 D A)).sm ρ)) =
      Function.update (fun ρ => (v ρ : (R.MW i (sg0 D A)).sm ρ)) τ (u : (R.MW i (sg0 D A)).sm τ) := by
    funext ρ
    by_cases hρ : ρ = τ
    · subst hρ; simp
    · simp [Function.update_of_ne hρ]
  rw [hupd]
  suffices H : ∀ T ∈ R.Wall i (sg0 D A), T (Function.update (fun ρ => (v ρ : (R.MW i (sg0 D A)).sm ρ)) τ (u : (R.MW i (sg0 D A)).sm τ)) =
      Formalism.L2.Theta.rTr (Wc D i) (atTau R.θ (Wc D i) τ (((R.MW i (sg0 D A)).fr τ)⁻¹ * k * (R.MW i (sg0 D A)).fr τ))
        (T (fun ρ => (v ρ : (R.MW i (sg0 D A)).sm ρ))) from H _ hmem
  intro T0 hT0
  induction hT0 using Submodule.span_induction with
  | mem T hT =>
    exact hT.equiv τ _ hg _ _ (by rw [hrep]; exact hu)
  | zero => rfl
  | add S T _ _ hS hT =>
    simp only [MultilinearMap.add_apply, hS, hT]
    rfl
  | smul a T _ hT =>
    simp only [MultilinearMap.smul_apply, hT]
    rfl

end GlobalTheory.EvalLowType

theorem GlobalTheory.EvalLowType.lowType_of_eval : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : Full D) [Algebra T.J.Q.c.F D.what₂.LL] (R : RealDat D A T.J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie T.J R κ v₀) (O : ∀ i, OMDat T.J.toCore R i Unit (fun _ => A.μ0)) (hT : LawsFull T), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), OMPins T.J R κ v₀ O i → R.LUnif → IoExt R → OneMapRow0 T.J R κ v₀ O i → PhaseTie T.J R κ v₀ O (fun _ => 1) i → GlobalTheory.OneMapAll.ClassSumsSpan (O i) (κ i) → ∀ (v : HeightOneSpectrum (𝓞 D.what₂.LL)), v ∈ R.twPl → R.tup_mu_on → QGuard R → GlobalTheory.FinalJoin2.FieldOK0 D (ownAt D v) → Formalism.L2.Host.ValLL0 D R.C → (∀ x, (((R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)).1 x : ℂˣ) : ℂ) ∈ D.what₂.embLL.range) → T.J.Q.l.Mb = ∏ PP ∈ R.Pg, PP.asIdeal → RunPin (T := T) R i (κ i).n v (ownAt D v) → ∀ (ℓ : G → (LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l)), LevelPin (T := T) R i ℓ → ActionPin (T := T) (R := R) hT.p fw i ℓ → ∀ (U : Subgroup G) χ ξR ω φ, KerDat R i (R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)) χ ξR (placesOver R (R.mu v) (ownAt D v)) ω φ → ∀ (Λ : GenLat D.host.E (Vc D i).rank) (h : GA D (Vc D i)), SplitOffBad (Vc D i) (badN D * (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M) h → (∀ w, w ∈ Λ.La ↔ (fun b => star (w b)) ∈ Bridge.hLat (Vc D i) (fin (Vc D i) h)) → ∀ (N : ℕ) (x₀ : Fin (Vc D i).rank → (T.Q.Dw ((i : ℕ) + 1)).La) (P : MvPolynomial (LtN (T.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank) T.Q.c.F) (x : U → Fin (Vc D i).rank → (T.Q.Dw ((i : ℕ) + 1)).La) (f : U → (recB hT.p.toLawsCore).Cusp ((i : ℕ) + 1) (κ i)) (y : VsV D i (O i).c'.F), Λ.Unimod → Λ.TrivAt (badN D) → Λ.TrivAt (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → Λ.LevOK N (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → AdmX (l := T.Q.l) true x₀ → P ∈ harmL (Dw := T.Q.Dw ((i : ℕ) + 1)) T.Q.c Λ (wtA (κ i)) → (∀ u : U, IsRightMul (ℓ u) x₀ (x u) ∧ AdmX (l := T.Q.l) true (x u) ∧ IsShortRule (T.Q.Xo ((i : ℕ) + 1)) T.Q.c (T.dδ ((i : ℕ) + 1) (Vc D i).rank) Λ N (x u) P ((f u).1 : T.R ((i : ℕ) + 1))) → (O i).io y = MvPolynomial.map (incF T.J.toCore.Q.c (O i).c' (O i).hle) P → ∀ (y₀ : ∀ PP : Pl D.host.E, Matrix (Fin (Vc D i).rank) (Fin (Wc D i).rank) (kP PP)) (c : D.what₂.LL), (∀ PP ∈ R.Pg, (y₀ PP).rank = (Wc D i).rank) → ∀ φ', VecOf R i (placesOver R (R.mu v) (ownAt D v)) (omegaFree R i (placesOver R (R.mu v) (ownAt D v)) ξR y₀) φ' → ∀ u : U, (∀ w₀ : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ, (∀ ρ, ((w₀ ρ : (R.MW i (sg0 D A)).sm ρ)) = v₀ i (sg0 D A) ρ) → adForm R i (cuspTo hT.p fw i (f u)) (fun ρ => w₀ ρ) = D.what₂.embLL c • actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG ((u : G)⁻¹)) (singleSeries R i ω φ' h ((O i).c0' y) w₀)) → ∀ w : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ, adForm R i (cuspTo hT.p fw i (f u)) (fun ρ => w ρ) = D.what₂.embLL c • actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG ((u : G)⁻¹)) (singleSeries R i ω φ' h ((O i).c0' y) w) := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ fw O hT hcore i _ _ _ _ _ _ v _ _ _ _ _ _ _ _ ℓ _ _ U χ ξR ω φ hker Λ h _ _ N x₀ P x f y _ _ _ _ _ _ _ _ y₀ c _ φ' hvec u hu
  have hext : IsExtVec (R.MW i (sg0 D A)) (v₀ i (sg0 D A)) := (fw.hv₀ i (sg0 D A)).1
  have hs0 : sg0 D A = D.what₂.embLL := sgAt_mk _ R.hv0
  have hσ : GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.OverK (sg0 D A) :=
    fun x _ => congrArg (fun s : D.what₂.LL →+* ℂ => s (D.embE x)) hs0
  let w₀ : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ := fun ρ => ⟨v₀ i (sg0 D A) ρ, (hext ρ).2.1⟩
  let Lin : LowT (R.MW i (sg0 D A)) →ₗ[ℂ] (GA D (Wc D i) → ℂ) :=
    { toFun := fun t g => Datum.thetaKO ω h g (Datum.pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1)
        (cart (R.MW i (sg0 D A))) (R.BV i) (onb (R.MW i (sg0 D A))) φ' (R.ioP i t ((O i).c0' y)))
      map_add' := fun a b => by funext g; simp [Datum.thetaKO, map_add (f := _)]
      map_smul' := fun a b => by funext g; simp [Datum.thetaKO, map_smul] }
  let act := Formalism.IndefR.Links.actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG ((u : G)⁻¹))
  let Rt : (∀ ρ, lowT (R.MW i (sg0 D A)) ρ) →ₘₗ[ℂ] (GA D (Wc D i) → ℂ) :=
    (D.what₂.embLL c • (act ∘ₗ Lin)).compMultilinearMap (PiTensorProduct.tprod ℂ)
  let Lf : (∀ ρ, lowT (R.MW i (sg0 D A)) ρ) →ₘₗ[ℂ] (GA D (Wc D i) → ℂ) :=
    (adForm R i (cuspTo hT.p fw i (f u))).compLinearMap fun ρ => (lowT (R.MW i (sg0 D A)) ρ).subtype
  have hRt : ∀ w, Rt w = D.what₂.embLL c • act (singleSeries R i ω φ' h ((O i).c0' y) w) := fun w => rfl
  have hLf : ∀ w, Lf w = adForm R i (cuspTo hT.p fw i (f u)) (fun ρ => (w ρ : (R.MW i (sg0 D A)).sm ρ)) := fun w => rfl
  have hrs : ∀ (g : GA D (Wc D i)) (a b : GA D (Wc D i) → ℂ) (s : ℂ),
      Formalism.L2.Theta.rTr (Wc D i) g a - s • Formalism.L2.Theta.rTr (Wc D i) g b = Formalism.L2.Theta.rTr (Wc D i) g (a - s • b) :=
    fun _ _ _ _ => rfl
  have key := GlobalTheory.EvalLowType.zero_of_span (Lf - Rt) w₀
    (fun ρ z => ∃ k ∈ Formalism.REAL.Kset ((R.MW i (sg0 D A)).ε ρ),
      ((z : (R.MW i (sg0 D A)).sm ρ) : (R.MW i (sg0 D A)).H ρ) = (R.MW i (sg0 D A)).σ ρ k ((v₀ i (sg0 D A) ρ : (R.MW i (sg0 D A)).sm ρ) : (R.MW i (sg0 D A)).H ρ))
    (fun ρ => GlobalTheory.LowSpan.span_translates_eq_top _ _ hext ρ
      ((GlobalTheory.HolLowOnce.lowSm_and_lowIrr D _ _ _ (GlobalTheory.GalLift.ProjLift.holShape_of_overK R i hσ)).2 ρ))
    (fun w ρ z hw ⟨k, hk, hu'⟩ h0 => by
      have hu2 : ((z : (R.MW i (sg0 D A)).sm ρ) : (R.MW i (sg0 D A)).H ρ) = (R.MW i (sg0 D A)).σ ρ k ((w ρ : (R.MW i (sg0 D A)).sm ρ) : (R.MW i (sg0 D A)).H ρ) := by
        rw [hu', hw]
      have e1 := GlobalTheory.EvalLowType.adForm_lowT_equiv R hcore.models.HW i (cuspTo hT.p fw i (f u)) ρ k hk w z hu2
      have e2 := _root_.GlobalTheory.SeriesKEquiv.singleSeries_kEquiv R F hcore i _ χ ξR _ ω φ hker _ _ φ' hvec h ((O i).c0' y) ((u : G)⁻¹) ρ k hk w z hu2
      rw [MultilinearMap.sub_apply, hLf, hRt, e1, e2]
      change Formalism.L2.Theta.rTr (Wc D i) _ (Lf w) - D.what₂.embLL c • Formalism.L2.Theta.rTr (Wc D i) _ (act _) = 0
      rw [hrs, ← hRt, ← MultilinearMap.sub_apply, h0]
      rfl)
    (by
      rw [MultilinearMap.sub_apply, sub_eq_zero, hLf, hRt]
      exact hu w₀ fun ρ => rfl)
  intro w
  have := key w
  rw [MultilinearMap.sub_apply, sub_eq_zero, hLf, hRt] at this
  exact this
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialOfIsSubquotient
section
open GlobalTheory.SmGL

noncomputable section

namespace GlobalTheory.TypeTwo.PowIrrProof

theorem equiv_of_isSubquotient {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] {σ : Representation ℂ G W} {ρ : Representation ℂ G V} (h : IsSubquotient σ ρ) [Nontrivial W]
    (hρ : ρ.IsIrreducible) : Nonempty (ρ.Equiv σ) := by
  obtain ⟨S, f, hf⟩ := h
  obtain ⟨y, hy⟩ := exists_ne (0 : W)
  letI : ρ.IsIrreducible := hρ
  rcases eq_bot_or_eq_top S with rfl | rfl
  · obtain ⟨v, rfl⟩ := hf y
    have hv : v = 0 := Subtype.ext ((Submodule.mem_bot ℂ).1 v.property)
    exact (hy (by rw [hv, map_zero])).elim
  · let e := (topEquiv ρ).symm
    let F : ρ.IntertwiningMap σ := f.comp e.toIntertwiningMap
    have hs : Function.Surjective F := hf.comp e.toLinearEquiv.surjective
    have hi : Function.Injective F :=
      (Representation.IsIrreducible.injective_or_eq_zero F).resolve_right fun hF => by
        obtain ⟨x, hx⟩ := hs y
        exact hy (by simpa [hF] using hx.symm)
    exact ⟨F.ofBijective ⟨hi, hs⟩⟩

theorem nontrivial_of_isSubquotient {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] {σ : Representation ℂ G W} {ρ : Representation ℂ G V} (h : IsSubquotient σ ρ) [Nontrivial W] :
    Nontrivial V := by
  obtain ⟨S, f, hf⟩ := h
  letI : Nontrivial S.toSubmodule := hf.nontrivial
  exact Subtype.val_injective.nontrivial (α := S.toSubmodule)

end GlobalTheory.TypeTwo.PowIrrProof
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerPreservesSchwartz
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeylFour
open scoped GlobalTheory.VacAny

namespace GlobalTheory.WeylFour.SchrKeep

theorem schr_mem_schA : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ]
    (w : (κ → AF F) × (κ → AF F)), ∀ Φ ∈ schA F κ, schr ψ w Φ ∈ schA F κ := by
  intro F _ _ ψ hψ κ _ w Φ hΦ
  exact GlobalTheory.ConeMeasV.schr_mem_schA hψ w hΦ

end GlobalTheory.WeylFour.SchrKeep
end

