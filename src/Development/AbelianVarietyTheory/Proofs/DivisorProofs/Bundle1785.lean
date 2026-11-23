module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0358
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0001
public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1243
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1782
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1749
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1643
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1502
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1617
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1660
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1682
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1674
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
public import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.SmallUnipotentElements
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1773
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1767
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1592
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1656
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1662
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1766
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0801
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0631
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaussianDatumFlippedFiniteTensorBigRoute
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsINeZeroKind
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerContentDetPowDependsOnPIK
section
open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.RefSum
open GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes (IsIntHom IsOrbit FrobOnType embX primeBelow SplitInK InertInK)
open GlobalTheory.IndefiniteRowSideFullHecke.BigBlockCharacters (HasChars)
open GlobalTheory.IndefiniteRowSideFullHecke.FactorDepthInertBounds (boundAll boundInert boundFine)

namespace GlobalTheory.DetPowContent

open GlobalTheory.DetPowShape

noncomputable def intCoeff (i k : ℕ) (α : (Σ _ : Fin i, Fin i) →₀ ℕ) : ℤ :=
  (detZ i ^ k).coeff α * α.prod fun _ n => ((n.factorial : ℕ) : ℤ)

theorem cast_intCoeff (C : Type) [Field C] (i k : ℕ) (α : (Σ _ : Fin i, Fin i) →₀ ℕ) :
    ((intCoeff i k α : ℤ) : C) = (detPow C i k).coeff α * GlobalTheory.FGDepth.mfact α := by
  rw [intCoeff, detPow_eq_map, MvPolynomial.coeff_map, Int.cast_mul, GlobalTheory.FGDepth.mfact]
  congr 1 <;> simp [Finsupp.prod]

theorem mem_support_iff' (C : Type) [Field C] [CharZero C] (i k : ℕ) (α) :
    α ∈ (detPow C i k).support ↔ α ∈ (detZ i ^ k).support := by
  rw [MvPolynomial.mem_support_iff, MvPolynomial.mem_support_iff, detPow_eq_map,
    MvPolynomial.coeff_map]
  simp

theorem intCoeff_ne_zero (i k : ℕ) (α) (h : α ∈ (detZ i ^ k).support) : intCoeff i k α ≠ 0 := by
  rw [intCoeff]
  refine mul_ne_zero (MvPolynomial.mem_support_iff.1 h) ?_
  rw [Finsupp.prod]
  refine Finset.prod_ne_zero_iff.2 fun a _ => ?_
  exact_mod_cast Nat.factorial_ne_zero _

theorem v_intCast (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (p : ℕ)
    (hp : p.Prime) (hv : v (p : C) = 1) (m : ℤ) (hm : m ≠ 0) :
    v (m : C) = (((padicValNat p m.natAbs : ℕ) : ℝ) : WithTop ℝ) := by
  have h := GlobalTheory.addValuation_natCast_eq_padicValNat C v p hp hv m.natAbs (Int.natAbs_ne_zero.2 hm)
  rcases Int.natAbs_eq m with h1 | h1
  · conv_lhs => rw [h1]
    simpa using h
  · conv_lhs => rw [h1, Int.cast_neg, v.map_neg]
    simpa using h

end GlobalTheory.DetPowContent

namespace GlobalTheory


open GlobalTheory.DetPowShape GlobalTheory.DetPowContent in
theorem detPow_content_const : ∀ (p : ℕ), p.Prime → ∀ i k : ℕ, ∃ κ : ℝ, ∀ (C : Type) [Field C]
    [CharZero C] (v : AddValuation C (WithTop ℝ)), v (p : C) = 1 →
      content v (detPow C i k) = (κ : EReal) := by
  intro p hp i k
  set S := (detZ i ^ k).support with hS
  have hne : S.Nonempty := by
    refine ⟨∑ a : Fin i, Finsupp.single ⟨a, a⟩ k, ?_⟩
    rw [← mem_support_iff' ℚ]
    rw [MvPolynomial.mem_support_iff, (detPow_shape ℚ i k).2.2.1]
    exact one_ne_zero
  let f : ((Σ _ : Fin i, Fin i) →₀ ℕ) → ℕ := fun α => padicValNat p (intCoeff i k α).natAbs
  obtain ⟨α0, hα0, hmin⟩ := S.exists_min_image f hne
  refine ⟨(f α0 : ℝ), fun C _ _ v hv => ?_⟩
  have hval : ∀ α ∈ S, GlobalTheory.FGDepth.toE (v ((detPow C i k).coeff α * GlobalTheory.FGDepth.mfact α)) =
      ((f α : ℝ) : EReal) := by
    intro α hα
    rw [← cast_intCoeff, v_intCast C v p hp hv _ (intCoeff_ne_zero i k α hα)]
    rfl
  unfold GlobalTheory.FGDepth.content
  apply le_antisymm
  · refine iInf₂_le_of_le α0 ((mem_support_iff' C i k α0).2 hα0) ?_
    rw [hval α0 hα0]
  · refine le_iInf₂ fun α hα => ?_
    have hα' := (mem_support_iff' C i k α).1 hα
    rw [hval α hα']
    exact_mod_cast hmin α hα'

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledWeilRepresentationLocalityFinitePlace
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.WeilLocalityDbl

theorem comm_off {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}
    (B : Base F E) (G : Geo σ a a')
    (dd : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J))) (Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a')))
    (omd : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J)) →* Module.End ℂ (((Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a')) → AF F) → ℂ))
    (hW : IsUSplitting (adeleClass F) B.ψ dd (actB (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ)) omd)
    (v : Pl (F := F)) (g : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J))) (hg : At (evFin F v) (GlobalTheory.InertDbl.matD g - 1))
    (u : AF F) (hu : evFin F v u = 0) (p q : (Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a')) → AF F)
    (Φ : ((Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a')) → AF F) → ℂ)
    (hΦ : Φ ∈ GlobalTheory.WeilM.schA F (Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a'))) :
      omd g (GlobalTheory.WeilM.schr B.ψ (u • p, u • q) Φ) = GlobalTheory.WeilM.schr B.ψ (u • p, u • q) (omd g Φ) := by

  have hw0 : dd.e.symm (u • p, u • q) = u • dd.e.symm (p, q) := by
    rw [← Prod.smul_mk, LinearEquiv.map_smul]
  have hM : u • GlobalTheory.InertDbl.matD g = u • (1 : Matrix _ _ (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) := by
    rw [← sub_eq_zero, ← smul_sub]
    exact hg u hu
  have hact : actB (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) g (dd.e.symm (u • p, u • q)) = dd.e.symm (u • p, u • q) := by
    rw [hw0]
    show (u • dd.e.symm (p, q)) * (GlobalTheory.InertDbl.matD g)ᵀ = u • dd.e.symm (p, q)
    rw [Matrix.smul_mul, ← Matrix.mul_smul, ← Matrix.transpose_smul, hM, Matrix.transpose_smul,
      Matrix.transpose_one, Matrix.mul_smul, Matrix.mul_one]
  have h := hW.impl g (dd.e.symm (u • p, u • q)) Φ hΦ
  rw [hact] at h
  simpa only [Darboux.rho, LinearEquiv.apply_symm_apply] using h

private lemma at_add_divisor {F : Type} [Field F] [NumberField F] {κ : Type} (v : Pl (F := F)) {z z' : κ → AF F}
    (hz : At (evFin F v) z) (hz' : At (evFin F v) z') : At (evFin F v) (z + z') := by
  intro u hu
  rw [smul_add, hz u hu, hz' u hu, add_zero]

private lemma at_liftV' {F : Type} [Field F] [NumberField F] {κ : Type} (v : Pl (F := F)) (t : κ → Fv F v) :
    At (evFin F v) (fun i => GlobalTheory.LatVac.liftV v (t i)) := by
  intro u hu
  funext i
  show u • GlobalTheory.LatVac.liftV v (t i) = 0
  exact GlobalTheory.LatVac.at_liftV v (t i) u hu

theorem locality : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (dd : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J))) (Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a'))) (omd : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J)) →* Module.End ℂ (((Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a')) → AF F) → ℂ)),
    IsUWeilSplit (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (adeleClass F) B.ψ (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J)) dd X.α (diagCols (Fin (a + a'))) omd →
    ∀ g : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J)), At (evFin F v) (GlobalTheory.InertDbl.matD g - 1) →
    ∀ φ ∈ SB ((Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a')) → Fv F v), ∃ φ₁ ∈ SB ((Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a')) → Fv F v), Acts (evFin F v) (omd g) φ φ₁ := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hTr v dd omd hWS g hg φ hφ
  have hW := hWS.2.1

  obtain ⟨R, hR0, hR⟩ := GlobalTheory.T.exists_complementary_adelicSchwartz_restFunction (F := F) (Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a')) v
  have hRφ := hR φ hφ

  have htr : ∀ c : (Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a')) → AF F, (∀ i, evFin F v (c i) = 0) →
      ∀ Φ ∈ schA F (Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a')),
        omd g (fun x => Φ (x + c)) = fun x => omd g Φ (x + c) := by
    intro c hc Φ hΦ
    have hu : evFin F v (1 - GlobalTheory.LatVac.liftV v (1 : Fv F v)) = 0 := by
      rw [map_sub, map_one, GlobalTheory.LatVac.evFin_liftV, sub_self]
    have huc : (1 - GlobalTheory.LatVac.liftV v (1 : Fv F v)) • c = c := by
      funext i
      show (1 - GlobalTheory.LatVac.liftV v (1 : Fv F v)) • c i = c i
      rw [smul_eq_mul, sub_mul, one_mul, GlobalTheory.WeilLocalityW.liftV_one_mul, hc i, map_zero, sub_zero]
    have h := comm_off B G dd omd hW v g hg _ hu c 0 Φ hΦ
    rw [huc, smul_zero] at h
    have hs : ∀ Ψ : ((Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a')) → AF F) → ℂ,
        GlobalTheory.WeilM.schr B.ψ (c, 0) Ψ = fun x => Ψ (x + c) := by
      intro Ψ
      funext x
      simp [GlobalTheory.WeilM.schr]
    rw [hs, hs] at h
    exact h

  refine ⟨fun t => (R 0)⁻¹ * omd g (tens (evFin F v) φ R) (fun i => GlobalTheory.LatVac.liftV v (t i)), ?_, ?_⟩
  · have h1 : omd g (tens (evFin F v) φ R) ∈ schA F (Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a')) :=
      hW.pres g _ hRφ.2
    exact (SB _).smul_mem (R 0)⁻¹ (GlobalTheory.T.adelicSchwartz_restrict_finitePlace_mem_schwartzBruhat v _ h1)
  · intro r hr
    funext y

    obtain ⟨yv, hyv⟩ : ∃ yv : (Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a')) → AF F,
        yv = fun i => GlobalTheory.LatVac.liftV v (evFin F v (y i)) := ⟨_, rfl⟩
    obtain ⟨y', hy'⟩ : ∃ y' : (Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a')) → AF F, y' = y - yv := ⟨_, rfl⟩
    have hatv : At (evFin F v) yv := by rw [hyv]; exact at_liftV' v _
    have hev : ∀ i, evFin F v (yv i) = evFin F v (y i) := by
      intro i; rw [hyv]; exact GlobalTheory.LatVac.evFin_liftV v _
    have hoff : ∀ i, evFin F v (y' i) = 0 := by
      intro i; rw [hy', Pi.sub_apply, map_sub, hev, sub_self]
    have hsum : y' + yv = y := by rw [hy', sub_add_cancel]
    have hry : r y = r y' := by rw [← hsum]; exact hr.1 y' yv hatv

    have hD : R 0 • tens (evFin F v) φ r - r y' • (fun x => tens (evFin F v) φ R (x + -y')) ∈
        schA F (Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a')) :=
      sub_mem (Submodule.smul_mem _ _ hr.2) (Submodule.smul_mem _ _ (_root_.GlobalTheory.SchwartzTranslation.schA_add_const (-y') _ hRφ.2))
    have hvan : ∀ z, At (evFin F v) z →
        (R 0 • tens (evFin F v) φ r - r y' • (fun x => tens (evFin F v) φ R (x + -y'))) (y + z) = 0 := by
      intro z hz
      have e1 : r (y + z) = r y' := by
        rw [← hsum, add_assoc]; exact hr.1 y' (yv + z) (at_add_divisor v hatv hz)
      have e2 : y + z + -y' = 0 + (yv + z) := by rw [← hsum]; abel
      have e3 : R (y + z + -y') = R 0 := by rw [e2]; exact hRφ.1 0 (yv + z) (at_add_divisor v hatv hz)
      have e4 : (fun i => evFin F v ((y + z + -y') i)) = fun i => evFin F v ((y + z) i) := by
        funext i
        simp only [Pi.add_apply, Pi.neg_apply, map_add (f := _), map_neg, hoff, neg_zero, add_zero]
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, tens]
      rw [e1, e3, e4]
      ring
    have hT := GlobalTheory.T.isometry_commuting_heisenberg_acts_fibrewise v B.ψ (omd g) hTr.base.std (GlobalTheory.T.standardAdelicAddChar_nontrivial_finitePlace B.ψ hTr.base.std)
      (fun Φ hΦ => hW.pres g Φ hΦ) (fun μ hμ Φ hΦ => hW.unit μ hμ g Φ hΦ)
      (fun u hu p q Φ hΦ => comm_off B G dd omd hW v g hg u hu p q Φ hΦ) _ hD y hvan
    have hoff' : ∀ i, evFin F v ((-y') i) = 0 := by
      intro i; rw [Pi.neg_apply, map_neg, hoff, neg_zero]
    rw [map_sub, map_smul, map_smul, htr (-y') hoff' _ hRφ.2] at hT
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hT
    have e5 : y + -y' = yv := by rw [← hsum]; abel
    rw [e5, sub_eq_zero] at hT
    show omd g (tens (evFin F v) φ r) y =
      (R 0)⁻¹ * omd g (tens (evFin F v) φ R) (fun i => GlobalTheory.LatVac.liftV v (evFin F v (y i))) * r y
    rw [← hyv, hry]
    calc omd g (tens (evFin F v) φ r) y = (R 0)⁻¹ * (R 0 * omd g (tens (evFin F v) φ r) y) := by
          rw [inv_mul_cancel_left₀ hR0]
      _ = _ := by rw [hT]; ring

end GlobalTheory.WeilLocalityDbl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCocyclePullbackRepresentation
section
set_option autoImplicit false

noncomputable section

open NumberField Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn GlobalTheory.CuspEmb

namespace GlobalTheory.PullCocycle

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {U C : Type} [Group U] [MulAction U C]

theorem formula_span (M : TwoLevels E r U C) (ka : Wt M.Ψ r) (ρ : Representation ℂ U (M.cusp ka))
    (a : U → C → ℂˣ)
    (ha : ∀ (h : U) (F : C → Frame M.Ψ r → ℂ) (hF : F ∈ M.SS ka) (c : C) (x : M.dom),
      ((ρ h⁻¹ ⟨M.res F, Submodule.subset_span ⟨F, hF, rfl⟩⟩ : M.cusp ka) : C → M.dom → ℂ) c x =
        (a h c : ℂ) * M.pull h F c x.1)
    (h : U) (c : C) (x : M.dom) (g : C → M.dom → ℂ) (hg : g ∈ Submodule.span ℂ (M.res '' M.SS ka)) :
    ((ρ h⁻¹ ⟨g, hg⟩ : M.cusp ka) : C → M.dom → ℂ) c x = (a h c : ℂ) * g (h • c) (Lmap M h c x) := by
  induction hg using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨F, hF, rfl⟩ := hy
    exact ha h F hF c x
  | zero =>
    show ((ρ h⁻¹ 0 : M.cusp ka) : C → M.dom → ℂ) c x = _
    simp
  | add y z hy hz ihy ihz =>
    show ((ρ h⁻¹ ((⟨y, hy⟩ : M.cusp ka) + ⟨z, hz⟩) : M.cusp ka) : C → M.dom → ℂ) c x = _
    rw [map_add (f := _), Submodule.coe_add, Pi.add_apply, Pi.add_apply, ihy, ihz]
    simp [mul_add]
  | smul t y hy ih =>
    show ((ρ h⁻¹ (t • (⟨y, hy⟩ : M.cusp ka)) : M.cusp ka) : C → M.dom → ℂ) c x = _
    rw [map_smul, Submodule.coe_smul, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, ih]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring

theorem rho_inv_rho (M : TwoLevels E r U C) (ka : Wt M.Ψ r) (ρ : Representation ℂ U (M.cusp ka)) (h : U)
    (f : M.cusp ka) : ρ h⁻¹ (ρ h f) = f := by
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

theorem pull_mul_eq (M : TwoLevels E r U C) (f : C → M.dom → ℂ) (hf : IsInv M f) (g h : U) (c : C) (x : M.dom) :
    f ((h * g) • c) (Lmap M (h * g) c x) = f (h • g • c) (Lmap M h (g • c) (Lmap M g c x)) := by
  set γ := M.tr (h * g) c * (M.tr h (g • c) * M.tr g c)⁻¹ with hγdef
  have hγ : γ ∈ (M.comp ((h * g) • c)).Γ := M.tr_mul h g c
  have e : lact γ (Lmap M h (g • c) (Lmap M g c x)).1 = (Lmap M (h * g) c x).1 := by
    show lact γ (lact (M.tr h (g • c)) (lact (M.tr g c) x.1)) = lact (M.tr (h * g) c) x.1
    rw [← ReciprocityTheory.ChartRestriction.G.AR.Up.FundSetPf.lact_mul (M.tr h (g • c)) (M.tr g c),
      ← ReciprocityTheory.ChartRestriction.G.AR.Up.FundSetPf.lact_mul γ, hγdef, inv_mul_cancel_right]
  have hx : lact γ (Lmap M h (g • c) (Lmap M g c x)).1 ∈ M.dom := e ▸ (Lmap M (h * g) c x).2
  have := hf ((h * g) • c) γ hγ (Lmap M h (g • c) (Lmap M g c x)) hx
  have e2 : (⟨lact γ (Lmap M h (g • c) (Lmap M g c x)).1, hx⟩ : M.dom) = Lmap M (h * g) c x := Subtype.ext e
  rw [e2] at this
  rw [this, mul_smul]

theorem exists_cocycle : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U] [MulAction U C] (M : TwoLevels E r U C) (ka : Wt M.Ψ r) (ρ : Representation ℂ U (M.cusp ka)), IsPullRep M ka ρ → (∀ f ∈ M.cusp ka, IsInv M f) → ∃ a : U → C → ℂˣ, (∀ (g h : U) (c : C), a (h * g) c = a g c * a h (g • c)) ∧ ∀ (h : U) (f : M.cusp ka) (c : C) (x : M.dom), ((ρ h⁻¹ f : M.cusp ka) : C → M.dom → ℂ) c x = (a h c : ℂ) * (f : C → M.dom → ℂ) (h • c) (Lmap M h c x) := by
  intro E _ _ _ r U C _ _ M ka ρ hρ hinv
  obtain ⟨a, ha⟩ := hρ
  have hform : ∀ (h : U) (f : M.cusp ka) (c : C) (x : M.dom),
      ((ρ h⁻¹ f : M.cusp ka) : C → M.dom → ℂ) c x = (a h c : ℂ) * (f : C → M.dom → ℂ) (h • c) (Lmap M h c x) := by
    rintro h ⟨g, hg⟩ c x
    exact formula_span M ka ρ a ha h c x g hg
  classical
  let C0 : C → Prop := fun c => ∃ f : M.cusp ka, ∃ x : M.dom, (f : C → M.dom → ℂ) c x ≠ 0
  have hstab : ∀ (h : U) (c : C), C0 c → C0 (h • c) := by
    rintro h c ⟨f, x, hfx⟩
    refine ⟨ρ h f, Lmap M h c x, fun h0 => hfx ?_⟩
    calc (f : C → M.dom → ℂ) c x = ((ρ h⁻¹ (ρ h f) : M.cusp ka) : C → M.dom → ℂ) c x := by
          rw [rho_inv_rho]
      _ = (a h c : ℂ) * ((ρ h f : M.cusp ka) : C → M.dom → ℂ) (h • c) (Lmap M h c x) := hform h _ c x
      _ = 0 := by rw [h0, mul_zero]
  have hstab' : ∀ (h : U) (c : C), ¬ C0 c → ¬ C0 (h • c) := fun h c hc h1 => hc (by
    have := hstab h⁻¹ (h • c) h1
    rwa [inv_smul_smul] at this)
  have hcoc : ∀ (g h : U) (c : C) (x : M.dom) (f : M.cusp ka),
      (a (h * g) c : ℂ) * (f : C → M.dom → ℂ) ((h * g) • c) (Lmap M (h * g) c x) =
        (a g c : ℂ) * (a h (g • c) : ℂ) * (f : C → M.dom → ℂ) ((h * g) • c) (Lmap M (h * g) c x) := by
    intro g h c x f
    have L := hform (h * g) f c x
    have R : ((ρ (h * g)⁻¹ f : M.cusp ka) : C → M.dom → ℂ) c x =
        (a g c : ℂ) * ((a h (g • c) : ℂ) * (f : C → M.dom → ℂ) (h • g • c) (Lmap M h (g • c) (Lmap M g c x))) := by
      rw [mul_inv_rev, map_mul, Module.End.mul_apply, hform g, hform h]
    rw [← L, R, pull_mul_eq M _ (hinv _ f.2) g h c x]
    ring
  refine ⟨fun h c => if C0 c then a h c else 1, ?_, ?_⟩
  · intro g h c
    by_cases hc : C0 c
    · have hgc : C0 (g • c) := hstab g c hc
      have hhgc : C0 ((h * g) • c) := hstab (h * g) c hc
      simp only [hc, hgc, if_true]
      obtain ⟨f', x, hfx⟩ := hc
      set f := ρ (h * g) f' with hfdef
      have hV : (f : C → M.dom → ℂ) ((h * g) • c) (Lmap M (h * g) c x) ≠ 0 := by
        intro h0
        apply hfx
        calc (f' : C → M.dom → ℂ) c x = ((ρ (h * g)⁻¹ f : M.cusp ka) : C → M.dom → ℂ) c x := by
              rw [hfdef, rho_inv_rho]
          _ = 0 := by rw [hform, h0, mul_zero]
      ext
      push_cast
      exact mul_right_cancel₀ hV (hcoc g h c x f)
    · have hgc : ¬ C0 (g • c) := hstab' g c hc
      simp [hc, hgc]
  · intro h f c x
    by_cases hc : C0 c
    · simp only [hc, if_true]
      exact hform h f c x
    · have hhc : ¬ C0 (h • c) := hstab' h c hc
      simp only [hc, if_false, Units.val_one, one_mul]
      have l0 : ((ρ h⁻¹ f : M.cusp ka) : C → M.dom → ℂ) c x = 0 := by
        by_contra hne
        exact hc ⟨ρ h⁻¹ f, x, hne⟩
      have r0 : (f : C → M.dom → ℂ) (h • c) (Lmap M h c x) = 0 := by
        by_contra hne
        exact hhc ⟨f, _, hne⟩
      rw [l0, r0]

end GlobalTheory.PullCocycle

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactSubgroupUnitaryPointsSupportedAtPlaStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix Filter Topology
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

open scoped GlobalTheory.VacAny
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_compactSubgroup_unitaryPoints_supportedAtPlace : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E},
    (∀ x, σ (σ x) = x) → ∀ {n : ℕ} (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))
    (U : Set (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J)), U ∈ 𝓝 (1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J) →
    ∃ K : Subgroup (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J), (∀ g ∈ K, g ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ X (GlobalTheory.AdelicU.evFin F v)) ∧
      IsCompact (K : Set (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J)) ∧
      (∃ O : Set (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J), IsOpen O ∧ (1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J) ∈ O ∧
        ∀ g ∈ O, g ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ X (GlobalTheory.AdelicU.evFin F v) → g ∈ K) ∧ (K : Set (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J)) ⊆ U := by
  first | exact @GlobalTheory.SmallAtPlace.exists_compact_subgroup_at_place | exact GlobalTheory.SmallAtPlace.exists_compact_subgroup_at_place | (intros; apply GlobalTheory.SmallAtPlace.exists_compact_subgroup_at_place <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoordOfIndep
section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links

set_option autoImplicit false

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.BigOn.Exp

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_coord_of_indep {K V W : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module ℂ W]
    (e : K →+* ℂ) (rd : V →ₛₗ[e] W)
    (hF : ∀ (n : ℕ) (v : Fin n → V), LinearIndependent K v → LinearIndependent ℂ fun c => rd (v c))
    {μ : ℂ} {f f' : V} (hf : f ≠ 0) (h : rd f' = μ • rd f) : ∃ u : K, e u = μ := by
  have hrf : rd f ≠ 0 := (hF 1 (fun _ => f) (linearIndependent_unique_iff.2 hf)).ne_zero 0
  by_cases hli : LinearIndependent K ![f, f']
  · have h2 := hF 2 _ hli
    have h2' : LinearIndependent ℂ ![rd f, rd f'] := by
      convert h2 using 1
      funext c
      fin_cases c <;> rfl
    have := (LinearIndependent.pair_iff.1 h2') (-μ) 1 (by rw [h, one_smul, neg_smul, neg_add_cancel])
    exact absurd this.2 one_ne_zero
  · rw [LinearIndependent.pair_iff] at hli
    push_neg at hli
    obtain ⟨s, t, hst, hne⟩ := hli
    have ht : t ≠ 0 := by
      intro ht0
      rw [ht0, zero_smul, add_zero] at hst
      exact hne ((smul_eq_zero.1 hst).resolve_right hf) ht0
    have hf' : f' = (-(s / t)) • f := by
      have : t • f' = -(s • f) := eq_neg_of_add_eq_zero_right hst
      calc f' = t⁻¹ • (t • f') := by rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
        _ = _ := by rw [this, smul_neg, smul_smul, ← neg_smul, div_eq_inv_mul]
    refine ⟨-(s / t), ?_⟩
    have h3 : e (-(s / t)) • rd f = μ • rd f := by rw [← h, hf', map_smulₛₗ]
    exact smul_left_injective ℂ hrf h3

end GlobalTheory.BigOn.Exp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaussianDatumFlippedFiniteTensorBigRouteStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_gaussianDatum_flippedFiniteTensor_bigRoute : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (M : Vol G) (hst : SquareStanding G t)
    (e : Num G i j) (Bs : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (X : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E)
    (om : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W) (om' : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (h : IsTripleOf W M t i j e Bs Γ X), IsTriple Bs Γ X om om' → IsTied t i j e Bs Γ X → ∀ n Φ τ τ',
    (∀ w ∈ locPl G t, depthAt G w ≤ n w ∧ IsNatDatum (unifAt w) (n w) (Φ w)) → HasFlip B t ρ i j n Φ τ τ' →
    ∀ φ, IsFinPart Γ.M X.T φ →
    (∀ w ∈ locPl G t, IsLocFn W B t e Γ w (w.under (𝓞 D.host.F)) (flipAt W t i j w (n w) (Φ w)) (φ (w.under (𝓞 D.host.F)))) →
    ∃ f₀, f₀ ≠ 0 ∧ Γ.M.IsGauss Bs.ψ Bs.emb f₀ ∧ IsDatumA W e Γ τ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₀ φ) := by
  first | exact @GlobalTheory.BigDat.exists_gauss_datum | exact GlobalTheory.BigDat.exists_gauss_datum | (intros; apply GlobalTheory.BigDat.exists_gauss_datum <;> assumption)
end

