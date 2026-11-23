module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankH1fDeRham
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0603
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0132
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TranslateMemCoefLatFn
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0605
public import Formalism.SharpRestriction.LevelLetterCocycles.DecompositionData
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBreuilKisinModuleBasisOfFCrystal
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTaylorShiftFrobeniusTwoVariableCompatible
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0602
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0482
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadicValNatFactorialBound
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0502
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0504
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0556
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0526
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0483
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoboundaryMemBlochKatoCocycles
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0198
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0294
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0599
public import Formalism.AdmissibleDesigns.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0607
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0317
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankH1fDeRhamStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_H1f_de_rham : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ A : GRep ↥(GK K) ℚ_[l] LL O, IsDR (P.PD K) A.ρ → Module.Finite LL (FiniteCohomology (P.PD K) A.ρ) ∧ (finrank LL (FiniteCohomology (P.PD K) A.ρ) : ℤ) = finrank LL ↥(H0V A.ρ) + ((finrank LL ↥(DdR (P.PD K) A.ρ) : ℤ) - finrank LL ↥(DdR (P.PD K) A.ρ ⊓ FilV (P.PD K) (LL := LL) (V := A.V) 0)) := by
  first | exact @GlobalTheory.SeqDim.h1f_finrank | exact GlobalTheory.SeqDim.h1f_finrank | (intros; apply GlobalTheory.SeqDim.h1f_finrank <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FischerInnerFormFockSubstitutionUnitaryInvariantStatement
section
open Formalism.BasicNotions Formalism.IndefR.Datum Formalism.IndefR.Links
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fischerInnerForm_fockSubstitution_unitary_invariant : ∀ (D : D7) (m n : ℕ) (p : D.what₂.Tau → ℕ) (U : GlobalTheory.ExportSeries.GLR D n), (∀ τ, (U τ).val ∈ Matrix.unitaryGroup (Fin n) ℂ) → ∀ P Q : PolF D m n, GlobalTheory.FockIsotypic.fis (GlobalTheory.ExportSeries.fockSubst p U P) (GlobalTheory.ExportSeries.fockSubst p U Q) = GlobalTheory.FockIsotypic.fis P Q := by
  first | exact @GlobalTheory.FockIsotypic.fis_fockSubst_of_unitary | exact GlobalTheory.FockIsotypic.fis_fockSubst_of_unitary | (intros; apply GlobalTheory.FockIsotypic.fis_fockSubst_of_unitary <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontainePropertiesAllPlacesStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fontaineAtPlacesOverL : ∀ (D : D7) (i : D.nd.Loc), Formalism.MainNotions.TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL (D := D) i := by
  first | exact @GlobalTheory.FontaineAdm.fontaineProperties_all_places | exact GlobalTheory.FontaineAdm.fontaineProperties_all_places | (intros; apply GlobalTheory.FontaineAdm.fontaineProperties_all_places <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisDividedTaylorExpansionFrobeniusBasis
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.CrysGal

open GlobalTheory.Prism

theorem span_range_tr {l : ℕ} {R : Type} [CommRing R] (E : FCrys l R) {P P' : Obj l R}
    (f : GlobalTheory.Prism.Hom P P') : Submodule.span P'.A (Set.range (E.tr f)) = ⊤ := by
  have hu := (E.tr_bc f (E.M P' ⧸ Submodule.span P'.A (Set.range (E.tr f))) 0).unique
    (y₁ := Submodule.mkQ _) (y₂ := 0)
    (fun x => by
      show Submodule.Quotient.mk _ = 0
      rw [Submodule.Quotient.mk_eq_zero]
      exact Submodule.subset_span ⟨x, rfl⟩)
    (fun x => rfl)
  rw [eq_top_iff]
  intro x _
  have := LinearMap.congr_fun hu x
  rwa [Submodule.mkQ_apply, LinearMap.zero_apply, Submodule.Quotient.mk_eq_zero] at this

theorem mem_span_tr {l : ℕ} {R : Type} [CommRing R] (E : FCrys l R) {P P' : Obj l R}
    (f : GlobalTheory.Prism.Hom P P') {O ι : Type} [Fintype ι] (oE : O → FHom E E) (b : ι → E.M P)
    (hgen : ∀ x : E.M P, ∃ (N : ℕ) (c : ι → Fin N → O) (s : ι → Fin N → P.A),
      x = ∑ j, ∑ q, s j q • (oE (c j q)).u P (b j)) (x : E.M P') :
    x ∈ Submodule.span P'.A (Set.range fun p : O × ι => (oE p.1).u P' (E.tr f (b p.2))) := by
  have hx : x ∈ Submodule.span P'.A (Set.range (E.tr f)) := (span_range_tr E f) ▸ Submodule.mem_top
  refine (Submodule.span_le.2 ?_) hx
  rintro _ ⟨z, rfl⟩
  obtain ⟨N, c, s, hz⟩ := hgen z
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hz, map_sum]
  refine Submodule.sum_mem _ fun j _ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Submodule.sum_mem _ fun q _ => ?_
  rw [map_smulₛₗ, ← (oE (c j q)).u_tr]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(c j q, j), rfl⟩)

theorem exists_rep {A M O ι : Type} [CommRing A] [AddCommGroup M] [Module A M] [Fintype ι] [DecidableEq ι]
    (v : O → ι → M) (x : ι → M) (hx : ∀ j, x j ∈ Submodule.span A (Set.range fun p : O × ι => v p.1 p.2)) :
    ∃ (Q : Type) (_ : Fintype Q) (c : ι → ι → Q → O) (y : ι → ι → Q → A),
      ∀ j, x j = ∑ i, ∑ q, y i j q • v (c i j q) i := by
  choose n w gg hgg using fun j => Submodule.mem_span_set'.1 (hx j)
  choose pc hpc using fun j k => (gg j k).2
  refine ⟨Σ j', Fin (n j'), inferInstance, fun i j q => (pc q.1 q.2).1,
    fun i j q => if q.1 = j then (if (pc q.1 q.2).2 = i then w q.1 q.2 else 0) else 0, fun j => ?_⟩
  rw [Finset.sum_comm]
  rw [Fintype.sum_sigma]
  rw [Finset.sum_eq_single j (fun j' _ hj' => by simp [hj']) (by simp)]
  rw [← hgg j]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [if_true, ite_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ]
  rw [← hpc j k]

theorem conv_comb {l : ℕ} [Fact l.Prime] {a e : ℕ} [NeZero a] [NeZero e] {O K : Type} [CommRing O]
    [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K]
    [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e)
    (g : ↥(GK (ϖ.field a))) {Q : Type} [Fintype Q] (c : Q → O) (z : Q → Per.Acris l)
    (F : Q → ℕ → (ZMod a → S O K e)) (G : ℕ → (ZMod a → S O K e)) (hG : ∀ k, G k = ∑ q, c q • F q k)
    (r : ℕ) (hconv : ∀ q, ∃ n₀ : ℕ, ∀ n ≥ n₀, (l : OCr l O) ^ r ∣
      (1 : O) ⊗ₜ[ℤ_[l]] z q - ∑ k ∈ Finset.range n, ϖ.muDiv a O g k * ϖ.iC t K (F q k))
    (w : OCr l O) (hw : w = ∑ q, c q ⊗ₜ[ℤ_[l]] z q) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, (l : OCr l O) ^ r ∣
      w - ∑ k ∈ Finset.range n, ϖ.muDiv a O g k * ϖ.iC t K (G k) := by
  subst hw
  choose n₀ hn₀ using hconv
  refine ⟨Finset.univ.sup n₀, fun n hn => ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    simp_rw [hG, map_sum, map_smul, Finset.mul_sum, mul_smul_comm]
  rw [Finset.sum_comm, ← Finset.sum_sub_distrib]
  apply Finset.dvd_sum
  intro q _
  rw [← Finset.smul_sum, show c q ⊗ₜ[ℤ_[l]] z q = c q • ((1 : O) ⊗ₜ[ℤ_[l]] z q) by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one], ← smul_sub, Algebra.smul_def]
  exact Dvd.dvd.mul_left (hn₀ q n (le_trans (Finset.le_sup (Finset.mem_univ q)) hn)) _

theorem comb_S {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
    {a e : ℕ} {Q : Type} [Fintype Q] (c : Q → O) (w : ZMod a → Q → K⟦X⟧⟦X⟧)
    (G : ℕ → ZMod a → S O K e) (F : Q → ℕ → ZMod a → S O K e)
    (hG : ∀ k τ, (G k τ : K⟦X⟧) = (X : K⟦X⟧) ^ k * ((k.factorial : K⟦X⟧) * coeff k (∑ q, c q • w τ q)))
    (hF : ∀ q k τ, (F q k τ : K⟦X⟧) = (X : K⟦X⟧) ^ k * ((k.factorial : K⟦X⟧) * coeff k (w τ q))) :
    ∀ k, G k = ∑ q, c q • F q k := by
  intro k
  funext τ
  apply Subtype.ext
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hG, Finset.sum_apply, AddSubmonoidClass.coe_finsetSum, map_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Pi.smul_apply, SetLike.val_smul, hF, PowerSeries.coeff_smul, mul_smul_comm, mul_smul_comm]


set_option maxHeartbeats 1000000 in
theorem galois_taylor_basis : GlobalTheory.Published.BhattScholzeCrystallineLattices → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T), IsBK (T := resF T (ϖ.field a)) (I.res (inclG (ϖ.field a)) (continuous_subtype_val.subtype_mk _)) → ∀ (hS : ∀ (τ : ZMod a) (j : ι) (k : ℕ) (i : ι), (X : (↥LL.1)⟦X⟧) ^ k * (P.mxInv τ *ᵥ (P.nabla ^ k) (P.phi (bas j)) τ) i ∈ S (↥(OL LL)) (↥LL.1) e) (g : ↥(GK (ϖ.field a))), ∃ Γ, (I.res (inclG (ϖ.field a)) (continuous_subtype_val.subtype_mk _)).IsLMat (g : GQ l) g Γ ∧ ∀ (i j : ι) (r : ℕ), ∃ n₀ : ℕ, ∀ n ≥ n₀, (l : OCr l ↥(OL LL)) ^ r ∣ toOCr l ↥(OL LL) (Γ i j) - ∑ k ∈ Finset.range n, ϖ.muDiv a ↥(OL LL) g k * ϖ.iC (thetaW a LL) ↥LL.1 (fun τ => ⟨_, hS τ j k i⟩) := by
  intro BS l _ a e _ _ ϖ LL _ _ hl2 ι _ _ P T I hBK hS g
  letI := zlLat (resF T (ϖ.field a))
  obtain ⟨E, jA, hR, hIm⟩ := hBK
  have hO : ∀ c : ↥(OL LL), ∃ u : FHom E E, ∀ x, jA (u.u (ainfObj (ϖ.field a)) x) =
      (OfCrystal.mulZ (resF T (ϖ.field a)) c).lTensor (WCb l) (jA x) := fun c => by
    obtain ⟨u, hu, -⟩ := (BS l (ϖ.field a) (ainfObj (ϖ.field a)) (ainfId (ϖ.field a)) hR.ainf).2 _ _ _ _ E E jA jA hR hR
      (OfCrystal.mulZ (resF T (ϖ.field a)) c) fun g x => (((resF T (ϖ.field a)).actT g).map_smul c x).symm
    exact ⟨u, hu⟩
  choose oE hoE using hO
  obtain ⟨b, hb, hgen⟩ := GlobalTheory.T.breuilKisinPrism_crystal_basis_and_span l a e ↥(OL LL) ↥LL.1 (thetaW a LL) ϖ ι P (resF T (ϖ.field a)) (I.res (inclG (ϖ.field a)) (continuous_subtype_val.subtype_mk _)) E jA hR hIm oE hoE
  obtain ⟨sh, φ₂, hsh, hφC, hφsh⟩ := GlobalTheory.TaylorShift.shift_frob_exists l ↥LL.1
  obtain ⟨PP, S₀, p₀, p₁, δ, κ, κ₀, hPPI, hδ, hκ₀, hκp, hκφ, hSS, -, hev⟩ :=
    GlobalTheory.T.exists_crystalline_prisms l a e ↥(OL LL) ↥LL.1 (thetaW a LL) ϖ hl2 sh φ₂ hsh hφC hφsh
  obtain ⟨Q, _, c, y, hε⟩ := GlobalTheory.CrysGal.exists_rep (A := PP.A)
    (fun c i => (oE c).u PP (E.tr p₀ (b i))) (fun j => E.tr p₁ (b j))
    (fun j => GlobalTheory.CrysGal.mem_span_tr E p₀ oE b hgen _)
  have hF := GlobalTheory.T.crystal_changeOfBasis_frobenius_compat l a e ↥(OL LL) ↥LL.1 (thetaW a LL) ϖ ι P (resF T (ϖ.field a)) (I.res (inclG (ϖ.field a)) (continuous_subtype_val.subtype_mk _)) E jA hR hIm oE hoE b hb sh φ₂ hsh hφC PP p₀ p₁ κ hPPI hκp hκφ Q c y hε
  have hD := GlobalTheory.T.prismCrystal_changeOfBasis_constantCoeff_eq_one l a e ↥(OL LL) ↥LL.1 (thetaW a LL) ϖ ι P (resF T (ϖ.field a)) (I.res (inclG (ϖ.field a)) (continuous_subtype_val.subtype_mk _)) E jA hR hIm oE hoE b hb PP S₀ p₀ p₁ δ κ κ₀ hδ hκ₀ (fun τ x => (hκp τ x).1) Q c y hε
  have hK := GlobalTheory.T.frobeniusStratification_coeff_eq_connection_pow ↥(OL LL) ↥LL.1 l e a ι P sh φ₂ hsh hφC hφsh _ hD hF
  obtain ⟨Cr, eC, h, hCrI, heCφ, heCh⟩ := GlobalTheory.AcrisPrism.main l (ϖ.field a)
  have hev' := hev Cr eC h hCrI heCφ heCh g
  obtain ⟨ev, hevs⟩ := hev'
  have hG := GlobalTheory.T.galoisMatrix_eq_crystal_changeOfBasis_value l a e ↥(OL LL) ↥LL.1 (thetaW a LL) ϖ ι P (resF T (ϖ.field a)) (I.res (inclG (ϖ.field a)) (continuous_subtype_val.subtype_mk _)) E jA hR hIm oE hoE b hb PP p₀ p₁ Q c y hε Cr eC h heCh g ev hevs.1 hevs.2.1
  obtain ⟨Γ, hΓ, hΓeq⟩ := hG
  have hconv := hevs.2.2
  refine ⟨Γ, hΓ, fun i j r => ?_⟩
  have hG := GlobalTheory.CrysGal.comb_S (e := e) (c i j) (fun τ q => κ τ (y i j q))
    (fun k τ => ⟨_, hS τ j k i⟩) (fun q k τ => ⟨_, hSS τ (y i j q) k⟩)
    (fun k τ => (congrArg ((X : (↥LL.1)⟦X⟧) ^ k * ·) (hK τ k i j)).symm) (fun q k τ => rfl)
  exact GlobalTheory.CrysGal.conv_comb (thetaW a LL) ϖ g (c i j) (fun q => eC (ev.f (y i j q)))
    (fun q k τ => ⟨_, hSS τ (y i j q) k⟩) (fun k τ => ⟨_, hS τ j k i⟩) hG r (fun q => hconv (y i j q) r)
    _ (hΓeq i j)

end GlobalTheory.CrysGal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.H1fTSpanCardBound
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

noncomputable section

namespace GlobalTheory.H1fGeneratorsAlt

section Eval

variable {G V LL : Type} [Field LL] [AddCommGroup V] [Module LL V]

theorem exists_finset_eval (W : Submodule LL (G → V)) [Module.Finite LL ↥W] :
    ∃ s : Finset G, ∀ c ∈ W, (∀ g ∈ s, c g = 0) → c = 0 := by
  classical
  let Ks : Finset G → Submodule LL (G → V) := fun s =>
    W ⊓ ⨅ g ∈ s, LinearMap.ker (LinearMap.proj (R := LL) (φ := fun _ : G => V) g)
  have hmem : ∀ s c, c ∈ Ks s ↔ c ∈ W ∧ ∀ g ∈ s, c g = 0 := by
    intro s c
    simp [Ks, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker]
  obtain ⟨s, -, hs⟩ := (measure fun s => finrank LL ↥(Ks s)).wf.has_min Set.univ ⟨∅, trivial⟩
  refine ⟨s, fun c hc h0 => ?_⟩
  by_contra hne
  obtain ⟨g, hg⟩ : ∃ g, c g ≠ 0 := by
    by_contra h
    push_neg at h
    exact hne (funext h)
  have hlt : Ks (insert g s) < Ks s := by
    refine lt_of_le_of_ne (fun x hx => ?_) fun heq => ?_
    · rw [hmem] at hx ⊢
      exact ⟨hx.1, fun g' hg' => hx.2 g' (Finset.mem_insert_of_mem hg')⟩
    · have h1 : c ∈ Ks s := (hmem s c).2 ⟨hc, h0⟩
      rw [← heq, hmem] at h1
      exact hg (h1.2 g (Finset.mem_insert_self g s))
  haveI : Module.Finite LL ↥(Ks s) := Submodule.finiteDimensional_of_le inf_le_left
  exact hs (insert g s) trivial (Submodule.finrank_lt_finrank_of_lt hlt)

theorem fg_of_le_of_values {O : Type} [CommRing O] [IsNoetherianRing O] [Algebra O LL] [Module O V]
    [IsScalarTower O LL V] (W : Submodule LL (G → V)) [Module.Finite LL ↥W]
    (T : Submodule O V) (hT : T.FG) (N : Submodule O (G → V)) (hNW : N ≤ W.restrictScalars O)
    (hNT : ∀ c ∈ N, ∀ g, c g ∈ T) : N.FG := by
  classical
  obtain ⟨s, hs⟩ := exists_finset_eval W
  haveI : IsNoetherian O ↥T := isNoetherian_of_fg_of_noetherian T hT
  let φ : ↥N →ₗ[O] (↥s → ↥T) :=
    { toFun := fun c i => ⟨(c : G → V) i, hNT _ c.2 _⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hφ : Function.Injective φ := by
    intro c c' h
    apply Subtype.ext
    rw [← sub_eq_zero]
    refine hs _ (W.sub_mem (hNW c.2) (hNW c'.2)) fun g hg => ?_
    have := congrArg (fun f => ((f ⟨g, hg⟩ : ↥T) : V)) h
    simpa [φ, sub_eq_zero] using this
  haveI : IsNoetherian O ↥N := isNoetherian_of_injective φ hφ
  exact Module.Finite.iff_fg.1 inferInstance

end Eval

section Cohomology

open GlobalTheory.H1fGeneratorBoundAlt GlobalTheory.IndefiniteRowSideFullHecke.GaloisLatticeModuleActions

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {ρ : Representation LL G V}
    [TopologicalSpace G] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousConstSMul LL V]
    {O : Type} [CommRing O] [Algebra O LL] [IsDomain O] [IsDiscreteValuationRing O]
    [IsFractionRing O LL] [Module O V] [IsScalarTower O LL V]

theorem finite_Z1f_of_H1fV [FiniteDimensional LL V] (hρ : ∀ x, Continuous fun g => ρ g x)
    [Module.Finite LL (FiniteCohomology PD ρ)] : Module.Finite LL ↥(finiteCocycles PD ρ) := by
  have hle : B1 ρ ≤ finiteCocycles PD ρ := by
    rintro _ ⟨x, rfl⟩
    exact coboundary_mem_blochKatoCocycles PD hρ x
  haveI : Module.Finite LL ↥(B1 ρ) := LinearMap.finiteDimensional_range _
  haveI : Module.Finite LL ↥((B1 ρ).comap (finiteCocycles PD ρ).subtype) :=
    Module.Finite.equiv (Submodule.comapSubtypeEquivOfLe hle).symm
  haveI : IsNoetherian LL ↥(finiteCocycles PD ρ) :=
    isNoetherian_of_range_eq_ker ((B1 ρ).comap (finiteCocycles PD ρ).subtype).subtype
      (Submodule.mkQ _) (by rw [Submodule.range_subtype, Submodule.ker_mkQ])
  infer_instance

theorem finite_Z1fT_of (L : Lattice (O := O) ρ) [Module.Finite LL ↥(finiteCocycles PD ρ)] :
    Module.Finite O ↥(latticeFiniteCocycles PD L) :=
  Module.Finite.iff_fg.2 (fg_of_le_of_values (finiteCocycles PD ρ) L.T L.fg (latticeFiniteCocycles PD L) inf_le_right
    fun _ hc g => hc.1.2 g (Set.mem_univ g))

theorem exists_generators_H1fT' [FiniteDimensional LL V] (L : Lattice (O := O) ρ)
    (hρ : ∀ x, Continuous fun g => ρ g x) [Module.Finite LL (FiniteCohomology PD ρ)]
    {ϖ : O} (hϖ : Irreducible ϖ) :
    ∃ m : ℕ, GeneratedByAtMost (latticeFiniteCohomology PD L) m ∧
      m + finrank LL ↥(H0V ρ) ≤ finrank LL (FiniteCohomology PD ρ) + h0ModResidueDim L ϖ := by
  classical
  haveI hI : (Ideal.span {ϖ}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hϖ
  letI : Field (O ⧸ Ideal.span {ϖ}) := Ideal.Quotient.field _
  haveI := L.free
  haveI : Module.Finite O ↥L.T := Module.Finite.iff_fg.2 L.fg
  haveI := finite_Z1f_of_H1fV PD hρ
  haveI := finite_Z1fT_of PD L
  haveI : Module.IsTorsionFree O LL := inferInstance
  haveI : Module.IsTorsionFree O V := Module.IsTorsionFree.trans LL
  haveI : Module.Free O ↥(latticeFiniteCocycles PD L) := inferInstance
  obtain ⟨m, z, hz, hm⟩ := exists_generators (Ideal.span {ϖ}) (cobT PD L hρ)
  refine ⟨m, ⟨Finset.univ.image fun i => classT PD L (z i), ?_, ?_⟩, ?_⟩
  · have := congrArg (Submodule.map (classT PD L)) hz
    rw [Submodule.map_sup, ← ker_classT, Submodule.map_top, range_classT,
      (Submodule.map_le_iff_le_comap.2 le_rfl : (LinearMap.ker (classT PD L)).map (classT PD L) ≤ ⊥).antisymm bot_le,
      sup_bot_eq, Submodule.map_span, ← Set.range_comp] at this
    rw [← this, Finset.coe_image, Finset.coe_univ, Set.image_univ]
    rfl
  · simpa using Finset.card_image_le (s := Finset.univ) (f := fun i => classT PD L (z i))
  · haveI := finite_latMod L (Ideal.span {ϖ})
    have h1 := Submodule.finrank_mono (ker_redMap_le PD L hρ (Ideal.span {ϖ}))
    have h2 := finrank_bloch_kato_cocycles PD hρ
    have h3 := finrank_lattice L
    have h4 : finrank O ↥(latticeFiniteCocycles PD L) ≤ finrank LL ↥(finiteCocycles PD ρ) :=
      finrank_le_of_injective (W := ↥(finiteCocycles PD ρ))
        { toFun := fun c => ⟨c, c.2.2⟩
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl } fun _ _ h =>
          Subtype.ext (congrArg (fun c : ↥(finiteCocycles PD ρ) => (c : G → V)) h)
    have h5 : finrank (O ⧸ Ideal.span {ϖ}) ↥(LinearMap.ker (redMap (Ideal.span {ϖ}) (cobT PD L hρ))) ≤
      h0ModResidueDim L ϖ := h1
    omega

end Cohomology

open GlobalTheory.H1fGeneratorBoundAlt GlobalTheory.IndefiniteRowSideFullHecke.GaloisLatticeModuleActions

theorem h1fT_generators : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ T : LocLat ↥(GK K) ℚ_[l] LL O, IsDR (P.PD K) T.ρ → ∃ s : Finset (LatticeCohomology T.L), Submodule.span O (s : Set (LatticeCohomology T.L)) = latticeFiniteCohomology (P.PD K) T.L ∧ s.card + finrank LL ↥(H0V T.ρ) ≤ finrank LL (FiniteCohomology (P.PD K) T.ρ) + finrank LL T.V := by
  intro l _ P AI hTied K LL _ _ _ O _ _ hO T hDR
  have hH1f := (GlobalTheory.SeqDim.h1f_finrank l P AI hTied K LL O hO (toGRep T) hDR).1
  obtain ⟨⟨hD, hDVR, hF⟩, -⟩ := hO
  haveI : IsTopologicalAddGroup T.V := IsModuleTopology.topologicalAddGroup LL T.V
  haveI : Module.Finite LL (FiniteCohomology (P.PD K) T.ρ) := hH1f
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨m, ⟨s, hs, hc⟩, hm⟩ := exists_generators_H1fT' (P.PD K) T.L T.cont hϖ
  have h5 := h0_mod_uniformizer_le_rank T.L hϖ
  have h3 := finrank_lattice T.L
  exact ⟨s, hs, by omega⟩

end GlobalTheory.H1fGeneratorsAlt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSeriesVectorMulOfParahoricBlockCharVector
section
open Polynomial GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.GLp.Supp GlobalTheory.SerSys GlobalTheory.TypeLeaf Formalism.BasicNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders
open scoped Classical

noncomputable section

namespace GlobalTheory.SerSys.ParVec

open GlobalTheory.GLq.Opp GlobalTheory.SerSys.Opp MonoidAlgebra

private theorem inPar_tl_br_par_one {g : ℕ} [Fact g.Prime] {a b : ℕ} (B : Matrix (Fin a) (Fin b) (ZMod g)) :
    InPar a ((par finSumFinEquiv (1 : Gn g a) B 1 : Gn g (a + b)) : Mt g (a + b)) ∧
    tl a ((par finSumFinEquiv (1 : Gn g a) B 1 : Gn g (a + b)) : Mt g (a + b)) = 1 ∧
    br a b ((par finSumFinEquiv (1 : Gn g a) B 1 : Gn g (a + b)) : Mt g (a + b)) = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j hj hi
    obtain ⟨i', rfl⟩ := finSumFinEquiv.surjective i
    obtain ⟨j', rfl⟩ := finSumFinEquiv.surjective j
    rw [par_apply]
    rcases i' with i' | i'
    · have := i'.isLt
      simp at hi
      omega
    · rcases j' with j' | j'
      · simp
      · simp at hj
  · ext i j
    show entN _ i j = _
    rw [(entN_par (1 : Gn g a) B 1 i j).1 i.isLt j.isLt]
    simp [entN]
  · ext i j
    show entN _ (a + i) (a + j) = _
    rw [(entN_par (1 : Gn g a) B 1 i j).2.2.1]
    simp [entN]

theorem has_mul_of_isParVec : ∀ (g : ℕ) [Fact g.Prime] (S : Sys g) (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) ℚ_[g]) V) (a b : ℕ) (χ : (ZMod g)ˣ →* ℂˣ) (h f : (ZMod g)[X]) (v : V), n = a + b → CharIn S χ b h → IsParVec π a b χ v → actTop π a b (S.e a f) v ≠ 0 → Has S π (f * h) := by
  intro g _ S n V _ _ π a b χ h f v hn hχ hv hne
  subst hn
  obtain ⟨hvK, hrad, hy⟩ := hv
  let v' : fixK1 π := ⟨v, hvK⟩
  have hA : ∀ x : Gn g a, blk a b (a + b) x 1 = inA finSumFinEquiv x := fun x => blk_eq x 1
  have hB : ∀ y : Gn g b, blk a b (a + b) 1 y = inB finSumFinEquiv y := fun y => blk_eq 1 y
  let ρA : Representation ℂ (Gn g a) (fixK1 π) := (repK π).comp (inA (g := g) (finSumFinEquiv : Fin a ⊕ Fin b ≃ Fin (a + b)))
  let ρB : Representation ℂ (Gn g b) (fixK1 π) := (repK π).comp (inB (g := g) (finSumFinEquiv : Fin a ⊕ Fin b ≃ Fin (a + b)))
  let u : fixK1 π := ρA.asAlgebraHom (S.e a f) v'
  have hu : (u : V) = actTop π a b (S.e a f) v := by
    show ((ρA.asAlgebraHom (S.e a f) v' : fixK1 π) : V) = _
    rw [alg_apply, actTop, Submodule.coe_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hA]
    rfl
  have hv1 : ρB.asAlgebraHom (S.e b h) v' = v' := by
    rw [alg_apply]
    have hyv : ∀ y : Gn g b, ρB y v' = ((χ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ) • v' := by
      intro y
      apply Subtype.ext
      show π (lift g (a + b) (inB finSumFinEquiv y)) v = _
      rw [← hB]
      exact hy y
    simp_rw [hyv, smul_smul, ← Finset.sum_smul]
    have hev := (Loc.charIn_iff S χ b h).1 hχ
    simp only [Loc.ev] at hev
    rw [hev, one_smul]
  have key : (repK π).asAlgebraHom (S.e (a + b) (f * h)) u = u := by
    apply S.mul a b (a + b) rfl f h (fixK1 π) (repK π) u
    · intro u0 h0 h1 h2
      obtain ⟨B, rfl⟩ := eq_par (k := a) (l := b) u0 h0 h1 h2
      show (repK π) _ (ρA.asAlgebraHom (S.e a f) v') = ρA.asAlgebraHom (S.e a f) v'
      set_option synthInstance.maxHeartbeats 100000 in
        rw [alg_apply, map_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [map_smul]
      congr 1
      have hconj : par finSumFinEquiv 1 B 1 * inA finSumFinEquiv x =
          inA finSumFinEquiv x * par finSumFinEquiv 1 (((x⁻¹ : Gn g a) : Mt g a) * B) 1 := by
        show par finSumFinEquiv 1 B 1 * par finSumFinEquiv x 0 1 =
          par finSumFinEquiv x 0 1 * par finSumFinEquiv 1 (((x⁻¹ : Gn g a) : Mt g a) * B) 1
        rw [par_mul, par_mul]
        simp [← Matrix.mul_assoc]
      show (repK π) (par finSumFinEquiv 1 B 1) ((repK π) (inA finSumFinEquiv x) v') = (repK π) (inA finSumFinEquiv x) v'
      rw [← Module.End.mul_apply, ← map_mul, hconj, map_mul, Module.End.mul_apply]
      congr 1
      obtain ⟨r0, r1, r2⟩ := inPar_tl_br_par_one (g := g) (((x⁻¹ : Gn g a) : Mt g a) * B)
      exact Subtype.ext (hrad _ r0 r1 r2)
    · simp_rw [hA]
      have e2 : ∑ x, (S.e a f).coeff x • (repK π) (inA finSumFinEquiv x) u = ρA.asAlgebraHom (S.e a f) u := by
        rw [alg_apply]
        rfl
      rw [e2]
      show ρA.asAlgebraHom (S.e a f) (ρA.asAlgebraHom (S.e a f) v') = ρA.asAlgebraHom (S.e a f) v'
      rw [← Module.End.mul_apply, ← map_mul, S.idem]
    · simp_rw [hB]
      have e3 : ∑ y, (S.e b h).coeff y • (repK π) (inB finSumFinEquiv y) u = ρB.asAlgebraHom (S.e b h) u := by
        rw [alg_apply]
        rfl
      rw [e3]
      show ρB.asAlgebraHom (S.e b h) (ρA.asAlgebraHom (S.e a f) v') = ρA.asAlgebraHom (S.e a f) v'
      have hc : ρB.asAlgebraHom (S.e b h) (ρA.asAlgebraHom (S.e a f) v') =
          ρA.asAlgebraHom (S.e a f) (ρB.asAlgebraHom (S.e b h) v') := by
        simp only [ρA, ρB, comp_alg]
        rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul,
          (commute_AB finSumFinEquiv (S.e a f) (S.e b h)).eq]
      rw [hc, hv1]
  refine ⟨(u : V), u.2, ?_⟩
  rw [← repK_alg, key, hu]
  exact hne

end GlobalTheory.SerSys.ParVec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ImportsBisLast
section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.DesignUnconditional

theorem main : ∀ D : D7, GlobalTheory.CoefDuty.TakenAll D → Formalism.MainNotions.N.K.Rows.AllDesignConditions D :=
  _root_.GlobalTheory.DesignFromSize.main (GlobalTheory.Published.chebotarevDegreeOne_iff_cheb.mp GlobalTheory.Published.chebotarevDegreeOne')

end GlobalTheory.DesignUnconditional
end

