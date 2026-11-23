module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
public import Formalism.LocalToGlobal.Columns.AdelicLemmas
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0809
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0250
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0401
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0227
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0221
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealThetaIntertwinerAdjointIsRealThetaIntertwine
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0433
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0529
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridColumnParametersNegatedDataARPair
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealIntertwinerAdjointSmoothValues
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0198
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0453
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0380
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0295
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0511
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0532
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0374
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0474
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0480
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0485
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0528
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VertexLatticeEqAtMulSplitSupported
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0525
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0301

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCommonDenominatorSelfDualLevel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevelDenom

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem natCast_smul_mem_hatL_std (Λ : Submodule (𝓞 E) (Fin n → E)) (c : ℕ)
    (hc : ∀ y ∈ Λ, c • y ∈ Formalism.L2.Col.stdLat E n) (x : Fin n → E ⊗[F] Formalism.L2.Herm.Af F)
    (hx : x ∈ Formalism.L2.Herm.hatL (F := F) Λ) :
    (c : E ⊗[F] Formalism.L2.Herm.Af F) • x ∈ Formalism.UG.latS (F := F) (Formalism.L2.Herm.Af F) (Formalism.L2.Herm.intAf F E) (Formalism.L2.Col.stdLat E n) := by
  unfold Formalism.L2.Herm.hatL Formalism.UG.latS at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨l, hl, rfl⟩ := hy
    apply Submodule.subset_span
    refine ⟨c • l, hc l hl, ?_⟩
    funext i
    simp [nsmul_eq_mul, map_mul, map_natCast]
  | zero => simp
  | add a b _ _ ha hb => rw [smul_add]; exact add_mem ha hb
  | smul a y _ hy =>
    rw [smul_comm]
    exact Submodule.smul_mem _ a hy

theorem exists_nsmul_le_std (Λ : Submodule (𝓞 E) (Fin n → E)) (hfg : Λ.FG) :
    ∃ c : ℕ, 0 < c ∧ ∀ y ∈ Λ, c • y ∈ Formalism.L2.Col.stdLat E n := by
  obtain ⟨S, hS⟩ := hfg
  obtain ⟨c, hc, h⟩ := GlobalTheory.LatSandwich.exists_nsmul_le S (Formalism.L2.Pj.stdLat E n)
    (fun x _ => GlobalTheory.LatSandwich.exists_nsmul_mem_stdLat x)
  exact ⟨c, hc, fun y hy => h y (by rw [hS]; exact hy)⟩

theorem exists_nsmul_single_mem (Λ : Submodule (𝓞 E) (Fin n → E)) (hsp : Submodule.span E (Λ : Set (Fin n → E)) = ⊤) :
    ∃ c : ℕ, 0 < c ∧ ∀ j, c • (Pi.single j (1 : E) : Fin n → E) ∈ Λ := by
  classical
  obtain ⟨c, hc, h⟩ := GlobalTheory.LatSandwich.exists_nsmul_le (Finset.univ.image fun j : Fin n => (Pi.single j (1 : E) : Fin n → E)) Λ
    (fun x _ => GlobalTheory.LatSandwich.exists_nsmul_mem_of_span Λ hsp x)
  exact ⟨c, hc, fun j => h _ (Submodule.subset_span (by simp))⟩

end GlobalTheory.LevelDenom

namespace GlobalTheory.LevelDenom

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {n : ℕ}

theorem exists_denom_stab (hc : Formalism.BasicNotions.CMData F E) (J : Matrix (Fin n) (Fin n) E) (Λ : Submodule (𝓞 E) (Fin n → E))
    (hfg : Λ.FG) (hsp : Submodule.span E (Λ : Set (Fin n → E)) = ⊤) :
    ∃ b : ℕ, 0 < b ∧ ∀ k ∈ congLev hc J Λ ⊤, ∀ i j,
      (b : E ⊗[F] Formalism.L2.Herm.Af F) * k.1 i j ∈ Formalism.L2.Herm.intAf F E := by
  classical
  obtain ⟨a, ha, hae⟩ := exists_nsmul_single_mem Λ hsp
  obtain ⟨c, hc0, hce⟩ := exists_nsmul_le_std Λ hfg
  refine ⟨a * c, Nat.mul_pos ha hc0, fun k hk i j => ?_⟩
  have hs := hk.2.1
  have hzmem : (fun l => Formalism.UG.inclE (Formalism.L2.Herm.Af F) ((a • (Pi.single j (1 : E) : Fin n → E)) l)) ∈
      Formalism.L2.Herm.hatL (F := F) Λ := Submodule.subset_span ⟨_, hae j, rfl⟩
  have ez : (fun l => Formalism.UG.inclE (Formalism.L2.Herm.Af F) ((a • (Pi.single j (1 : E) : Fin n → E)) l)) =
      (a : E ⊗[F] Formalism.L2.Herm.Af F) • (Pi.single j 1 : Fin n → E ⊗[F] Formalism.L2.Herm.Af F) := by
    funext l
    by_cases e : l = j
    · subst e; simp [nsmul_eq_mul]
    · simp [Pi.single_eq_of_ne e, nsmul_eq_mul]
  rw [ez] at hzmem
  have hkz := (hs _).1 hzmem
  have h2 := natCast_smul_mem_hatL_std Λ c hce _ hkz
  rw [Formalism.L2.Col.mem_latS_std] at h2
  have h3 := h2 i
  rw [Matrix.mulVec_smul] at h3
  convert h3 using 1
  simp [Matrix.mulVec_single_one, mul_comm, mul_left_comm, mul_assoc]

end GlobalTheory.LevelDenom

namespace GlobalTheory.LevelDenom

theorem exists_denom_congLev : ∀ (D : D7) (V : HSp D) (Λ : Lat V), IsSelfDualC V Λ → ∃ b : ℕ, 0 < b ∧ ∀ k ∈ congLev D.sp.cm V.gram Λ ⊤, ∀ i j, (b : Lev.EAf D) * k.1 i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  intro D V Λ hΛ
  classical
  haveI := hΛ.1
  obtain ⟨c, hc, hcΛ⟩ := exists_nsmul_le_std Λ (Submodule.IsLattice.fg D.host.E Λ)
  have hsp : Submodule.span D.host.E (Λ : Set (Fin V.rank → D.host.E)) = ⊤ := by
    apply top_unique
    intro y _
    let t : Fin V.rank → D.host.E := fun i => ∑ j, V.gram i j * y j
    obtain ⟨d, hd, hdt⟩ := GlobalTheory.LatSandwich.exists_nsmul_mem_stdLat t
    have hy : (c * d) • y ∈ Λ := by
      apply (hΛ.2 _).2
      intro x hx
      have hcx := (GlobalTheory.LatSandwich.mem_stdLat_iff _).1 (hcΛ x hx)
      have hdt' := (GlobalTheory.LatSandwich.mem_stdLat_iff _).1 hdt
      have hint : IsIntegral ℤ (∑ i, star ((c • x) i) * (d • t) i) := by
        apply IsIntegral.sum
        intro i _
        exact ((hcx i).map (starRingEnd D.host.E).toIntAlgHom).mul (hdt' i)
      refine ⟨⟨_, hint⟩, ?_⟩
      change (∑ i, star ((c • x) i) * (d • t) i) = _
      simp only [t, Pi.smul_apply, nsmul_eq_mul, Nat.cast_mul, star_mul, star_natCast,
        Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    have hm : (c * d) • y ∈ Submodule.span D.host.E (Λ : Set (Fin V.rank → D.host.E)) :=
      Submodule.subset_span hy
    have hn : (c * d : D.host.E) ≠ 0 := by
      exact mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hc))
        (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hd))
    have hm' : (c * d : D.host.E) • y ∈ Submodule.span D.host.E (Λ : Set (Fin V.rank → D.host.E)) := by
      simpa [Nat.cast_mul, ← Nat.cast_smul_eq_nsmul D.host.E] using hm
    have := Submodule.smul_mem (Submodule.span D.host.E (Λ : Set (Fin V.rank → D.host.E))) (c * d : D.host.E)⁻¹ hm'
    simpa only [smul_smul, inv_mul_cancel₀ hn, one_smul] using this
  exact exists_denom_stab D.sp.cm V.gram Λ (Submodule.IsLattice.fg D.host.E Λ)
    hsp

end GlobalTheory.LevelDenom
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDownArrowRealIntertwinerWithAdjoint
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Chain.RealIt GlobalTheory.PairLift

namespace GlobalTheory.DownArrow

theorem itPair_gen (hD : GlobalTheory.Published.DiscreteSeriesCover) (hH : GlobalTheory.Published.HarishChandraModules) {D : D7} {V W : HSp D}
    {S S' : D.what₂.Tau → SPar} (M : DSModel V S) (M' : DSModel W S') (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ)
    (aS aT : D.what₂.Tau → ℚ) (hθ : IsInfFam θ)
    (hP : ∀ τ, ∃ (t : ℕ) (al be ga de : List ℚ), Formalism.MainNotions.SchurIrreducible.DataAR t al be ga de ∧
      S τ = dualPar (signed (al ++ be) (ga ++ de) (aT τ)) ∧
      S' τ = dualPar (signed (al ++ block t ++ de) (ga ++ be) (aS τ))) :
    ∃ It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M, It ≠ 0 ∧
      ∀ ω f, IsWeilExp ψ V W aS aT ω → IsVacVec ψ θ M M' f → IsItW θ M M' ω (ptOf ψ θ M M' f) It := by
  obtain ⟨X, hX, h1, h2⟩ := GlobalTheory.Chain.ItPairObj.exists_record hD hH
  have key : ∀ τ, (0 < V.rank ∧ 0 < W.rank) ∧ ∃ A, LocIt M M' τ (aS τ) (aT τ) A := fun τ => by
    obtain ⟨t, al, be, ga, de, hd, e1, e2⟩ := hP τ
    exact exists_locIt hX h1 h2 (_root_.GlobalTheory.modelsAreCoverSeries_of_hypotheses hD hH D) M M' τ hd e1 e2
  choose hr A hA using key
  obtain ⟨It, I, hI⟩ := GlobalTheory.T.exists_globalFockIntertwiner_tensor_realPlaces D V W _ _ M M' aS aT A GlobalTheory.Contr.contraction.2 (_root_.GlobalTheory.Chain.RealIt.GlueProof.glueLaw D _ _) hA
  refine ⟨It, hI.ne, fun ω f ⟨χS, χT, hω, he⟩ hf => ?_⟩
  have hv := fun τ => _root_.GlobalTheory.vacChar_of_record D V W _ _ M M' θ ψ χS χT ω f τ _ _ hθ hω (he τ).1 (he τ).2 hf
  exact isItW_of_globIt hθ hI hr (_root_.GlobalTheory.vacuumFock_all_records D V W _ _ M M' ψ θ hω.std hθ f hf).2.2.2.2 (fun τ => (hv τ).2.1)
    fun τ => (hv τ).2.2

theorem down_intertwiner_adj : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : GlobalTheory.ChiGrid.Consts}, GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → HostHyp D → ∀ {F : Face D A}, GlobalTheory.Hk3.Core R F → sc.cGap = 1 → ∀ {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (W : G'.Weil), W.Over R → ∀ G : GlobalTheory.Grid.GridPre R, G.IsSpaces → G.IsChars → SpAgree G W → (∀ i, i < D.R.m → ∀ κ : G'.CosAt i, IsThetaAt W.ψ (symplO _ _) (heisO W.ψ _ _) G.idem (latO (G'.pS (.chi i 0)) (G'.pT (.chi i 0)) (G'.latS (.chi i 0) : Set _) (G'.latT (.chi i 0) : Set _) fun _ => True) 1 (W.vac i) (cosInd G.idem κ) (W.cosVec i κ)) → ∀ i, i < D.R.m → ∀ (ω : GlobalTheory.Grid.WRep (G.P (i + 1)).V (G.P i).V) (f : WO (G.P (i + 1)).V (G.P i).V → ℂ), GlobalTheory.Grid.IsWeil R.ψ true (G.P (i + 1)).V (G.P i).V (G.chi (D.R.m - i)) (G.chi (D.R.m - i)) ω → GlobalTheory.Grid.IsVac R.ψ R.θ true (G.P (i + 1)) (G.P i) f → ∃ (It : GlobalTheory.Grid.Pol (G.P (i + 1)) (G.P i) →ₗ[ℂ] SmT (G.P (i + 1)).M →ₗ[ℂ] SmT (G.P i).M) (U : GlobalTheory.Grid.Pol (G.P (i + 1)) (G.P i) →ₗ⋆[ℂ] SmT (G.P i).M →ₗ[ℂ] SmT (G.P (i + 1)).M), GlobalTheory.Grid.IsIntw R.θ (G.P i).M (G.P (i + 1)).M ω.swap (GlobalTheory.Grid.fock R.ψ R.θ true (G.P (i + 1)) (G.P i) f) It ∧ (⟨ω, f, It⟩ : GlobalTheory.Grid.ArrT (G.P (i + 1)) (G.P i)).IsAdj U := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R sc hDC hHC hH F hC hgap G' W hW G hsp hch hag hcos i hi ω f hω hf
  have hθ : IsInfFam R.θ := hC.models.inf
  obtain ⟨ω₀, f₀, χ₀, e, hω₀, hχ₀, hf₀, htr⟩ :=
    _root_.GlobalTheory.AdjTr.downArrow_transport (G.P (i + 1)) (G.P i) R.ψ R.θ (G.chi (D.R.m - i)) ω f hθ hω hf
  have hm1 : 1 ≤ D.R.m - i := by omega
  have hm2 : D.R.m - i ≤ D.R.m := by omega
  have hexp : ∀ τ, HasInfExp D (G.chi (D.R.m - i)) τ (GlobalTheory.Grid.cen D τ (D.R.m - i)) :=
    (GlobalTheory.HeckeInfExp.hasInfExp_iff_hasInfQ D _ _ (fun τ => (GlobalTheory.Grid.cen D τ (D.R.m - i) : ℚ))
      (hch.tie _ hm1 hm2)).2 (hch.aux _ hm1 hm2).inf
  have hS : (G.P i).S = GlobalTheory.Grid.parP D i := (hsp.P i (by omega)).par
  have hS' : (G.P (i + 1)).S = GlobalTheory.Grid.parP D (i + 1) := (hsp.P (i + 1) (by omega)).par
  have hP : ∀ τ, ∃ (t : ℕ) (al be ga de : List ℚ), Formalism.MainNotions.SchurIrreducible.DataAR t al be ga de ∧
      (G.P i).S τ = dualPar (signed (al ++ be) (ga ++ de) (-(GlobalTheory.Grid.cen D τ (D.R.m - i) : ℚ))) ∧
      (G.P (i + 1)).S τ = dualPar (signed (al ++ block t ++ de) (ga ++ be) (-(GlobalTheory.Grid.cen D τ (D.R.m - i) : ℚ))) :=
    fun τ => by
      obtain ⟨al, be, ga, de, hd, e1, e2⟩ := _root_.GlobalTheory.NegPair.params D i hi τ
      exact ⟨_, al, be, ga, de, hd, by rw [hS]; exact e1, by rw [hS']; exact e2⟩
  obtain ⟨It, -, hIt⟩ := itPair_gen hDC hHC (G.P i).M (G.P (i + 1)).M R.θ R.ψ
    (fun τ => -(GlobalTheory.Grid.cen D τ (D.R.m - i) : ℚ)) (fun τ => -(GlobalTheory.Grid.cen D τ (D.R.m - i) : ℚ)) hθ hP
  have hωe : IsWeilExp R.ψ (G.P i).V (G.P (i + 1)).V (fun τ => -(GlobalTheory.Grid.cen D τ (D.R.m - i) : ℚ))
      (fun τ => -(GlobalTheory.Grid.cen D τ (D.R.m - i) : ℚ)) ω₀ :=
    ⟨χ₀, χ₀, hω₀, fun τ => ⟨hχ₀ τ _ (hexp τ), hχ₀ τ _ (hexp τ)⟩⟩
  have hI := hIt ω₀ f₀ hωe hf₀
  obtain ⟨Tp, hTp⟩ := _root_.GlobalTheory.AdjSmooth.adjoint_smooth (G.P i).M (G.P (i + 1)).M R.θ R.ψ _ _ ω₀ f₀ It hDC hHC hθ hP hωe hf₀ hI
  refine ⟨It ∘ₗ e.toLinearMap, Tp.comp e.toLinearMap, htr It hI, fun P v w => ?_⟩
  exact hTp (e P) v w

end GlobalTheory.DownArrow
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsGlobalScalarPrimeToConjPolarisationLattice
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftLevel

noncomputable section

namespace GlobalTheory.GenChoice

theorem exists_gen_avoid {R K ι : Type} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] (A : FractionalIdeal (nonZeroDivisors R) K) (hA : A ≠ 0) (Qs : Finset ι)
    (Q : ι → Ideal R) (hQ : ∀ i ∈ Qs, (Q i).IsPrime) (hQ0 : ∀ i ∈ Qs, Q i ≠ ⊥) :
    ∃ γ : K, γ ≠ 0 ∧ ∃ s : R, (∀ i ∈ Qs, s ∉ Q i) ∧
      (∀ c ∈ A, ∃ r : R, algebraMap R K r = algebraMap R K s * γ⁻¹ * c) ∧
      algebraMap R K s * γ ∈ A := by
  obtain ⟨a, I, ha, hAI⟩ := FractionalIdeal.exists_eq_spanSingleton_mul A
  have hI : I ≠ ⊥ := by
    rintro rfl
    apply hA
    rw [hAI, FractionalIdeal.coeIdeal_bot, mul_zero]
  have hinj := IsFractionRing.injective R K
  obtain ⟨g, hgI, hg0, hgQ⟩ : ∃ g ∈ I, g ≠ 0 ∧ ∀ i ∈ Qs, ¬ Ideal.span {g} ≤ I * Q i := by
    rcases Qs.eq_empty_or_nonempty with rfl | ⟨i0, hi0⟩
    · obtain ⟨g, hg, hg0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
      exact ⟨g, hg, hg0, by simp⟩
    · have hQp0 : (∏ i ∈ Qs, Q i) ≠ 0 := Finset.prod_ne_zero_iff.2 fun i hi => hQ0 i hi
      obtain ⟨g, hg⟩ := IsDedekindDomain.exists_sup_span_eq (Ideal.mul_le_left : I * (∏ i ∈ Qs, Q i) ≤ I)
        (mul_ne_zero hI hQp0)
      have hgI : g ∈ I := by
        rw [← hg]; exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self g)
      have key : ∀ i ∈ Qs, ¬ Ideal.span {g} ≤ I * Q i := by
        intro i hi h
        have hle : (∏ j ∈ Qs, Q j) ≤ Q i := Ideal.prod_le_inf.trans (Finset.inf_le hi)
        have h1 : I ≤ I * Q i := by
          calc I = I * (∏ j ∈ Qs, Q j) ⊔ Ideal.span {g} := hg.symm
            _ ≤ I * Q i := sup_le (Ideal.mul_mono_right hle) h
        have h2 : I * Q i = I * ⊤ := by
          rw [Ideal.mul_top]; exact le_antisymm Ideal.mul_le_left h1
        exact (hQ i hi).ne_top (mul_left_cancel₀ hI h2)
      refine ⟨g, hgI, ?_, key⟩
      rintro rfl
      apply key i0 hi0
      rw [Ideal.span_singleton_eq_bot.2 rfl]
      exact bot_le
  obtain ⟨J, hJ⟩ := Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hgI)
  have hJQ : ∀ i ∈ Qs, ¬ J ≤ Q i := fun i hi h => hgQ i hi (by rw [hJ]; exact Ideal.mul_mono_right h)
  obtain ⟨s, hsJ, hsQ⟩ : ∃ s ∈ J, ∀ i ∈ Qs, s ∉ Q i := by
    rcases Qs.eq_empty_or_nonempty with rfl | ⟨i0, hi0⟩
    · exact ⟨0, J.zero_mem, by simp⟩
    · by_contra hcon
      push_neg at hcon
      have hsub : (J : Set R) ⊆ ⋃ i ∈ (Qs : Set ι), (Q i : Set R) := by
        intro x hx
        obtain ⟨i, hi, hxi⟩ := hcon x hx
        exact Set.mem_biUnion hi hxi
      obtain ⟨i, hi, hle⟩ := (Ideal.subset_union_prime i0 i0 (fun i hi _ _ => hQ i hi)).1 hsub
      exact hJQ i hi hle
  have ha' : algebraMap R K a ≠ 0 := by
    intro h; exact ha (hinj (by rw [h, map_zero]))
  have hg' : algebraMap R K g ≠ 0 := by
    intro h; exact hg0 (hinj (by rw [h, map_zero]))
  refine ⟨(algebraMap R K a)⁻¹ * algebraMap R K g, mul_ne_zero (inv_ne_zero ha') hg', s, hsQ, ?_, ?_⟩
  · intro c hc
    rw [hAI, FractionalIdeal.mem_singleton_mul] at hc
    obtain ⟨y, hy, rfl⟩ := hc
    obtain ⟨x, hx, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hy
    have hxs : x * s ∈ Ideal.span {g} := by
      rw [hJ]; exact Ideal.mul_mem_mul hx hsJ
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 hxs
    refine ⟨r, ?_⟩
    have hr' : algebraMap R K r * algebraMap R K g = algebraMap R K x * algebraMap R K s := by
      rw [← map_mul, ← map_mul, hr]
    field_simp
    linear_combination hr'
  · rw [hAI, FractionalIdeal.mem_singleton_mul]
    refine ⟨algebraMap R K (s * g), FractionalIdeal.mem_coeIdeal_of_mem _ (I.mul_mem_left s hgI), ?_⟩
    rw [map_mul]
    field_simp

theorem exists_global_scalar_prime_to_conj_polarisationLattice : ∀ (D : D7) (n : ℕ) (Λ ΛT : Lt D.host.E n), IsAA Λ ΛT → ∀ P : Finset (Formalism.L2.DIV.Pl D.host.E), ∃ γ : D.host.E, γ ≠ 0 ∧ ∃ s : 𝓞 D.host.E, (∀ PP ∈ P, s ∉ conjI PP.asIdeal) ∧ (∀ v ∈ Λ, ((s : D.host.E) * γ⁻¹) • v ∈ ΛT) ∧ (∀ v ∈ ΛT, ((s : D.host.E) * γ) • v ∈ Λ) := by
  intro D n Λ ΛT h P
  obtain ⟨γ, hγ, s, hsQ, hint, hmem⟩ := exists_gen_avoid D.host.AA (GlobalTheory.FinPl.LocGen.AA_ne_zero D) P
    (fun PP => conjI PP.asIdeal)
    (fun PP _ => by rw [GlobalTheory.LiftIdeal.conjI_eq_map]; exact (GlobalTheory.LiftIdeal.isMaximal_map D PP).isPrime)
    (fun PP _ => by
      rw [GlobalTheory.LiftIdeal.conjI_eq_map, Ne, Ideal.map_eq_bot_iff_of_injective (f := ((GlobalTheory.LiftIdeal.conjO D : 𝓞 D.host.E →+* 𝓞 D.host.E))) (GlobalTheory.LiftIdeal.conjO D).injective]
      exact PP.ne_bot)
  refine ⟨γ, hγ, s, hsQ, ?_, ?_⟩
  · intro v hv
    have hv' := (h v).1 hv
    induction hv' using AddSubgroup.closure_induction with
    | mem u hu =>
      obtain ⟨c, hc, t, ht, rfl⟩ := hu
      obtain ⟨r, hr⟩ := hint c hc
      rw [smul_smul]
      have : ((s : D.host.E) * γ⁻¹ * c) = algebraMap (𝓞 D.host.E) D.host.E r := by
        rw [hr]
      rw [this, algebraMap_smul]
      exact ΛT.smul_mem r ht
    | zero => rw [smul_zero]; exact ΛT.zero_mem
    | add x y _ _ hx hy =>
      rw [smul_add]; exact ΛT.add_mem (hx ((h x).2 ‹_›)) (hy ((h y).2 ‹_›))
    | neg x _ hx =>
      rw [smul_neg]; exact ΛT.neg_mem (hx ((h x).2 ‹_›))
  · intro v hv
    rw [h]
    exact AddSubgroup.subset_closure ⟨(s : D.host.E) * γ, hmem, v, hv, rfl⟩

end GlobalTheory.GenChoice
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLieDerivativePolynomialFockSeesaw
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Classical

namespace GlobalTheory.OscLie

theorem exists_lie_deriv_pol : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {a a' : ℕ} (B : Base F E) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    IsTriple B G X om om' → ∀ γ ∈ Lines σ G.W,
    ∃ δ : SInf F (Fin a × Fin (a + a')) →ₗ[ℂ] SInf F (Fin a × Fin (a + a')), ∀ f ∈ G.M.Pol B.ψ B.emb,
      δ f ∈ G.M.Pol B.ψ B.emb ∧ ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f (δ f) := by
  intro F E _ _ _ _ _ σ a a' B G X om om' hT γ hγ
  choose T hT' using fun t : ℝ => _root_.GlobalTheory.ArchFactor.exists_archOperator B G X om om' hT (γ (Multiplicative.ofAdd t)) (hγ.2 _)
  have hvac : ∀ f₀, G.M.IsGauss B.ψ B.emb f₀ → f₀ ∈ G.M.Pol B.ψ B.emb := fun f₀ h =>
    Submodule.mem_sInf.2 fun N hN => hN.1 f₀ h
  have hstab : ∀ u, At (evI F) u → ∀ f ∈ G.M.Pol B.ψ B.emb, ∀ f₁ : SInf F (Fin a × Fin (a + a')),
      ActsD (evI F) (G.M.heisLine B.ψ u) f f₁ → f₁ ∈ G.M.Pol B.ψ B.emb := fun u hu f hf f₁ h =>
    Submodule.mem_sInf.2 fun N hN => hN.2 u hu f (Submodule.mem_sInf.1 hf N hN) f₁ h
  let N : Submodule ℂ (SInf F (Fin a × Fin (a + a'))) :=
    { carrier := {f | f ∈ G.M.Pol B.ψ B.emb ∧
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun p : ℝ × (Fin a × Fin (a + a') → mixedEmbedding.mixedSpace F) => T p.1 f p.2) ∧
        ∃ f' ∈ G.M.Pol B.ψ B.emb, ∀ x, HasDerivAt (fun t => T t f x) (f' x) 0}
      zero_mem' := ⟨zero_mem _, by simpa using contDiff_const, 0, zero_mem _, fun x => by simpa using hasDerivAt_const _ _⟩
      add_mem' := by
        rintro f g ⟨hf, hf1, f', hf', hf2⟩ ⟨hg, hg1, g', hg', hg2⟩
        refine ⟨add_mem hf hg, by simpa using hf1.add hg1, f' + g', add_mem hf' hg', fun x => ?_⟩
        show HasDerivAt (fun t => T t (f + g) x) ((f' + g') x) 0
        simp only [map_add (f := _), SchwartzMap.add_apply]
        exact (hf2 x).add (hg2 x)
      smul_mem' := by
        rintro c f ⟨hf, hf1, f', hf', hf2⟩
        refine ⟨Submodule.smul_mem _ c hf, by simpa using hf1.const_smul c, c • f', Submodule.smul_mem _ c hf', fun x => ?_⟩
        simpa using (hf2 x).const_mul c }
  have hPN : G.M.Pol B.ψ B.emb ≤ N := by
    refine sInf_le ⟨fun f₀ h => ?_, fun u hu f hf f₁ h => ?_⟩
    · exact ⟨hvac f₀ h, _root_.GlobalTheory.GaussLine.smooth_vacuum_line B G X om om' hT γ hγ T hT' f₀ h⟩
    · obtain ⟨hf0, hf1, hf2⟩ := hf
      exact ⟨hstab u hu f hf0 f₁ h, _root_.GlobalTheory.HeisOrbit.orbit_heis B G X om om' hT γ hγ T hT' u hu f hf0 hf1 hf2 f₁ h⟩
  have hex : ∀ f : G.M.Pol B.ψ B.emb, ∃ f' : SInf F (Fin a × Fin (a + a')), f' ∈ G.M.Pol B.ψ B.emb ∧
      ∀ x, HasDerivAt (fun t => T t (f : SInf F (Fin a × Fin (a + a'))) x) (f' x) 0 := fun f => by
    obtain ⟨-, -, f', hf', h⟩ := hPN f.2
    exact ⟨f', hf', h⟩
  choose d hdP hd using hex
  have huniq : ∀ (f g₁ g₂ : SInf F (Fin a × Fin (a + a'))), (∀ x, HasDerivAt (fun t => T t f x) (g₁ x) 0) →
      (∀ x, HasDerivAt (fun t => T t f x) (g₂ x) 0) → g₁ = g₂ := fun f g₁ g₂ h₁ h₂ =>
    SchwartzMap.ext fun x => (h₁ x).unique (h₂ x)
  let δ₀ : G.M.Pol B.ψ B.emb →ₗ[ℂ] SInf F (Fin a × Fin (a + a')) :=
    { toFun := d
      map_add' := fun f g => huniq _ _ _ (hd (f + g)) (fun x => by
        show HasDerivAt (fun t => T t ((f : SInf F (Fin a × Fin (a + a'))) + g) x) ((d f + d g) x) 0
        simp only [map_add (f := _), SchwartzMap.add_apply]
        exact (hd f x).add (hd g x))
      map_smul' := fun c f => huniq _ _ _ (hd (c • f)) (fun x => by simpa using (hd f x).const_mul c) }
  obtain ⟨δ, hδ⟩ := LinearMap.exists_extend δ₀
  have e : ∀ f (hf : f ∈ G.M.Pol B.ψ B.emb), δ f = d ⟨f, hf⟩ := fun f hf => by
    have := congrArg (fun φ => φ ⟨f, hf⟩) hδ
    exact this
  refine ⟨δ, fun f hf => ⟨by rw [e f hf]; exact hdP _, fun r hr x => ?_⟩⟩
  have h1 : ∀ t : ℝ, om (1, γ (Multiplicative.ofAdd t)) (tens (evI F) f r) = tens (evI F) (T t f) r :=
    fun t => hT' t f r hr
  simp only [h1]
  rw [e f hf]
  exact (hd ⟨f, hf⟩ _).mul_const (r x)

end GlobalTheory.OscLie
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRationalFiniteTranslate
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

noncomputable section

namespace GlobalTheory.MovedKappaDec

theorem eqAt_refl {D : D7} {N : ℕ} (q : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) : EqAt D q L L := by
  refine ⟨1, Nat.coprime_one_left q, ?_, ?_⟩ <;>
  · intro x hx
    rwa [Nat.cast_one, one_smul]

theorem eqAt_symm {D : D7} {N : ℕ} {q : ℕ} {L L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} (h : EqAt D q L L₁) :
    EqAt D q L₁ L := by
  obtain ⟨s, hcop, hto, hback⟩ := h
  exact ⟨s, hcop, hback, hto⟩

theorem eqAt_trans {D : D7} {N : ℕ} {q : ℕ} {L L₁ L₂ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} (h : EqAt D q L L₁)
    (h' : EqAt D q L₁ L₂) : EqAt D q L L₂ := by
  obtain ⟨a, ha, hL₁, hL₁'⟩ := h
  obtain ⟨b, hb, hL₂, hL₂'⟩ := h'
  refine ⟨a * b, Nat.Coprime.mul_left ha hb, fun x hx => ?_, fun x hx => ?_⟩
  ·
    have h1 : ((b : D.host.E) • ((a : D.host.E) • x)) ∈ L₂ := hL₂ _ (hL₁ x hx)
    rwa [smul_smul, mul_comm, ← Nat.cast_mul] at h1
  ·
    have h1 : ((a : D.host.E) • ((b : D.host.E) • x)) ∈ L := hL₁' _ (hL₂' x hx)
    rwa [smul_smul, ← Nat.cast_mul] at h1

end GlobalTheory.MovedKappaDec

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteUnitaryPointDarbouxTrivialArchimedeanStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteUnitaryPoint_darboux_trivial_archimedean : ∀ (D : D7) (X : HSp D) {k : ℕ} (e : Fin k ≃ Fin X.rank) {J : Matrix (Fin k) (Fin k) D.host.E}
    (hJ : J = D.host.xi0 • (X.gramᵀ).submatrix e e) (g : GA D X), g ∈ GfC X →
    ∀ u : AF D.host.F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) u →
      u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (σ := D.sp.cm.sig) (GlobalTheory.TripleRead.toUX X e hJ g) - 1) = 0 := by
  first | exact @GlobalTheory.GfCArch.gfc_arch | exact GlobalTheory.GfCArch.gfc_arch | (intros; apply GlobalTheory.GfCArch.gfc_arch <;> assumption)
end

