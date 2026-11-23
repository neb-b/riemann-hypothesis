module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0595
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0624
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0587
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0584
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0593
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0003
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0197
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0443
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0124
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0252
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TypePlacesDatumMoveToFullRank
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0051
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0829
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLowestKTypeFockMapThetaVectors
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0625
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0610
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridCoreNodeUnitReadingIntegralCongruent
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0865
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0332
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0627
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0618

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsNsmulSelfDualHomLatticeMemDepthLattice
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace GlobalTheory.BigRow

variable {D : D7}

private theorem smul_mem_hatMx_of_fr {m n : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    {Λ' : Submodule (𝓞 D.host.E) (Fin m → D.host.E)} {β : GL (Fin n) (Lev.EAf D)} {β' : GL (Fin m) (Lev.EAf D)}
    (hβ : Formalism.L2.DIV.IsFrame β Λ) (hβ' : Formalism.L2.DIV.IsFrame β' Λ') (𝔪 : Ideal (𝓞 D.host.E)) {a : AE D}
    (ha0 : infPart D a = 0) (ha : toEAf D a ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) {z : Mx D m n}
    (hz : ∀ i j, ∃ s ∈ Formalism.L2.DIV.idS D.host.F 𝔪, s.1 = GlobalTheory.FunObj.Comparison₂.fr β' β (z.map (toEAf D)) i j) :
    a • z ∈ hatMx (𝔪 • homLat Λ Λ') := by
  rw [GlobalTheory.FunObj.HatFrame.mem_hatMx_homLat_iff D Λ Λ' β β' hβ hβ' 𝔪]
  refine ⟨fun i j => by rw [Matrix.smul_apply, smul_eq_mul, map_mul, ha0, zero_mul], fun i j => ?_⟩
  obtain ⟨s, hs, hse⟩ := hz i j
  refine ⟨⟨toEAf D a, ha⟩ * s, Ideal.mul_mem_left _ _ hs, ?_⟩
  have e2 : GlobalTheory.FunObj.Comparison₂.fr β' β ((a • z).map (toEAf D)) i j = toEAf D a * GlobalTheory.FunObj.Comparison₂.fr β' β (z.map (toEAf D)) i j := by
    simp only [GlobalTheory.FunObj.Comparison₂.fr, Matrix.mul_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul,
      Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
  exact (congrArg (toEAf D a * ·) hse).trans e2.symm

private theorem exists_frames {m n : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    {Λ' : Submodule (𝓞 D.host.E) (Fin m → D.host.E)} (hΛ : Submodule.IsFullLattice D.host.E Λ)
    (hΛ' : Submodule.IsFullLattice D.host.E Λ') :
    ∃ β : GL (Fin n) (Lev.EAf D), ∃ β' : GL (Fin m) (Lev.EAf D), Formalism.L2.DIV.IsFrame β Λ ∧ Formalism.L2.DIV.IsFrame β' Λ' := by
  obtain ⟨β, hβ⟩ := GlobalTheory.AdelicFrame.exists_isFrame D.host.F Λ hΛ.fg (Submodule.IsFullLattice.span_eq_top (self := hΛ))
  obtain ⟨β', hβ'⟩ := GlobalTheory.AdelicFrame.exists_isFrame D.host.F Λ' hΛ'.fg (Submodule.IsFullLattice.span_eq_top (self := hΛ'))
  exact ⟨β, β', hβ, hβ'⟩

private theorem smul_mem_hatMx {m n : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    {Λ' : Submodule (𝓞 D.host.E) (Fin m → D.host.E)} (hΛ : Submodule.IsFullLattice D.host.E Λ)
    (hΛ' : Submodule.IsFullLattice D.host.E Λ') (𝔪 : Ideal (𝓞 D.host.E)) {a : AE D}
    (ha0 : infPart D a = 0) (ha : toEAf D a ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) {z : Mx D m n}
    (hz : z ∈ hatMx (𝔪 • homLat Λ Λ')) : a • z ∈ hatMx (𝔪 • homLat Λ Λ') := by
  obtain ⟨β, β', hβ, hβ'⟩ := exists_frames hΛ hΛ'
  rw [GlobalTheory.FunObj.HatFrame.mem_hatMx_homLat_iff D Λ Λ' β β' hβ hβ' 𝔪] at hz
  exact smul_mem_hatMx_of_fr hβ hβ' 𝔪 ha0 ha hz.2

theorem exists_nsmul_mem {K : Type} [Field K] [NumberField K] (I : FractionalIdeal (𝓞 K)⁰ K) {𝔪 : Ideal (𝓞 K)}
    (h𝔪 : 𝔪 ≠ ⊥) : ∃ N : ℕ, 0 < N ∧ ∀ a ∈ I, ∃ o ∈ 𝔪, (N : K) * a = algebraMap (𝓞 K) K o := by
  obtain ⟨d, hd, hI⟩ := I.isFractional
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  have hJ : Ideal.span {d} * 𝔪 ≠ ⊥ := mul_ne_zero (by simpa using hd0) h𝔪
  refine ⟨Ideal.absNorm (Ideal.span {d} * 𝔪), Nat.pos_of_ne_zero (by rwa [Ne, Ideal.absNorm_eq_zero_iff]), fun a ha => ?_⟩
  obtain ⟨z, hz, hzd⟩ := Ideal.mem_span_singleton_mul.1 (Ideal.absNorm_mem (Ideal.span {d} * 𝔪))
  obtain ⟨b, hb⟩ := hI a ha
  refine ⟨z * b, 𝔪.mul_mem_right _ hz, ?_⟩
  rw [← map_natCast (algebraMap (𝓞 K) K), ← hzd, map_mul, map_mul, hb, Algebra.smul_def]
  ring

private theorem selfDual_full (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (hΛ : IsSelfDualC V Λ) : Submodule.IsFullLattice D.host.E Λ := by
  haveI : Submodule.IsLattice D.host.E Λ := hΛ.1
  refine ⟨?_⟩
  obtain ⟨s, hs⟩ := hΛ.1.fg
  apply eq_top_iff.mpr
  intro y _
  let f : (Fin V.rank → D.host.E) → D.host.E := fun x =>
    ∑ i, ∑ j, star (x i) * V.gram i j * y j
  obtain ⟨a, ha⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 D.host.E)) s f
  have ha0 : (algebraMap (𝓞 D.host.E) D.host.E a) ≠ 0 := by
    exact (FaithfulSMul.algebraMap_injective _ _).ne (mem_nonZeroDivisors_iff_ne_zero.mp a.2)
  let P : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E) := {
    carrier := {x | ∃ b : 𝓞 D.host.E, (b : D.host.E) = (algebraMap (𝓞 D.host.E) D.host.E a) * f x}
    zero_mem' := by refine ⟨0, ?_⟩; simp [f]
    add_mem' := by
      rintro x z ⟨b, hb⟩ ⟨c, hc⟩
      refine ⟨b + c, ?_⟩
      change (b : D.host.E) + c = _
      rw [hb, hc]
      simp [f, map_add, add_mul, Finset.sum_add_distrib, mul_add]
    smul_mem' := by
      rintro c x ⟨b, hb⟩
      refine ⟨RingOfIntegers.mapRingHom (starRingEnd D.host.E) c * b, ?_⟩
      simp only [map_mul, hb, f, Pi.smul_apply, Algebra.smul_def, map_mul, RingOfIntegers.mapRingHom_apply, star_mul]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      change star (c : D.host.E) * _ = _
      ring }
  have hsP : (s : Set (Fin V.rank → D.host.E)) ⊆ P := by
    intro x hx
    obtain ⟨b, hb⟩ := ha x hx
    exact ⟨b, by simpa [Algebra.smul_def] using hb⟩
  have hy : (algebraMap (𝓞 D.host.E) D.host.E a) • y ∈ Λ := by
    apply (hΛ.2 _).2
    intro x hx
    have hxP : x ∈ P := (hs ▸ Submodule.span_le.mpr hsP) hx
    obtain ⟨b, hb⟩ := hxP
    refine ⟨b, ?_⟩
    rw [hb]
    dsimp only [f, Pi.smul_apply]
    simp only [smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hy' : (algebraMap (𝓞 D.host.E) D.host.E a) • y ∈ Submodule.span D.host.E (Λ : Set (Fin V.rank → D.host.E)) :=
    Submodule.subset_span hy
  have := (Submodule.span D.host.E (Λ : Set (Fin V.rank → D.host.E))).smul_mem
    (algebraMap (𝓞 D.host.E) D.host.E a)⁻¹ hy' 
  change (algebraMap (𝓞 D.host.E) D.host.E a)⁻¹ •
    ((algebraMap (𝓞 D.host.E) D.host.E a) • y) ∈ _ at this
  rw [← smul_assoc, smul_eq_mul, inv_mul_cancel₀ ha0, one_smul] at this
  exact this


theorem nsmul_tmul (N : ℕ) (α : AF D.host.F) (x : D.host.E) :
    (N • (α ⊗ₜ[D.host.F] x) : AE D) = α ⊗ₜ[D.host.F] ((N : D.host.E) * x) := by
  rw [← nsmul_eq_mul]
  exact (map_nsmul (TensorProduct.mk D.host.F (AF D.host.F) D.host.E α) N x).symm

theorem nsmul_mem_latO {S T : HSp D} (LS : Set (Fin S.rank → D.host.E)) (LT LT' : Set (Fin T.rank → D.host.E)) (N : ℕ)
    (h : ∀ t ∈ LT, (N : D.host.E) • t ∈ LT') (x : WO S T) (hx : x ∈ latO S T LS LT fun _ => True) :
    N • x ∈ latO S T LS LT' fun _ => True := by
  induction hx using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, h0, a, ha, s, hs, t, ht, rfl⟩ := hw
    refine AddSubgroup.subset_closure ⟨α, hα, h0, a, ha, s, hs, _, h t ht, ?_⟩
    ext i j
    simp only [Matrix.smul_apply, Matrix.of_apply, Pi.smul_apply, smul_eq_mul]
    rw [nsmul_tmul]
    congr 1
    ring
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

theorem nsmul_mem_hatMx {S T : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} (hS : IsSelfDualC S ΛS) {𝔪 : Ideal (𝓞 D.host.E)} {N : ℕ}
    (h : ∀ a ∈ D.host.AA, ∃ o ∈ 𝔪, (N : D.host.E) * a = algebraMap (𝓞 D.host.E) D.host.E o)
    (x : WO S T) (hx : x ∈ latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True) :
    N • x ∈ hatMx (𝔪 • homLat ΛS ΛT) := by
  induction hx using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, h0, a, ha, s, hs, t, ht, rfl⟩ := hw
    obtain ⟨o, ho, hoa⟩ := h a ha
    refine AddSubgroup.subset_closure ⟨α, hα, _,
      Submodule.smul_mem_smul ho (GlobalTheory.RowLatChi.genMap_one_mem_homLat hS hs ht), ?_⟩
    ext i j
    simp only [Matrix.smul_apply, Matrix.of_apply, GlobalTheory.LatVac.genMap]
    rw [nsmul_tmul, Algebra.smul_def, ← hoa]
    congr 1
    ring
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

theorem smul_mem_of_idLat {n : ℕ} {I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E}
    (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) {N : ℕ}
    (h : ∀ a ∈ I, ∃ o ∈ (⊤ : Ideal (𝓞 D.host.E)), (N : D.host.E) * a = algebraMap (𝓞 D.host.E) D.host.E o) :
    ∀ t ∈ idLat I Λ, (N : D.host.E) • t ∈ Λ := by
  intro t ht
  induction ht using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨s, hs, y, hy, rfl⟩ := hx
    obtain ⟨o, -, ho⟩ := h s hs
    rw [smul_smul, ho, algebraMap_smul]
    exact Λ.smul_mem o hy
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | smul o x _ hx => rw [smul_comm]; exact Λ.smul_mem o hx

theorem exists_nsmul_latBig_mem_latRow : OnStd fun {D} _ _ {sc} {G} _ _ => ∀ i, i < D.R.m → ∃ N : ℕ, 0 < N ∧ ∀ u ∈ latBig G i, N • u ∈ latRow G i := by
  intro D hq T L μ0 hL sc G W M hM F hF i hi
  obtain ⟨N₁, hN₁, h₁⟩ := exists_nsmul_mem (shiftId G) (𝔪 := ⊤) top_ne_bot
  obtain ⟨N₂, hN₂, h₂⟩ := exists_nsmul_mem D.host.AA (𝔪 := G.modul) (G.pl.modul_ne_bot sc)
  have hsd := GlobalTheory.CosetRow.selfDual_chi hL G i hi
  refine ⟨N₂ * N₁, Nat.mul_pos hN₂ hN₁, fun u hu => ?_⟩
  have k1 := nsmul_mem_latO _ _ (G.Λ (.grid i 0) : Set _) N₁ (smul_mem_of_idLat _ h₁) u hu
  have k2 : N₁ • u ∈ latO (negSp (G.V (.grid (i + 1) 0))) (G.V (.grid i 0)) (G.Λ (.grid (i + 1) 0) : Set _)
      (G.Λ (.grid i 0) : Set _) (fun _ => True) := GlobalTheory.RowLoc.mem_latO_negSp.2 k1
  rw [mul_smul]
  refine ⟨nsmul_mem k2 N₂, fun e he => ?_⟩
  have hprops := GlobalTheory.IdemSumIdeal.isIdemSum_props e G.pl.W0 (fun _ => 0) he
  exact smul_mem_hatMx (selfDual_full _ _ hsd.1) (selfDual_full _ _ hsd.2) G.modul hprops.1 hprops.2.1
    (nsmul_mem_hatMx hsd.1 h₂ _ k2)

end GlobalTheory.BigRow
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOpenCompactLevelThetaKernelSource
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
open scoped Topology

noncomputable section

namespace GlobalTheory.SrcLevel

theorem ker_finE {D : D7} (V : HSp D) {k : GA D V} (hk : Lev.finE V k = 1) : k ∈ GinfC V := by
  show finHom V k = 1
  have hinj : Function.Injective (Lev.swapAE D) :=
    (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).injective
  have h1 : Formalism.UG.bc (Lev.swapAE D) (finHom V k) = 1 := hk
  apply Units.ext
  have h2 := congrArg Units.val h1
  change Matrix.map (finHom V k).val (Lev.swapAE D) = 1 at h2
  refine Matrix.map_injective hinj ?_
  beta_reduce
  rw [h2, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]

theorem level_of_open {D : D7} (V : HSp D) (U : Subgroup (GA D V)) (hUo : IsOpen (U : Set (GA D V)))
    (hinf : GinfC V ≤ U) :
    ∃ K : Subgroup (GL (Fin V.rank) (Lev.EAf D)), GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.IsOpenCompactLevel V K ∧ ∀ k ∈ Lev.levA V K, k ∈ U := by
  obtain ⟨ho, hc⟩ := GlobalTheory.FunObj.congLev_open_compact V (GlobalTheory.AdelicU.SelfDual.isLattice_frameLat V) (𝔪 := ⊤) top_ne_bot
  set K₀ := congLev D.sp.cm V.gram (GlobalTheory.AdelicU.frameLat V) ⊤ with hK₀
  have hmem : ∀ k ∈ Lev.levA V (K₀ ⊓ U.map (Lev.finE V)), k ∈ U := by
    intro k hk
    obtain ⟨-, hkK⟩ := Lev.mem_levA.1 hk
    obtain ⟨k', hk'U, e⟩ := Subgroup.mem_map.1 hkK.2
    have h1 : k'⁻¹ * k ∈ GinfC V := ker_finE V (by rw [map_mul, map_inv, e, inv_mul_cancel])
    have h2 := U.mul_mem hk'U (hinf h1)
    rwa [mul_inv_cancel_left] at h2
  have hopen : IsOpen (((K₀ ⊓ U.map (Lev.finE V)).comap (Lev.finE V) : Subgroup (GA D V)) : Set (GA D V)) := by
    rw [Subgroup.comap_inf, Subgroup.coe_inf]
    exact ho.inter (Subgroup.isOpen_mono (Subgroup.le_comap_map _ _) hUo)
  refine ⟨K₀ ⊓ U.map (Lev.finE V), ⟨hopen, ?_⟩, hmem⟩
  have hcl : IsClosed ((Lev.levA V (K₀ ⊓ U.map (Lev.finE V)) : Subgroup (GA D V)) : Set (GA D V)) := by
    have e : ((Lev.levA V (K₀ ⊓ U.map (Lev.finE V)) : Subgroup (GA D V)) : Set (GA D V)) =
        (GfC V : Set (GA D V)) ∩ (((K₀ ⊓ U.map (Lev.finE V)).comap (Lev.finE V) : Subgroup (GA D V)) : Set (GA D V)) := rfl
    rw [e]
    exact (GlobalTheory.Ker.CongTop.isClosed_GfC V).inter (Subgroup.isClosed_of_isOpen _ hopen)
  refine hc.of_isClosed_subset hcl fun k hk => ?_
  obtain ⟨h1, h2⟩ := Lev.mem_levA.1 hk
  exact Lev.mem_levA.2 ⟨h1, h2.1⟩

theorem dat_fix : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {i j : Fin D.R.m}
    {A A' WW : HSp D} {X : Tri T A A' WW}, IsBottomTri W i j X → ∀ t : T,
    ∃ U : Subgroup (GA D A), IsOpen (U : Set (GA D A)) ∧ GinfC A ≤ U ∧
      ∀ k ∈ U, k ∈ GfC A → X.ω t (k, 1) X.vac = X.vac → X.ω t (k, 1) (X.f t) = X.f t := by
  intro D T L sc G W i j A A' WW X hX t
  obtain ⟨U, hUo, hUinf, hU⟩ := _root_.GlobalTheory.StdFstFix.stdFst_fixed hX t
  refine ⟨U, hUo, hUinf, fun k hkU hkf hv => ?_⟩
  obtain ⟨hΛ, hΦ⟩ := hU k hkU hkf
  have hW : IsWeilDatumO W.ψ (GlobalTheory.Grid.neg A) WW _ _ ((X.ω t).toSgn true) := hX.is.weil t
  have e1 : ∀ F, (X.ω t).toSgn true ((GlobalTheory.Grid.ofSgn true A).symm k, 1) F = X.ω t (k, 1) F := by
    intro F
    simp [GlobalTheory.Grid.WRep.toSgn]
  have hsdS : IsSelfDualC (GlobalTheory.Grid.neg A) X.rA.Λ := GlobalTheory.RowTest.isSelfDualC_neg' hX.is.rigA.1
  have hsdT : IsSelfDualC WW X.rW.Λ := hX.is.rigW.1
  have hmv := GlobalTheory.TypeMove.isThetaAt_move hW hsdS hsdT (GlobalTheory.PlaceDatum.idemSum_mul_self (hX.is.idem t))
    (GlobalTheory.PlaceDatum.infPart_idemSum (hX.is.idem t)) hΛ hX.is.isVac.2.theta (by rw [e1]; exact hv) (hX.is.fst t)
  have hf := hX.is.fst t
  obtain ⟨⟨T₀, hT₀⟩, hall⟩ := hmv
  obtain ⟨-, hall'⟩ := hf
  rw [← e1, hall T₀ hT₀, hall' T₀ hT₀]
  congr 1
  funext x
  exact hΦ x

theorem exists_level_ker : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {i j : Fin D.R.m}
    {A A' WW : HSp D} {X : Tri T A A' WW}, IsBottomTri W i j X → ∀ t : T,
    ∃ K : Subgroup (GL (Fin A.rank) (Lev.EAf D)), GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.IsOpenCompactLevel A K ∧
      ∀ (P : PolF D WW.rank A.rank) (h : GA D WW), ∀ k ∈ Lev.levA A K, ∀ g,
        X.ker W.ψ W.θ t P h (g * k) = X.ker W.ψ W.θ t P h g := by
  intro D T L sc G W i j A A' WW X hX t
  obtain ⟨U₁, hU₁o, hU₁inf, hU₁⟩ := _root_.GlobalTheory.VacFixNeg.exists_open_fix_vac_neg hX t
  obtain ⟨U₂, hU₂o, hU₂inf, hU₂⟩ := dat_fix hX t
  obtain ⟨K, hK, hKU⟩ := level_of_open A (U₁ ⊓ U₂) (hU₁o.inter hU₂o) (le_inf hU₁inf hU₂inf)
  refine ⟨K, hK, fun P h k hk g => ?_⟩
  have hkf : k ∈ GfC A := (Lev.mem_levA.1 hk).1
  have hkU := hKU k hk
  have hv := hU₁ k hkU.1 hkf
  have hf := hU₂ k hkU.2 hkf hv
  have hW : IsWeilDatumO W.ψ (GlobalTheory.Grid.neg A) WW _ _ ((X.ω t).toSgn true) := hX.is.weil t
  have hθ := hX.is.isVac.2.inf
  have hft : IsThetaFunO W.ψ (GlobalTheory.Grid.neg A) WW (X.f t) :=
    GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt hX.is.isVac.1 hθ (hX.is.fst t) hX.is.isVac.2.theta
  have hκ : (GlobalTheory.Grid.ofSgn true A).symm k ∈ GfC (GlobalTheory.Grid.neg A) :=
    (GlobalTheory.SgnIdent.mem_GfC_sgn true A _).2 (by rw [MulEquiv.apply_symm_apply]; exact hkf)
  have e1 : ∀ F, (X.ω t).toSgn true ((GlobalTheory.Grid.ofSgn true A).symm k, 1) F = X.ω t (k, 1) F := by
    intro F
    simp [GlobalTheory.Grid.WRep.toSgn]
  have key : X.ω t (k, 1) (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P) =
      pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P := by
    rw [← e1, GlobalTheory.OrientedHeis.om_fin_pureTensorO _ _ _ _ _ _ hW _ hθ _ hκ 1 (one_mem _) _ _ _ _ _ P hft, e1, hf]
  show X.ω t (g * k, h) _ 0 = X.ω t (g, h) _ 0
  have e : ((g * k, h) : GA D A × GA D WW) = (g, h) * (k, 1) := by simp
  rw [e, map_mul, Module.End.mul_apply, key]

end GlobalTheory.SrcLevel

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsWeightedAverageHaarLifted
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section

open scoped ComplexOrder

open GlobalTheory.ClassRegroup GlobalTheory.DefiniteClassAvg GlobalTheory.DefiniteClassReal

namespace GlobalTheory.RowTest.BottomClassSum

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {i j : Fin D.R.m}
    {A A' WW : HSp D} {X : Tri T A A' WW}

theorem weil' (hX : IsBottomTri W i j X) (t : T) :
    IsWeilDatumO W.ψ A' WW (L.mu t (j + 1) * L.eta ^ (rankV D i j % 2))
      ((L.mu t (j + 1) * L.eta ^ (rankV D i j % 2)) / (G.ch.chi (D.R.m - i) * L.eta ^ (rankV D i j % 2))) (X.ω' t) :=
  hX.is.weil' t

theorem theta' (hX : IsBottomTri W i j X) (t : T) (P : PolF D WW.rank A'.rank) :
    IsThetaFunO W.ψ A' WW (pureTensorO W.ψ W.θ A' WW X.rA'.s X.rW.s X.rA'.B X.rW.B (X.f' t) P) :=
  GlobalTheory.Chain.InnerSteps.theta_pureTensorO hX.is.isVac'.1 hX.is.isVac'.2.inf X.rA'.s X.rA'.B X.rW.s X.rW.B
    (GlobalTheory.ConstRatio.theta_f hX.is t).2 P

theorem ker'_left (hX : IsBottomTri W i j X) (t : T) (P : PolF D WW.rank A'.rank) (h : GA D WW) :
    ∀ γ ∈ GQ A', ∀ g, X.ker' W.ψ W.θ t P h (γ * g) = X.ker' W.ψ W.θ t P h g := by
  intro γ hγ g
  have hW := weil' hX t
  have hF := theta' hX t P
  show X.ω' t (γ * g, h) _ 0 = X.ω' t (g, h) _ 0
  have e : ((γ * g, h) : GA D A' × GA D WW) = (γ, 1) * (g, h) := by simp
  rw [e, map_mul, Module.End.mul_apply]
  exact hW.om_aut γ hγ 1 (one_mem _) _ (hW.om_pres _ _ hF)

theorem ker'_cont (hX : IsBottomTri W i j X) (t : T) (P : PolF D WW.rank A'.rank) (h : GA D WW) (x : GA D A') :
    Continuous fun k : GinfC A' => X.ker' W.ψ W.θ t P h (x * k) := by
  have hW := weil' hX t
  have hF := theta' hX t P
  exact (hW.om_cont _ hF 0).comp ((continuous_const.mul continuous_subtype_val).prodMk continuous_const)

theorem level_all [Finite T] (t₀ : T) (hX : IsBottomTri W i j X) :
    ∃ K : Subgroup (GL (Fin A'.rank) (Lev.EAf D)), GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.IsOpenCompactLevel A' K ∧
      ∀ (t : T) (P : PolF D WW.rank A'.rank) (h : GA D WW), ∀ k ∈ Lev.levA A' K, ∀ g,
        X.ker' W.ψ W.θ t P h (g * k) = X.ker' W.ψ W.θ t P h g := by
  choose K hK hinv using _root_.GlobalTheory.BotKerLevel.exists_level hX
  have hT := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D A'
  have hG := hT.2.2.2.2.1
  refine ⟨⨅ t, K t, ⟨?_, ?_⟩, fun t P h k hk g => hinv t P h k ?_ g⟩
  · have e : (((⨅ t, K t).comap (Lev.finE A') : Subgroup (GA D A')) : Set (GA D A')) =
        ⋂ t, (((K t).comap (Lev.finE A') : Subgroup (GA D A')) : Set (GA D A')) := by
      ext x; simp [Subgroup.mem_iInf]
    rw [e]
    exact isOpen_iInter_of_finite fun t => (hK t).1
  · have hcl : IsClosed ((((⨅ t, K t).comap (Lev.finE A') : Subgroup (GA D A')) : Set (GA D A'))) := by
      have e : (((⨅ t, K t).comap (Lev.finE A') : Subgroup (GA D A')) : Set (GA D A')) =
          ⋂ t, (((K t).comap (Lev.finE A') : Subgroup (GA D A')) : Set (GA D A')) := by
        ext x; simp [Subgroup.mem_iInf]
      rw [e]
      exact isClosed_iInter fun t => Subgroup.isClosed_of_isOpen _ (hK t).1
    have e2 : ((Lev.levA A' (⨅ t, K t) : Subgroup (GA D A')) : Set (GA D A')) =
        (Lev.levA A' (K t₀) : Set (GA D A')) ∩ (((⨅ t, K t).comap (Lev.finE A') : Subgroup (GA D A')) : Set (GA D A')) := by
      ext x
      simp only [SetLike.mem_coe, Set.mem_inter_iff, Lev.mem_levA, Subgroup.mem_comap]
      exact ⟨fun ⟨h1, h2⟩ => ⟨⟨h1, (Subgroup.mem_iInf.1 h2) t₀⟩, h2⟩, fun ⟨⟨h1, _⟩, h2⟩ => ⟨h1, h2⟩⟩
    rw [e2]
    exact (hK t₀).2.inter_right hcl
  · obtain ⟨hk1, hk2⟩ := Lev.mem_levA.1 hk
    exact Lev.mem_levA.2 ⟨hk1, (Subgroup.mem_iInf.1 hk2) t⟩

end GlobalTheory.RowTest.BottomClassSum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridCoreNodeUnitReadingIntegralCongruentStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexConjugate TensorProduct
open Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gridCoreNode_unitReading_integral_congruent : All fun {D} _ _ _ {G} W _ => ∀ i, i < D.R.m → ∀ e : AE D, IsIdemSum e G.pl.W0 →
    ∀ g : GA D (G.V (.core i)), ∀ a₁ ∈ GlobalTheory.ChiGrid.hatMx (G.modul • GlobalTheory.ChiGrid.homLat (G.Λ (.core i)) (G.Λ (.core i))), ∀ a₂ ∈ GlobalTheory.ChiGrid.hatMx (G.modul • GlobalTheory.ChiGrid.homLat (G.Λ (.core i)) (G.Λ (.core i))),
    e • ((1 : WO (G.V (.core i)) (G.V (.core i))) - a₁) = actO (G.V (.core i)) (G.V (.core i)) 1 g (e • (1 - a₂)) →
    ∀ x ∈ Formalism.L2.Herm.hatL (F := D.host.F) (G.Λ (.core i)),
      toEAf D e • ((Lev.finE (G.V (.core i)) g).1 *ᵥ x) ∈ Formalism.L2.Herm.hatL (F := D.host.F) (G.Λ (.core i)) ∧
      toEAf D e • (((Lev.finE (G.V (.core i)) g)⁻¹).1 *ᵥ x) ∈ Formalism.L2.Herm.hatL (F := D.host.F) (G.Λ (.core i)) ∧
      toEAf D e • ((Lev.finE (G.V (.core i)) g).1 *ᵥ x - x) ∈ Formalism.L2.Herm.hatL (F := D.host.F) (G.modul • G.Λ (.core i)) := by
  first | exact @GlobalTheory.UnitRead.unit_read | exact GlobalTheory.UnitRead.unit_read | (intros; apply GlobalTheory.UnitRead.unit_read <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.InversePartialFourierSumCompFromBlocksStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inversePartialFourierSum_comp_fromBlocks : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {A D₁ D₂ : Type} [Fintype A] [DecidableEq A] [Fintype D₁] [DecidableEq D₁] [Fintype D₂] [DecidableEq D₂]
    (ψ : AddChar k Circle) (ϖ : kˣ) (e : ℕ), IsUnif ϖ → HasConductor ψ 1 →
    ∀ Φ : Matrix A (D₁ ⊕ D₂) k → ℂ, HasDepth ϖ e (blockLat ϖ e (Assignment.one.block D₁ D₂)ᶜ) Φ →
    ∀ M₁ ∈ KO k D₁, ∀ M₂ ∈ KO k D₂, ∀ X : Matrix A (D₁ ⊕ D₂) k,
      invFourierSum ψ ϖ e (Assignment.one.block D₁ D₂)ᶜ (fun Z => Φ (Z * fromBlocks M₁.val 0 0 (invT M₂).val)) X =
        invFourierSum ψ ϖ e (Assignment.one.block D₁ D₂)ᶜ Φ (X * fromBlocks M₁.val 0 0 M₂.val) := by
  first | exact @GlobalTheory.BlockSubstFourier.invFourierSum_comp_fromBlocks | exact GlobalTheory.BlockSubstFourier.invFourierSum_comp_fromBlocks | (intros; apply GlobalTheory.BlockSubstFourier.invFourierSum_comp_fromBlocks <;> assumption)
end

