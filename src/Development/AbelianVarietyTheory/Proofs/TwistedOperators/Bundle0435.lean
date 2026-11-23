module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import GroundTheory.GlobalFields.TateThesis.AdelicCharDual
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1566
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0059
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0341
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0276
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0108
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0114
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0096
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0095
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0153
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0179
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Divisors.BplusOfEquivariant

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.StandardCharSeparatesIntegralFiniteAdeles
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace GlobalTheory.StdCharSep

variable {F : Type} [Field F] [NumberField F]

theorem trace_int_of_psi {ψ : AddChar (AF F) ℂ} (hψ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ) (x : F)
    (h : ψ (pairA F 0 (algebraMap F (Af F) x)) = 1) : ∃ z : ℤ, Algebra.trace ℚ F x = z := by
  rw [GlobalTheory.PsiNontriv.isStd_fin_rat hψ, Complex.exp_eq_one_iff] at h
  obtain ⟨n, hn⟩ := h
  refine ⟨n, ?_⟩
  have hne : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have h2 : ((Algebra.trace ℚ F x : ℚ) : ℂ) = ((n : ℚ) : ℂ) := by
    rw [mul_comm (2 * Real.pi * Complex.I : ℂ)] at hn
    push_cast
    exact mul_right_cancel₀ hne hn
  exact_mod_cast h2

theorem psi_of_trace_int {ψ : AddChar (AF F) ℂ} (hψ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ) (x : F)
    (h : ∃ z : ℤ, Algebra.trace ℚ F x = z) : ψ (pairA F 0 (algebraMap F (Af F) x)) = 1 := by
  obtain ⟨z, hz⟩ := h
  rw [GlobalTheory.PsiNontriv.isStd_fin_rat hψ, hz, Complex.exp_eq_one_iff]
  exact ⟨z, by push_cast; ring⟩

theorem psi_int_mul {ψ : AddChar (AF F) ℂ} (hψ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ) (s : F)
    (hs : ∀ a : 𝓞 F, ∃ z : ℤ, Algebra.trace ℚ F ((a : F) * s) = z)
    (w : Af F) (hw : ∀ v : HeightOneSpectrum (𝓞 F), w v ∈ v.adicCompletionIntegers F) :
    ψ (pairA F 0 (w * algebraMap F (Af F) s)) = 1 :=
  GlobalTheory.IntDense.addChar_eq_one_of_integral F ψ hψ.1 s (fun a => psi_of_trace_int hψ _ (hs a)) w hw

theorem mem_of_dual (k : F) (h : ∀ s : F, (∀ a : 𝓞 F, ∃ z : ℤ, Algebra.trace ℚ F ((a : F) * s) = z) →
    ∃ z : ℤ, Algebra.trace ℚ F (k * s) = z) : ∃ c : 𝓞 F, algebraMap (𝓞 F) F c = k := by
  have h1 : k ∈ FractionalIdeal.dual ℤ ℚ
      (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)) := by
    rw [FractionalIdeal.mem_dual (FractionalIdeal.dual_ne_zero ℤ ℚ (GlobalTheory.AdLat.one_ne_zero_fracIdeal F))]
    intro s hs
    rw [FractionalIdeal.mem_dual (GlobalTheory.AdLat.one_ne_zero_fracIdeal F)] at hs
    obtain ⟨z, hz⟩ := h s (fun a => by
      obtain ⟨y, hy⟩ := hs (a : F) ((FractionalIdeal.mem_one_iff _).2 ⟨a, rfl⟩)
      refine ⟨y, ?_⟩
      rw [Algebra.traceForm_apply] at hy
      rw [mul_comm, ← hy]
      simp)
    exact ⟨z, by rw [Algebra.traceForm_apply, hz]; simp⟩
  rw [FractionalIdeal.dual_dual] at h1
  exact (FractionalIdeal.mem_one_iff _).1 h1

theorem exists_sep : ∀ {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ →
    ∀ b : FiniteAdeleRing (𝓞 F) F, ¬ (∀ v : HeightOneSpectrum (𝓞 F), b v ∈ v.adicCompletionIntegers F) →
    ∃ s : F, ψ (((0 : InfiniteAdeleRing F), b * algebraMap F (FiniteAdeleRing (𝓞 F) F) s) : AF F) ≠ 1 ∧
      ∀ w : FiniteAdeleRing (𝓞 F) F, (∀ v : HeightOneSpectrum (𝓞 F), w v ∈ v.adicCompletionIntegers F) →
        ψ (((0 : InfiniteAdeleRing F), w * algebraMap F (FiniteAdeleRing (𝓞 F) F) s) : AF F) = 1 := by
  intro F _ _ ψ hψ b hb
  by_contra H
  obtain ⟨k, hk⟩ := GroundTheory.Global.exists_sub_mem_integralFiniteAdeles (R := 𝓞 F) b
  have hbk : b = algebraMap F (Af F) k + (b - algebraMap F (FiniteAdeleRing (𝓞 F) F) k) := by abel
  obtain ⟨o, ho⟩ := mem_of_dual k (fun s hs => by
    have hb1 : ψ (pairA F 0 (b * algebraMap F (Af F) s)) = 1 := by
      by_contra hne
      exact H ⟨s, hne, fun w hw => psi_int_mul hψ s hs w hw⟩
    have hc1 := psi_int_mul hψ s hs _ hk
    have e : pairA F 0 (b * algebraMap F (Af F) s) = pairA F 0 (algebraMap F (Af F) (k * s)) +
        pairA F 0 ((b - algebraMap F (FiniteAdeleRing (𝓞 F) F) k) * algebraMap F (Af F) s) := by
      refine Prod.ext (add_zero 0).symm ?_
      show b * algebraMap F (Af F) s = algebraMap F (Af F) (k * s) +
        (b - algebraMap F (FiniteAdeleRing (𝓞 F) F) k) * algebraMap F (Af F) s
      rw [map_mul]
      ring
    rw [e, AddChar.map_add_eq_mul, hc1, mul_one] at hb1
    exact trace_int_of_psi hψ _ hb1)
  apply hb
  intro v
  rw [hbk]
  refine add_mem ?_ (hk v)
  show ((k : F) : v.adicCompletion F) ∈ v.adicCompletionIntegers F
  rw [← ho]
  exact GroundTheory.Global.coe_algebraMap_mem_adicCompletionIntegers v o

end GlobalTheory.StdCharSep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SubMemLatticeCompletionOfSupportedPlaces
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open ValuativeRel

namespace GlobalTheory.LatBridge

theorem cut_mem_latV {D : D7} (S : HSp D) (L : GlobalTheory.FinPl.Lat S) (P : GlobalTheory.FinPl.Pl D → Prop)
    (u : Fin S.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)
    (hu : u ∈ latHat D.host.F D.host.E (L : Set (Fin S.rank → D.host.E))) :
    AddMonoidHom.compLeft (GlobalTheory.HatLatV.cutHom P) (Fin S.rank) u ∈ latV S L P := by
  refine AddSubgroup.closure_induction (fun y hy => ?_) ?_ (fun y z _ _ hy hz => ?_) (fun y _ hy => ?_) hu
  · obtain ⟨a, ha, x, hx, rfl⟩ := hy
    refine AddSubgroup.subset_closure ⟨GlobalTheory.SelfDualAt.indP P * a, ?_, ?_, 1, rfl, x, hx, ?_⟩
    · intro v
      rw [map_mul, GlobalTheory.SelfDualAt.evalV_indP]
      split_ifs
      · rw [one_mul]
        exact ha v
      · rw [zero_mul]
        exact zero_mem _
    · intro v hv
      rw [map_mul, GlobalTheory.SelfDualAt.evalV_indP, if_neg hv, zero_mul]
    · funext i
      rw [one_mul]
      exact GlobalTheory.HatLatV.cut_tmul P a (x i)
  · rw [map_zero]
    exact (latV S L P).zero_mem
  · rw [map_add (f := _)]
    exact (latV S L P).add_mem hy hz
  · rw [map_neg]
    exact (latV S L P).neg_mem hy

theorem finPart_mul_cut {D : D7} (P : GlobalTheory.FinPl.Pl D → Prop) (a : AE D) (ha : a ∈ idAt D P)
    (u : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) :
    finPart D (a * GlobalTheory.HatLatV.cut P u) = finPart D a * u := by

  have hfix := congrArg (finPart D) (GlobalTheory.HatLatV.cut_finPart P a ha)
  simp only [GlobalTheory.HatLatV.cut, Formalism.IndefR.Fin.LevelGroupLemmas.Lat.finPart_lift] at hfix
  rw [map_mul]
  simp only [GlobalTheory.HatLatV.cut, Formalism.IndefR.Fin.LevelGroupLemmas.Lat.finPart_lift]
  rw [← mul_assoc, mul_comm (finPart D a), hfix]


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in
theorem sub_mem_hatL : ∀ (D : D7) (S : HSp D) (P : GlobalTheory.FinPl.Pl D → Prop) (L L' : GlobalTheory.FinPl.Lat S) (g : GA D S), g ∈ grpAt S P →
  (∀ y : Fin S.rank → AE D, y ∈ latV S L P → (mt S g - 1) *ᵥ y ∈ latV S L' P) →
  ∀ x ∈ Formalism.L2.Herm.hatL (F := D.host.F) L, (Lev.finE S g).1 *ᵥ x - x ∈ Formalism.L2.Herm.hatL (F := D.host.F) L' := by
  intro D S P L L' g hg hmove x hx

  set u : Fin S.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E :=
    fun j => Algebra.TensorProduct.comm D.host.F D.host.E (Formalism.L2.Herm.Af D.host.F) (x j) with hu_def
  have hswap : ∀ j, Formalism.IndefR.Lev.swapAE D (u j) = x j := by
    intro j
    simp only [u, Formalism.IndefR.Lev.swapAE]
    generalize x j = z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul a b => simp
    | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb]
  have hu : u ∈ latHat D.host.F D.host.E (L : Set (Fin S.rank → D.host.E)) := by
    rw [GlobalTheory.LevSplit.latHat_iff]
    convert hx using 1
    funext j
    exact hswap j

  have hI : ∀ i j, (Formalism.L2.Theta.mt S g - 1) i j ∈ idAt D P :=
    (GlobalTheory.FrameAt.mem_congGrp S (idAt D P) g).1 hg
  have hmem := GlobalTheory.LatVHat.latV_mem_hatL D S L' P _ (hmove _ (cut_mem_latV S L P u hu))
  have hcut : ∀ z, GlobalTheory.HatLatV.cutHom P z = GlobalTheory.HatLatV.cut P z := fun _ => rfl
  have hlhs : (Lev.finE S g).1 *ᵥ x - x = ((Formalism.L2.Theta.mt S g - 1).map (GlobalTheory.LevSplit.finSw D)) *ᵥ x := by
    rw [GlobalTheory.LevSplit.finE_val, Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _), Matrix.sub_mulVec,
      Matrix.one_mulVec]
  rw [hlhs]
  convert hmem using 1
  funext i
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum,
    AddMonoidHom.compLeft_apply, Function.comp_apply, hcut]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [finPart_mul_cut P _ (hI i j), map_mul, hswap]
  rfl

end GlobalTheory.LatBridge
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoPlaceComponentsFiniteAdelicUnitary
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Filter Topology

namespace GlobalTheory.PlaceLimit

theorem sum_placeIdem {D : D7} {ε : HeightOneSpectrum (𝓞 D.host.F) → AF D.host.F}
    (hε : ∀ v, IsPlaceIdem D v (ε v)) (A : Finset (HeightOneSpectrum (𝓞 D.host.F))) :
    ∑ v ∈ A, ε v = pairA D.host.F 0 (GlobalTheory.LevelClosure.cutIdem A) := by
  choose α h0 h1 h2 using hε
  refine Prod.ext ?_ ?_
  · change fstA D.host.F (∑ v ∈ A, ε v) = 0
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_eq_zero fun v _ => by rw [h0]; rfl
  · change sndA D.host.F (∑ v ∈ A, ε v) = GlobalTheory.LevelClosure.cutIdem A
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine RestrictedProduct.ext _ _ fun w => ?_
    change Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F w (∑ v ∈ A, sndA D.host.F (ε v)) =
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F w (GlobalTheory.LevelClosure.cutIdem A)
    have e : ∀ v, sndA D.host.F (ε v) = α v := fun v => by rw [h0]; rfl
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [e]
    by_cases hw : w ∈ A
    · rw [GlobalTheory.LevelClosure.evalV_cutIdem_of_mem hw,
        Finset.sum_eq_single w (fun v _ hv => h2 v w (Ne.symm hv)) (fun h => absurd hw h), h1]
    · rw [GlobalTheory.LevelClosure.evalV_cutIdem_of_notMem hw]
      exact Finset.sum_eq_zero fun v hv => h2 v w fun h => hw (h ▸ hv)

theorem pair_cutIdem_mul_self {F : Type} [Field F] [NumberField F] (A : Finset (HeightOneSpectrum (𝓞 F))) :
    pairA F 0 (GlobalTheory.LevelClosure.cutIdem A) * pairA F 0 (GlobalTheory.LevelClosure.cutIdem A) =
      pairA F 0 (GlobalTheory.LevelClosure.cutIdem A) := by
  refine Prod.ext (mul_zero _) ?_
  change GlobalTheory.LevelClosure.cutIdem A * GlobalTheory.LevelClosure.cutIdem A = GlobalTheory.LevelClosure.cutIdem A
  refine RestrictedProduct.ext _ _ fun w => ?_
  change Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F w (GlobalTheory.LevelClosure.cutIdem A * GlobalTheory.LevelClosure.cutIdem A) =
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F w (GlobalTheory.LevelClosure.cutIdem A)
  rw [map_mul]
  by_cases hw : w ∈ A
  · rw [GlobalTheory.LevelClosure.evalV_cutIdem_of_mem hw, one_mul]
  · rw [GlobalTheory.LevelClosure.evalV_cutIdem_of_notMem hw, zero_mul]

theorem tendsto_cut_mul {D : D7} {z : AE D} (hz : infPart D z = 0) :
    Tendsto (fun A : Finset (HeightOneSpectrum (𝓞 D.host.F)) =>
      algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (GlobalTheory.LevelClosure.cutIdem A)) * z) atTop (𝓝 z) := by
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  have h : Tendsto (fun A : Finset (HeightOneSpectrum (𝓞 D.host.F)) =>
      pairA D.host.F 0 (GlobalTheory.LevelClosure.cutIdem A)) atTop (𝓝 (pairA D.host.F 0 1)) := by
    have := GlobalTheory.LevelClosure.tendsto_cutIdem_mul (1 : Af D.host.F)
    simp only [mul_one] at this
    exact (tendsto_const_nhds (x := (0 : Ainf D.host.F))).prodMk_nhds this
  have h2 := h.smul_const z
  have e : pairA D.host.F 0 1 • z = z := by
    rw [Algebra.smul_def, mul_comm]
    exact GlobalTheory.PlaceDatum.mul_pair_one hz
  rw [e] at h2
  simpa only [Algebra.smul_def] using h2

theorem tendsto_mix {D : D7} (V : HSp D) {g : GA D V} (hg : g ∈ GfC V) :
    Tendsto (fun A : Finset (HeightOneSpectrum (𝓞 D.host.F)) =>
      algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (GlobalTheory.LevelClosure.cutIdem A)) • Formalism.L2.Theta.mt V g +
        (1 - algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (GlobalTheory.LevelClosure.cutIdem A))) •
          (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D))) atTop (𝓝 (Formalism.L2.Theta.mt V g)) := by
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  haveI : ContinuousAdd (AE D) := IsModuleTopology.toContinuousAdd (AF D.host.F) _
  refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
  have h1 : infPart D (Formalism.L2.Theta.mt V g i j) = (1 : Matrix (Fin V.rank) (Fin V.rank) _) i j :=
    congrArg (fun u : GL (Fin V.rank) (Ainf D.host.F ⊗[D.host.F] D.host.E) => u.1 i j) (show infHom V g = 1 from hg)
  have h2 : infPart D (Formalism.L2.Theta.mt V g i j - (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j) = 0 := by
    rw [RingHom.map_sub, h1, sub_eq_zero, Matrix.one_apply, Matrix.one_apply]
    split_ifs
    · exact (RingHom.map_one _).symm
    · exact (RingHom.map_zero _).symm
  have h3 := (tendsto_cut_mul h2).add_const ((1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j)
  rw [sub_add_cancel] at h3
  refine h3.congr fun A => ?_
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

theorem eq_mix_of_mul {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n] {f : R} (hf : f * f = f)
    {a a' b b' : Matrix n n R} (ha : a * a' = 1) (hb : b' * b = 1)
    (h : b = f • a + (1 - f) • (1 : Matrix n n R)) : b' = f • a' + (1 - f) • (1 : Matrix n n R) := by
  have : b * (f • a' + (1 - f) • (1 : Matrix n n R)) = 1 := by
    rw [h, GlobalTheory.IdemSupport.mix_mul hf, ha, one_mul, GlobalTheory.IdemSupport.mix_self]
  calc b' = b' * (b * (f • a' + (1 - f) • (1 : Matrix n n R))) := by rw [this, mul_one]
    _ = _ := by rw [← mul_assoc, hb, one_mul]

theorem tendsto_components : ∀ (D : D7) (V : HSp D) (g : GA D V), g ∈ GfC V → ∀ (ε : HeightOneSpectrum (𝓞 D.host.F) → AF D.host.F), (∀ v, IsPlaceIdem D v (ε v)) → ∀ gs : Finset (HeightOneSpectrum (𝓞 D.host.F)) → GA D V, (∀ A, Formalism.L2.Theta.mt V (gs A) = algebraMap (AF D.host.F) (AE D) (∑ v ∈ A, ε v) • Formalism.L2.Theta.mt V g + (1 - algebraMap (AF D.host.F) (AE D) (∑ v ∈ A, ε v)) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D))) → Filter.Tendsto gs Filter.atTop (nhds g) := by
  intro D V g hg ε hε gs hgs
  simp only [sum_placeIdem hε] at hgs
  have hinv : ∀ A, Formalism.L2.Theta.mt V (gs A)⁻¹ =
      algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (GlobalTheory.LevelClosure.cutIdem A)) • Formalism.L2.Theta.mt V g⁻¹ +
        (1 - algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (GlobalTheory.LevelClosure.cutIdem A))) •
          (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) := fun A =>
    eq_mix_of_mul (by rw [← RingHom.map_mul, pair_cutIdem_mul_self])
      (by rw [← GlobalTheory.IdemSupport.mt_mul, mul_inv_cancel, GlobalTheory.IdemSupport.mt_one])
      (by rw [← GlobalTheory.IdemSupport.mt_mul, inv_mul_cancel, GlobalTheory.IdemSupport.mt_one]) (hgs A)
  have h1 := (tendsto_mix V hg).congr fun A => (hgs A).symm
  have h2 := (tendsto_mix V (inv_mem hg)).congr fun A => (hinv A).symm
  refine tendsto_subtype_rng.2 (Units.isEmbedding_embedProduct.tendsto_nhds_iff.2 ?_)
  exact h1.prodMk_nhds ((MulOpposite.continuous_op.tendsto _).comp h2)

end GlobalTheory.PlaceLimit

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryEmbeddingContinuousMulRational
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.UnitaryEmbeddingProperties

def ex {R : Type} [CommRing R] {n r : ℕ} (P : Matrix (Fin n) (Fin r) R) (Q : Matrix (Fin r) (Fin n) R)
    (h : Matrix (Fin r) (Fin r) R) : Matrix (Fin n) (Fin n) R :=
  1 + P * (h - 1) * Q

section Gen

variable {R : Type} [CommRing R] {n r : ℕ} (P : Matrix (Fin n) (Fin r) R) (Q : Matrix (Fin r) (Fin n) R)

theorem ex_mul_P (hQP : Q * P = 1) (h : Matrix (Fin r) (Fin r) R) : ex P Q h * P = P * h := by
  rw [ex, Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc, hQP, Matrix.mul_one, Matrix.mul_sub, Matrix.mul_one,
    add_sub_cancel]

theorem ex_mul_N (hQP : Q * P = 1) (h : Matrix (Fin r) (Fin r) R) : ex P Q h * (1 - P * Q) = 1 - P * Q := by
  have e : Q * (1 - P * Q) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hQP, Matrix.one_mul, sub_self]
  rw [ex, Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc (P * (h - 1)), e, Matrix.mul_zero, add_zero]

theorem ex_mul (hQP : Q * P = 1) (a b : Matrix (Fin r) (Fin r) R) : ex P Q (a * b) = ex P Q a * ex P Q b := by
  have e3 : P * (a - 1) * Q * (P * (b - 1) * Q) = P * ((a - 1) * (b - 1)) * Q := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Q P, hQP, Matrix.one_mul]
  have e4 : a * b - 1 = (a - 1) + (b - 1) + (a - 1) * (b - 1) := by noncomm_ring
  rw [ex, ex, ex, Matrix.add_mul, Matrix.one_mul, Matrix.mul_add, Matrix.mul_one, e3, e4]
  simp only [Matrix.mul_add, Matrix.add_mul]
  abel

theorem ex_one : ex P Q 1 = 1 := by simp [ex]

theorem ex_map {R' : Type} [CommRing R'] (φ : R →+* R') (h : Matrix (Fin r) (Fin r) R) :
    (ex P Q h).map φ = ex (P.map φ) (Q.map φ) (h.map φ) := by
  simp only [ex, Matrix.map_add _ (map_add φ), Matrix.map_mul, Matrix.map_sub _ (map_sub φ),
    Matrix.map_one _ (map_zero φ) (map_one φ)]

end Gen

variable {D : D7} {A B : HSp D} {c : ℕ} {ε : D.host.E}

def qM (d : HermitianOrthogonalExtensionData A B c ε) : Matrix (Fin A.rank) (Fin B.rank) D.host.E :=
  A.gram⁻¹ * (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (frameMat B A d.ι) * B.gram)

theorem qM_mul (d : HermitianOrthogonalExtensionData A B c ε) : qM d * frameMat B A d.ι = 1 := by
  rw [qM, Matrix.mul_assoc, GlobalTheory.AutFunCounterexample.gram_pull B A d.ι d.isom,
    Matrix.nonsing_inv_mul _ (GlobalTheory.AutFunCounterexample.gram_det_ne A).isUnit]

theorem qM_mul_map {R : Type} [CommRing R] (φ : D.host.E →+* R) (d : HermitianOrthogonalExtensionData A B c ε) :
    (qM d).map φ * (frameMat B A d.ι).map φ = 1 := by
  rw [← Matrix.map_mul, qM_mul, Matrix.map_one _ (map_zero φ) (map_one φ)]

theorem unitaryEmbedding_matrix_formula (d : HermitianOrthogonalExtensionData A B c ε) (h : GA D A) :
    (matHom B (stabilizerEmbedding d h)).1 = ex ((frameMat B A d.ι).map (incA D)) ((qM d).map (incA D)) (matHom A h).1 := by
  have hr := (embRel_iff d h _).2 rfl
  set P := frameMat B A d.ι
  set C := Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) P * B.gram
  have hG : C * P = A.gram := GlobalTheory.AutFunCounterexample.gram_pull B A d.ι d.isom
  set N : Matrix (Fin B.rank) (Fin B.rank) D.host.E := 1 - P * qM d with hN
  have hC : C * N = 0 := by
    rw [hN, qM, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hG,
      Matrix.mul_nonsing_inv _ (GlobalTheory.AutFunCounterexample.gram_det_ne A).isUnit, Matrix.one_mul, sub_self]
  have h1 : (matHom B (stabilizerEmbedding d h)).1 * N.map (incA D) = N.map (incA D) := by
    ext i j
    exact congr_fun (hr.2 (fun k => N k j) (by funext k; exact congr_fun (congr_fun hC k) j)) i
  have hNm : N.map (incA D) = (1 : Matrix (Fin B.rank) (Fin B.rank) (AF D.host.F ⊗[D.host.F] D.host.E)) -
      HMul.hMul (P.map (incA D)) ((qM d).map (incA D)) := by
    rw [hN, Matrix.map_sub _ (map_sub _), Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
  refine GlobalTheory.AutFunCounterexample.split_gen (incA D) P (qM d) _ _ ?_ ?_
  · rw [h1, hNm, ex_mul_N _ _ (qM_mul_map _ d)]
  · rw [hr.1, ex_mul_P _ _ (qM_mul_map _ d)]

theorem unitaryEmbedding_mul (d : HermitianOrthogonalExtensionData A B c ε) (g h : GA D A) : stabilizerEmbedding d (g * h) = stabilizerEmbedding d g * stabilizerEmbedding d h := by
  apply GlobalTheory.AutFunCounterexample.GA_ext
  rw [map_mul, Units.val_mul, unitaryEmbedding_matrix_formula, unitaryEmbedding_matrix_formula, unitaryEmbedding_matrix_formula, map_mul, Units.val_mul,
    ex_mul _ _ (qM_mul_map _ d)]

theorem unitaryEmbedding_rational (d : HermitianOrthogonalExtensionData A B c ε) (γ : GA D A) (hγ : γ ∈ GQ A) : stabilizerEmbedding d γ ∈ GQ B := by
  obtain ⟨γE, hγE, e⟩ := Subgroup.mem_subgroupOf.1 hγ
  have q2 : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (frameMat B A d.ι) * B.gram = A.gram * qM d := by
    rw [qM, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (GlobalTheory.AutFunCounterexample.gram_det_ne A).isUnit, Matrix.one_mul]
  set P := frameMat B A d.ι
  set Q := qM d
  have q3 : Q * P = 1 := qM_mul d
  have q1 : B.gram * P = Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Q * A.gram := by
    have := congrArg (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E)) q2
    rwa [Formalism.UG.cT_mul, Formalism.UG.cT_mul, GlobalTheory.AutFunCounterexample.gram_herm, GlobalTheory.AutFunCounterexample.cT_cT,
      GlobalTheory.AutFunCounterexample.gram_herm] at this
  let γ' : GL (Fin B.rank) D.host.E := ⟨ex P Q γE, ex P Q (γE⁻¹ : GL (Fin A.rank) D.host.E),
    by rw [← ex_mul _ _ q3, Units.mul_inv, ex_one], by rw [← ex_mul _ _ q3, Units.inv_mul, ex_one]⟩
  have hu : γ' ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) B.gram :=
    GlobalTheory.AutFunCounterexample.ext_unitary _ B.gram A.gram P Q q1 q2 q3 _ hγE
  refine Subgroup.mem_subgroupOf.2 ⟨γ', hu, Units.ext ?_⟩
  have hA : (matHom A γ).1 = (γE : Matrix (Fin A.rank) (Fin A.rank) D.host.E).map (incA D) := by
    exact (congrArg Units.val e).symm
  show (ex P Q γE).map (incA D) = (matHom B (stabilizerEmbedding d γ)).1
  rw [unitaryEmbedding_matrix_formula, hA, ex_map]


set_option synthInstance.maxHeartbeats 400000 in
theorem continuous_unitaryEmbedding (d : HermitianOrthogonalExtensionData A B c ε) : Continuous (stabilizerEmbedding d) := by
  haveI : IsTopologicalRing (AF D.host.F ⊗[D.host.F] D.host.E) :=
    IsModuleTopology.isTopologicalRing (AF D.host.F) _
  have hf : ∀ {f : GA D A → Matrix (Fin A.rank) (Fin A.rank) (AF D.host.F ⊗[D.host.F] D.host.E)}, Continuous f →
      Continuous fun h => ex ((frameMat B A d.ι).map (incA D)) ((qM d).map (incA D)) (f h) := fun hc =>
    continuous_const.add ((continuous_const.matrix_mul (hc.sub continuous_const)).matrix_mul continuous_const)
  have hv : Continuous fun h : GA D A => (matHom A h).1 :=
    Units.continuous_val.comp continuous_subtype_val
  have hi : Continuous fun h : GA D A => (matHom A h⁻¹).1 :=
    Units.continuous_coe_inv.comp continuous_subtype_val
  let φ : GA D A →* GA D B := MonoidHom.mk' (stabilizerEmbedding d) (unitaryEmbedding_mul d)
  have hc : Continuous fun h => matHom B (stabilizerEmbedding d h) := by
    refine Units.continuous_iff.2 ⟨(hf hv).congr fun h => (unitaryEmbedding_matrix_formula d h).symm, (hf hi).congr fun h => ?_⟩
    have e : (stabilizerEmbedding d h)⁻¹ = stabilizerEmbedding d h⁻¹ := (map_inv φ h).symm
    rw [← map_inv (matHom B), e, unitaryEmbedding_matrix_formula]
  exact Continuous.subtype_mk (p := fun g => g ∈ HR (AF D.host.F) D.sp.cm.sig B.gram) hc fun h => (stabilizerEmbedding d h).2

theorem unitaryEmbedding_continuous_hom_rational : ∀ {D : D7} {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε), Continuous (stabilizerEmbedding d) ∧
    (∀ g h, stabilizerEmbedding d (g * h) = stabilizerEmbedding d g * stabilizerEmbedding d h) ∧ ∀ γ ∈ GQ A, stabilizerEmbedding d γ ∈ GQ B :=
  fun d => ⟨continuous_unitaryEmbedding d, unitaryEmbedding_mul d, unitaryEmbedding_rational d⟩

end GlobalTheory.UnitaryEmbeddingProperties
end
end

