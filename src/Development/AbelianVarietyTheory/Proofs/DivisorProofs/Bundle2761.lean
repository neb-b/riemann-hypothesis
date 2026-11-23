module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueVectorFieldOfGlobalOneFormValues
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1490
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AuxiliaryVectorDecompositionEqZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0534
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2581
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2739
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2379
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2752
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0079
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2755
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1162
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1163
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2338
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1168
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2725
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2750
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2728
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2178
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2746
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1728
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0430
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0124
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0434
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsConjAdjointPullbackBijection
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLowestKTypeFockMapThetaVectors
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0187
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainStepFockVectorSphericalOffS
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0592
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0123
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1557
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0023
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2738
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2740
public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeDifferentialsFromGlobalForms
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory
open TensorProduct
namespace GlobalTheory.ParForm

theorem isBaseChange_of_dual {R B M N : Type} [CommRing R] [CommRing B] [Algebra R B] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Module B N] [IsScalarTower R B N] [Module.Finite R M] [Module.Projective R M]
    [Module.Finite B N] [Module.Projective B N] (f : M →ₗ[R] N)
    (h : ∀ l : M →ₗ[R] B, ∃! δ : N →ₗ[B] B, ∀ w, δ (f w) = l w) : IsBaseChange B f := by
  let F : B ⊗[R] M →ₗ[B] N := f.liftBaseChange B
  have hF : ∀ w, F (1 ⊗ₜ w) = f w := fun w ↦ by simp [F]
  have hd : Function.Bijective F.dualMap := by
    rw [Function.bijective_iff_existsUnique]
    intro φ
    obtain ⟨δ, h1, h2⟩ := h ((φ.restrictScalars R).comp (TensorProduct.mk R B M 1))
    refine ⟨δ, ?_, fun δ' e ↦ h2 δ' fun w ↦ ?_⟩
    · refine (LinearMap.liftBaseChangeEquiv B).symm.injective (LinearMap.ext fun w ↦ ?_)
      simpa [hF] using h1 w
    · rw [← hF]
      exact LinearMap.congr_fun e (1 ⊗ₜ w)
  have hdd : Function.Bijective F.dualMap.dualMap :=
    (LinearEquiv.ofBijective _ hd).dualMap.bijective
  have hb : Function.Bijective F := by
    have e : ⇑(Module.Dual.eval B N) ∘ ⇑F = ⇑F.dualMap.dualMap ∘ ⇑(Module.Dual.eval B (B ⊗[R] M)) :=
      funext fun x ↦ rfl
    rw [← Function.Bijective.of_comp_iff' (Module.bijective_dual_eval B N), e]
    exact hdd.comp (Module.bijective_dual_eval B _)
  exact IsBaseChange.of_equiv (LinearEquiv.ofBijective F hb) hF

theorem smooth_sec {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) (hs : Smooth s)
    (U : X.affineOpens) : Algebra.Smooth R (Sec s U.1) := by
  have h1 : RingHom.Smooth (s.appLE ⊤ U.1 le_top).hom :=
    HasRingHomProperty.appLE @Smooth s hs ⟨⊤, isAffineOpen_top _⟩ U le_top
  have h2 : RingHom.Smooth (secMap s U.1).hom :=
    RingHom.Smooth.respectsIso.2 _ (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv h1
  exact h2

theorem par : CrystallineSmoothLift → AbelianHodgeDeRham → ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → Par A.hom := by
  intro H H' R _ A _ g hA hg U
  have hs : Smooth A.hom := SmoothOfRelativeDimension.smooth g A.hom
  have := smooth_sec A.hom hs U.unop
  obtain ⟨-, -, ⟨h1, h2, -⟩, -⟩ := H' R A g hA hg
  exact isBaseChange_of_dual _ (_root_.GlobalTheory.ParPt.exists_unique_of_globForm H H' R A g hA hg U)

end GlobalTheory.ParForm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsNormEqOfTwoOver
section
noncomputable section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

namespace GlobalTheory.ModulusNorm

theorem absNorm_eq_of_two_over {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (h2 : Module.finrank F E = 2) {w w' : HeightOneSpectrum (𝓞 E)} (hne : w ≠ w')
    (h : w'.under (𝓞 F) = w.under (𝓞 F)) :
    Ideal.absNorm w.asIdeal = Ideal.absNorm (w.under (𝓞 F)).asIdeal := by
  set p := (w.under (𝓞 F)).asIdeal with hp
  have l1 : w.asIdeal.LiesOver p := ⟨rfl⟩
  have l2 : w'.asIdeal.LiesOver p := ⟨by rw [hp, ← h]; rfl⟩
  have f1 := Ideal.absNorm_pow_inertiaDeg p w.asIdeal
  have f2 := Ideal.absNorm_pow_inertiaDeg p w'.asIdeal
  have c1 := w.asIdeal.inertiaDeg_pos (𝓞 F)
  have c2 := w'.asIdeal.inertiaDeg_pos (𝓞 F)
  have m1 : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) p ≤ w.asIdeal := Ideal.map_le_iff_le_comap.2 (le_of_eq l1.over)
  have m2 : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) p ≤ w'.asIdeal := Ideal.map_le_iff_le_comap.2 (le_of_eq l2.over)
  have cop : w.asIdeal ⊔ w'.asIdeal = ⊤ :=
    Ideal.IsMaximal.coprime_of_ne w.isMaximal w'.isMaximal fun e => hne (HeightOneSpectrum.ext e)
  have hle : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) p ≤ w.asIdeal * w'.asIdeal := by
    rw [Ideal.mul_eq_inf_of_coprime cop]; exact le_inf m1 m2
  have hd := map_dvd Ideal.absNorm (Ideal.dvd_iff_le.2 hle)
  rw [map_mul, Ideal.absNorm_algebraMap, ← f1, ← f2, ← pow_add,
    ← Algebra.IsAlgebraic.finrank_of_isFractionRing (𝓞 F) F (𝓞 E) E, h2] at hd
  have hq : 1 < Ideal.absNorm p := by
    rcases Nat.lt_or_ge 1 (Ideal.absNorm p) with h' | h'
    · exact h'
    · exfalso
      interval_cases hh : Ideal.absNorm p
      · exact (w.under (𝓞 F)).ne_bot (Ideal.absNorm_eq_zero_iff.1 hh)
      · exact (w.under (𝓞 F)).isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 hh)
  have := (Nat.pow_dvd_pow_iff_le_right hq).1 hd
  have e1 : w.asIdeal.inertiaDeg (𝓞 F) = 1 := by omega
  rw [← f1, e1, pow_one]

variable {D : D7}

theorem conjPl_ne_of_isIdemAt {w : HeightOneSpectrum (𝓞 D.host.E)} {e : Formalism.L2.Theta.AE D}
    (he : Formalism.L2.NTheta.IsIdemAt e w) : Formalism.DivisionValues.conjPl w ≠ w := by
  rw [GlobalTheory.FunObj.conjPl_eq_cP]
  exact GlobalTheory.FunObj.conjPrime_ne_of_isIdempotentAt he

theorem absNorm_of_isIdemAt {w : HeightOneSpectrum (𝓞 D.host.E)} {e : Formalism.L2.Theta.AE D} (he : Formalism.L2.NTheta.IsIdemAt e w) :
    Ideal.absNorm w.asIdeal = Ideal.absNorm (w.under (𝓞 D.host.F)).asIdeal :=
  absNorm_eq_of_two_over D.sp.cm.deg2 (conjPl_ne_of_isIdemAt he).symm (GlobalTheory.ChainTw.ParInv.under_conjPl w)

variable {T : Type} {L : LevCh D T}

theorem absNorm_condE (P : Places L) : Ideal.absNorm (GlobalTheory.FunObj.SqNum.condE P) = GlobalTheory.FunObj.SqNum.levQ P := by
  unfold GlobalTheory.FunObj.SqNum.condE GlobalTheory.FunObj.SqNum.levQ
  rw [map_prod]
  refine Finset.prod_congr rfl fun v hv => ?_
  obtain ⟨e, he⟩ := P.w_split v hv
  rw [map_pow, absNorm_of_isIdemAt he, P.under_w hv]

end GlobalTheory.ModulusNorm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithHeightProjectionFormulaEveryPoint
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

namespace GlobalTheory.MixHt

theorem hasDim_iff_clo {Y : Scheme.{0}} (y : Y) (e : ℕ) : HasDim y e ↔ topologicalKrullDim (clo y) = (e : ℕ) := by
  have hemb := (cloι y).isClosedEmbedding
  have hr : Set.range (cloι y) = closure ({y} : Set Y) := by
    rw [← Set.image_univ, ← (genericPoint_spec (clo y)).def, ← hemb.isClosedMap.closure_image_eq_of_continuous
      hemb.continuous, Set.image_singleton, cloι_genericPoint]
  have h := (hemb.toIsEmbedding.toHomeomorph).isHomeomorph.topologicalKrullDim_eq
  unfold HasDim
  rw [h, hr]

theorem heightProj : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (D E : ℕ),
    IsArithVar p D → IsArithVar q E → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q) (L : HermLB p) (h : X → ℝ) (h' : Y → ℝ),
    L.IsArithHeight h → (L.pull π hπ).IsArithHeight h' → ∀ y : Y, h' y = (π.residueDegree y : ℝ) * h (π y) := by
  intro k _ X Y p q D E hX hY π hπ L h h' H H'
  have key : ∀ (n : ℕ) (w : Y), HasDim w (n + 1) → h' w = (π.residueDegree w : ℝ) * h (π w) := by
    intro n
    induction n with
    | zero =>
      intro w hw
      rcases hY.vertical_or_horizontal (cloι w) with ⟨l, _, hl⟩ | ⟨hc, e, he⟩
      · exact _root_.GlobalTheory.ProjFormulaVert.height_pull_vertical k X Y p q D E hX hY π hπ L h h' H H' w l hl
      · exact _root_.GlobalTheory.ProjCurve.main k X Y p q D E hX hY π hπ L h h' H H' w hc hw
    | succ m ih =>
      intro w hw
      rcases hY.vertical_or_horizontal (cloι w) with ⟨l, _, hl⟩ | ⟨hc, e, he⟩
      · exact _root_.GlobalTheory.ProjFormulaVert.height_pull_vertical k X Y p q D E hX hY π hπ L h h' H H' w l hl
      · exact _root_.GlobalTheory.ProjStep.main k X Y p q D E hX hY π hπ L h h' H H' w m hc hw ih
  intro y
  rcases hY.vertical_or_horizontal (cloι y) with ⟨l, _, hl⟩ | ⟨hc, e, he⟩
  · exact _root_.GlobalTheory.ProjFormulaVert.height_pull_vertical k X Y p q D E hX hY π hπ L h h' H H' y l hl
  · exact key e y ((hasDim_iff_clo y (e + 1)).2 he)

end GlobalTheory.MixHt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithHilbertSamuelLowerBoundNefPlusAmple
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.HSNef

theorem lowerBound_along_div : GlobalTheory.Published.ArCalc → AmpleHS → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p) (c n : ℕ) (α : ℝ), 0 < n → NefFib P.L → P.L.SemiPos D → IsAmpleLB P.A.B → P.A.SemiPos D → ((P.L.pow n).tens P.A).IsSelfInter α → ∀ ε : ℝ, 0 < ε → ∀ᶠ M : ℕ in atTop, (α / (D + 1).factorial / (n : ℝ) ^ (D + 1) - ε) * (M : ℝ) ^ (D + 1) ≤ P.lc M ((M / n : ℕ) - c) 1 := by
  intro _ hHS k _ X _ p D hX P c n α hn hL hLs hA hAs hα ε hε
  have : Module.Finite ℤ k := hX.finite
  have hp : IsProjOver p := hX.isProjOver
  have hLn : NefFib (P.L.pow n) := fun Z i _ _ κ _ _ _ hd => by
    rw [NefHodgeTateAt.topSelf_pow hp P.L n Z i κ hd]
    exact mul_nonneg (Nat.cast_nonneg _) (hL Z i κ hd)
  have hAmp : IsAmpleLB ((P.L.pow n).tens P.A).B := _root_.GlobalTheory.AmpleNefFibZ.isAmpleLB_tens_of_nefFib k X p D hX _ _ hLn hA
  have hSP : ((P.L.pow n).tens P.A).SemiPos D := (hLs.pow n).tens hAs
  have hRep : P.Rep (n : ℤ) 1 ((P.L.pow n).tens P.A) := by
    have h1 := Pair.rep_pow k X p P 1 0 P.L n (Pair.rep_base k X p P).1
    have h2 := Pair.rep_tens k X p P _ _ 0 1 _ _ h1 (Pair.rep_base k X p P).2.1
    simpa using h2
  refine lowerBound_along_residues (D + 1) n (fun M => P.lc M ((M / n : ℕ) - c) 1) (α / (D + 1).factorial) hn
    (fun r hr ε' hε' => ?_) ε hε
  filter_upwards [_root_.GlobalTheory.HSNef.lc_one_eventually_ge hHS k X p D hX P n 1 r (-(c : ℤ)) _ α hRep hAmp hSP hα ε' hε'] with q hq
  have e : (n * q + r) / n = q := by
    rw [Nat.add_comm, Nat.add_mul_div_left _ _ hn, Nat.div_eq_of_lt hr, zero_add]
  simp only [e]
  convert hq using 2 <;> push_cast <;> ring

end GlobalTheory.HSNef
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithKleimanSelfIntersectionNonneg
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.KleimanStep

theorem selfInter_nonneg : GlobalTheory.Published.ArCalc → AmpleHS → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X]
    (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → 1 ≤ D →
    (∀ (C : HermLB p) (h : X → ℝ), C.IsNef D → C.IsArithHeight h → ∀ z, z ≠ genericPoint X → 0 ≤ h z) →
    ∀ (C : HermLB p) (c : ℝ), C.IsNef D → C.IsSelfInter c → 0 ≤ c := by
  intro hC hHS k _ X _ p D hX hD hlow C c hnef hc
  obtain ⟨A, hA, hAn, -⟩ := GlobalTheory.AmpleNefSmall.exists_ample_nef_smallSec hC k X p D hX
  obtain ⟨α, hα, hlim⟩ := GlobalTheory.SelfInterGrowth.main hC k X p D hX C A c hc
  refine ge_of_tendsto' hlim fun n => div_nonneg ?_ (by positivity)
  have hpow := GlobalTheory.NefPow.isNef_pow hC k X p D hX C n hnef
  have htens := _root_.GlobalTheory.NefTens.isNef_tens hC k X p D hX _ _ hpow hAn
  have hamp := _root_.GlobalTheory.AmpleNefFibZ.isAmpleLB_tens_of_nefFib k X p D hX _ A hpow.vertical hA
  obtain ⟨h, hh, he⟩ := hα n
  rw [← he]
  exact _root_.GlobalTheory.HSNef.height_generic_nonneg_of_ample hC hHS k X p D hX hD _ h hamp htens.semiPos hh (hlow _ h htens hh)

end GlobalTheory.KleimanStep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BialgHomSurjectiveIffFinrankKernelQuotientEqOne
section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

namespace GlobalTheory.Dieu

theorem surjective_iff_finrank_quot_kerIdeal_eq_one :
    ∀ (k : Type) [Field k] (A : Type) [CommRing A] [HopfAlgebra k A] [IsCocomm k A]
      [Module.Finite k A] (C : Type) [CommRing C] [HopfAlgebra k C] [IsCocomm k C]
      [Module.Finite k C] (f : C →ₐc[k] A),
      Function.Surjective f ↔ Module.finrank k (A ⧸ kerIdeal f) = 1 := by
  intro k _ A _ _ _ _ C _ _ _ _ f
  constructor
  · intro hf
    rw [kerIdeal_of_surjective hf]
    have hs : Function.Surjective (counitAlgHom k A) := fun c =>
      ⟨algebraMap k A c, by simp⟩
    let e : (A ⧸ augIdeal (R := k) (A := A)) ≃ₐ[k] k := Ideal.quotientKerAlgEquivOfSurjective hs
    rw [e.toLinearEquiv.finrank_eq, Module.finrank_self]
  · intro h
    have hL := _root_.GlobalTheory.Dieu.finrank_eq_range_mul_ker k A C f
    rw [h, mul_one] at hL
    have htop : LinearMap.range (f : C →ₐ[k] A).toLinearMap = ⊤ :=
      Submodule.eq_top_of_finrank_eq hL.symm
    intro a
    have ha : a ∈ LinearMap.range (f : C →ₐ[k] A).toLinearMap := htop ▸ Submodule.mem_top
    obtain ⟨c, hc⟩ := ha
    exact ⟨c, hc⟩

end GlobalTheory.Dieu
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomTripleThetaKernelMinorsEqConstConjJet
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BotFormula.ConjJet

theorem dRho_conj {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (S T : HSp D) (θ : InfFam D)
    (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (f : WO S T → ℂ) :
    dRho (heisO ψ S T) θ τ z (fun w => starRingEnd ℂ (f w)) =
      fun w => starRingEnd ℂ (dRho (heisO ψ (GlobalTheory.Grid.neg S) T) θ τ z f w) := by
  funext x
  show deriv (fun t : ℝ => heisO ψ S T (lineAt θ τ z t) (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id f) x) 0 =
    starRingEnd ℂ (deriv (fun t : ℝ => heisO ψ (GlobalTheory.Grid.neg S) T (lineAt θ τ z t) f x) 0)
  have e : (fun t : ℝ => heisO ψ S T (lineAt θ τ z t) (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id f) x) =
      fun t => star (heisO ψ (GlobalTheory.Grid.neg S) T (lineAt θ τ z t) f x) := by
    funext t
    rw [GlobalTheory.CjNeg.heis_negS' hψ]
    rfl
  rw [e, deriv.star]
  rfl

theorem isFockVacAt_conj {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {θ : InfFam D} (hθ : IsInfFam θ)
    (S T : HSp D) (f : WO S T → ℂ) (hf : IsThetaFunO ψ (GlobalTheory.Grid.neg S) T f) (τ : D.what₂.Tau)
    (hv : IsFockVacAt (heisO ψ (GlobalTheory.Grid.neg S) T) θ τ (cplxO (-1) 1) f) :
    IsFockVacAt (heisO ψ S T) θ τ (cplxO 1 1) (fun w => starRingEnd ℂ (f w)) := by
  intro z
  have h0 : annih (heisO ψ (GlobalTheory.Grid.neg S) T) θ τ (cplxO (-1) 1) z f = 0 := hv z
  have hJ : cplxO (-1 : Matrix (Fin S.rank) (Fin S.rank) ℂ) (1 : Matrix (Fin T.rank) (Fin T.rank) ℂ) z = -cplxO 1 1 z := by
    simp [cplxO]
  unfold annih at h0 ⊢
  rw [hJ, GlobalTheory.FockAdjoint.dRho_neg' hψ hθ hf] at h0
  rw [dRho_conj hψ, dRho_conj hψ]
  funext x
  have h2 := congrFun h0 x
  simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul, Pi.zero_apply] at h2 ⊢
  have e := congrArg (starRingEnd ℂ) h2
  simp only [map_add (f := _), map_mul, map_neg, Complex.conj_I, map_zero] at e
  linear_combination e

theorem map_conj_minorPol {D : D7} {a d : ℕ} {n : D.what₂.Tau → ℕ} (U : Tup D a d n) :
    MvPolynomial.map (starRingEnd ℂ) (GlobalTheory.NormSum.minorPol D U) = GlobalTheory.NormSum.minorPol D U := by
  simp only [GlobalTheory.NormSum.minorPol, map_prod, RingHom.map_det]
  refine Finset.prod_congr rfl fun τ _ => Finset.prod_congr rfl fun j _ => ?_
  congr 1
  ext i i' : 2
  simp

theorem ker_minorF_eq_conj_jet : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData Lc sc) (W : G.Weil),
    IsStdChar D W.ψ (-1) → ∀ (i j : Fin D.R.m) (A A' WW : HSp D) (X : Tri T A A' WW), IsBottomTri W i j X →
    ∀ (r : ℂ) (rc : ℝ), r ≠ 0 → (∀ τ, rc * ‖r‖ ^ 2 = 2 * ‖tauE D τ D.host.xi0‖) → ∀ n₀ : D.what₂.Tau → ℕ,
    ∃ Ω : ℂ, Ω ≠ 0 ∧ ∀ (a d : ℕ) (n : D.what₂.Tau → ℕ) (ea : a = A.rank) (ed : d = WW.rank), n = n₀ →
      ∀ (s : T) (g : GA D WW) (y : GA D A), g ∈ GfC WW → y ∈ GfC A → ∀ Tu : Tup D a d n,
        X.ker W.ψ W.θ s (GlobalTheory.BotFormula.minorF ea ed Tu) g y =
          Ω * starRingEnd ℂ (Formalism.MainNotions.GL3Theta.applyAt0 D (GlobalTheory.NormSum.minorPol D Tu)
            (GlobalTheory.AdForm.xiN W.θ A WW ea.symm ed.symm r rc fun w => starRingEnd ℂ (X.ω s (y, g) (X.f s) w))) := by
  intro D T Lc sc G W hψ i j A A' WW X hX r rc hr hrc n₀
  have hI := hX.is
  have hθ : IsInfFam W.θ := hI.isVac.2.inf
  obtain ⟨c₁, hc₁, H⟩ := GlobalTheory.NormDictEx.Jets.fock_minorPol_zero W.ψ W.θ A WW rfl rfl n₀ r rc hψ hθ hX.std.1 hX.stdW.1 hr hrc
  refine ⟨starRingEnd ℂ c₁, (map_ne_zero _).2 hc₁, ?_⟩
  intro a d n ea ed hn s g y hg hy Tu
  subst ea ed hn
  have hom := hI.weil s
  have e1 : (fun τ => -X.rA.s τ) = fun _ => (-1 : Matrix (Fin A.rank) (Fin A.rank) ℂ) :=
    funext fun τ => by rw [(hX.std.2.2 τ).1]
  have e2 : X.rW.s = fun _ => (1 : Matrix (Fin WW.rank) (Fin WW.rank) ℂ) := funext fun τ => (hX.stdW.2.2 τ).1
  have e3 : X.rA.B = fun _ => (1 : Matrix (Fin A.rank) (Fin A.rank) ℂ) := funext fun τ => (hX.std.2.2 τ).2
  have e4 : X.rW.B = fun _ => (1 : Matrix (Fin WW.rank) (Fin WW.rank) ℂ) := funext fun τ => (hX.stdW.2.2 τ).2
  have hf : IsThetaFunO W.ψ (GlobalTheory.Grid.neg A) WW (X.f s) := (GlobalTheory.ConstRatio.theta_f hI s).1
  have ho := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum (hI.idem s)
  have hv : ∀ τ, IsFockVacAt (heisO W.ψ (GlobalTheory.Grid.neg A) WW) W.θ τ (cplxO (-X.rA.s τ) (X.rW.s τ)) (X.f s) := fun τ =>
    GlobalTheory.DatumFock.isFockVacAt_of_isThetaAt hψ.1.1 hθ ho.infPart_eq ho.conj.infPart_eq (hI.fst s)
      hI.isVac.2.theta hf (hI.isVac.2.fock τ)
  have hy' : (GlobalTheory.Grid.ofSgn true A).symm y ∈ GfC (GlobalTheory.Grid.neg A) := hy
  have hmove := GlobalTheory.FockRealMove.om_fin_fockVac D W.ψ W.θ (GlobalTheory.Grid.neg A) WW _ _ ((X.ω s).toSgn true) hom hθ
    (fun τ => -X.rA.s τ) X.rW.s (X.f s) hf hv _ hy' g hg
  have hcomm := GlobalTheory.OrientedHeis.om_fin_pureTensorO W.ψ (GlobalTheory.Grid.neg A) WW _ _ ((X.ω s).toSgn true) hom W.θ hθ _ hy' g hg
    (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f s) (GlobalTheory.BotFormula.minorF rfl rfl Tu) hf
  set F : WO A WW → ℂ := X.ω s (y, g) (X.f s) with hF
  have hF1 : IsThetaFunO W.ψ (GlobalTheory.Grid.neg A) WW F := hmove.1
  have hF2 : ∀ τ, IsFockVacAt (heisO W.ψ (GlobalTheory.Grid.neg A) WW) W.θ τ (cplxO (-1) 1) F := fun τ => by
    have h := hmove.2 τ
    rw [(hX.std.2.2 τ).1, (hX.stdW.2.2 τ).1] at h
    exact h
  have hJ := H (fun w => starRingEnd ℂ (F w))
    (GlobalTheory.CjNeg.theta_negS' hψ (show IsThetaFunO W.ψ (GlobalTheory.ChiGrid.negSp A) WW F from hF1))
    (fun τ => isFockVacAt_conj hψ hθ A WW F hF1 τ (hF2 τ)) Tu
  have hP : MvPolynomial.map (starRingEnd ℂ) (GlobalTheory.BotFormula.minorF (rfl : A.rank = A.rank) (rfl : WW.rank = WW.rank) Tu) =
      GlobalTheory.BotFormula.minorF rfl rfl Tu := by
    unfold GlobalTheory.BotFormula.minorF
    rw [MvPolynomial.map_rename, map_conj_minorPol]
  have hc := GlobalTheory.FockNegSubst.pureTensorO_negSp_map_conj W.ψ W.θ A WW hψ hθ (fun _ => 1) (fun _ => 1) F
    (GlobalTheory.BotFormula.minorF rfl rfl Tu)
  rw [hP] at hc
  have hk : X.ker W.ψ W.θ s (GlobalTheory.BotFormula.minorF rfl rfl Tu) g y =
      pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B F
        (GlobalTheory.BotFormula.minorF rfl rfl Tu) 0 := congrFun hcomm 0
  rw [hk, e1, e2, e3, e4, ← map_mul, ← hJ]
  exact congrFun hc 0

end GlobalTheory.BotFormula.ConjJet

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardTorsionGeometricPointsEqPowTwoDim
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem comp_pow_id_torscard {S : Scheme.{0}} {G T : Over S} [GrpObj G] (x : T ⟶ G) (n : ℕ) :
    x ≫ (𝟙 G) ^ n = x ^ n := by
  induction n with
  | zero => simp [MonObj.comp_one]
  | succ k ih => rw [pow_succ, MonObj.comp_mul, ih, Category.comp_id, pow_succ]

theorem card_torsion_pt (K : Type) [Field K] (A : AbVar K) (n : ℕ) (hn : (n : K) ≠ 0) :
    Nat.card {x : A.Pt // x ^ n = 1} = n ^ (2 * A.dim) := by
  have hn0 : (n : ℤ) ≠ 0 := by
    intro h; apply hn; simp at h; simp [h]
  obtain ⟨hiso, hdeg⟩ := _root_.GlobalTheory.MulIsogeny.mul_isogeny K A (n : ℤ) hn0
  have hf : ((n : ℤ) • 𝟙 A).hom = (𝟙 A.X) ^ n := by
    rw [natCast_zsmul, nsmul_hom, id_hom]
  have hker : ∀ {T : Over (Sp K)} (x : T ⟶ A.X), x ≫ ((n : ℤ) • 𝟙 A).hom = x ^ n := by
    intro T x; rw [hf, comp_pow_id_torscard]
  have hd := _root_.GlobalTheory.AV.DegSep.deg_eq_card_ker_of_killed K A A ((n : ℤ) • 𝟙 A) n hn hiso (fun T x hx => by rw [← hker]; exact hx)
  rw [hdeg, Int.natAbs_natCast] at hd
  rw [hd]
  apply Nat.card_congr
  exact Equiv.subtypeEquivRight (fun x => by rw [MonoidHom.mem_ker, ptMap_apply, hker])

end GlobalTheory.AV.AbVar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConnectedPDivGroupChartSemilinearHomIsFormalGrouStatement
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.connectedPDivGroupChart_semilinearHom_isFormalGroupHom : ∀ (p : ℕ) (k k' : Type) [CommRing k] [CommRing k'] (σ : k →+* k') (d e : ℕ) (G : PDivGroup p k) (G' : PDivGroup p k') (c : Chart G d) (c' : Chart G' e) (s : SemiHom σ G' G) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k) (ν : Fin e → MvPowerSeries (Fin e ⊕ Fin e) k') (φ : Fin d → MvPowerSeries (Fin e) k'), c.IsLawOf μ → c'.IsLawOf ν → (∀ n j, c'.ev n (φ j) = s.app n (c.x n j)) → IsHom ν (fun i => MvPowerSeries.map σ (μ i)) φ := by
  first | exact @GlobalTheory.Katz.isHom_map_of_semiHom_ev | exact GlobalTheory.Katz.isHom_map_of_semiHom_ev | (intros; apply GlobalTheory.Katz.isHom_map_of_semiHom_ev <;> assumption)
end

