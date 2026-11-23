module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0021
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0033
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.GeoNum
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0008
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0005
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0010
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0006
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.RelabelTransport
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0009

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ExistsUnique
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open ReciprocityTheory.ChartRestriction.G.AI.I1 GroundTheory.Heights₂.Heights.NumbersDVR

universe u v w

theorem ExistsUnique.of_found (hN : IntNumIsFieldIntersection.Statement.{u})
    (hUq : FieldNumbers.IntNumUnique.Statement.{u}) (hBase : FieldNumbers.IntNumBase.Statement.{u})
    (F : Type u) [Field F] {K : Type} [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] :
    ExistsUniqueStatement F ι := by
  classical
  exact Numbers.existsUnique hN hUq (IntNumPoint.proof hBase) hBase

theorem ExistsUnique.full (F : Type u) [Field F] {K : Type} [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] : ExistsUniqueStatement F ι :=
  ExistsUnique.of_found IntNumIsFieldIntersection.full FieldNumbers.IntNumUnique.full
    FieldNumbers.IntNumBase.full F ι

end GroundTheory.Heights₂.Heights.Targets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.GeoNum
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GroundTheory.Heights₂.Heights.FieldNumbers

noncomputable section

namespace GeoNumTarget

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem geoIsMultiProjPrime {F : Type} [Field F] {P : Ideal (NumbersDVR.MRing ι F)}
    (hP : NumbersDVR.IsMultiProjPrime P) : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiProjPrime P :=
  ⟨hP.isPrime, (VocabMultiHomogIdeal.proof VocabMultiHomog.proof F K ι P).2 hP.multiHomog,
    hP.relevant⟩

theorem dvrIsMultiProjPrime {F : Type} [Field F] {P : Ideal (NumbersDVR.MRing ι F)}
    (hP : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiProjPrime P) : NumbersDVR.IsMultiProjPrime P :=
  ⟨hP.1, (VocabMultiHomogIdeal.proof VocabMultiHomog.proof F K ι P).1 hP.2.1, hP.2.2⟩

theorem finsum_mul_eq_sum {α : Type*} (D : α →₀ ℤ) (J : α → ℤ) :
    ∑ᶠ W, D W * J W = D.sum fun W m => m * J W := by
  classical
  rw [Finsupp.sum, finsum_eq_sum_of_support_subset]
  intro W hW
  rw [Function.mem_support] at hW
  rw [Finset.mem_coe, Finsupp.mem_support_iff]
  intro h0
  exact hW (by rw [h0, zero_mul])

theorem isIntersectionTheory {F : Type} [Field F] (I : ReciprocityTheory.ChartRestriction.G.AI.I1.IFamily F ι)
    (hI : ReciprocityTheory.ChartRestriction.G.AI.I1.IsFieldIntersection I) :
    IsIntersectionTheory F (fun P n L => I P n L) := by
  constructor
  · intro P hP hdim
    have hd : ringKrullDim (NumbersDVR.MRing ι F ⧸ P) = ((0 + Fintype.card K : ℕ) : WithBot ℕ∞) :=
      (CutRegular.relDim_eq_natCast_iff P 0).mp (by rw [hdim]; rfl)
    have hi : ∀ k, (X ⟨k, (hP.relevant k).choose⟩ : NumbersDVR.MRing ι F) ∉ P :=
      fun k => (hP.relevant k).choose_spec
    rw [hI.1 P ![] (fun k => (hP.relevant k).choose) ⟨geoIsMultiProjPrime hP, hd⟩ hi,
      ← NumbersDVR.IntNumPoint.proof IntNumBase.full F K ι P _ hP hd hi]
    obtain ⟨-, h⟩ := IntNumBase.full F K ι P hP hdim
    rw [h]
    have := hP.isPrime
    simp [resDeg, hP.isPrime]
  · intro P n hP hdim bf bg f g hf hg hfP hgP bs
    have hd := (CutRegular.relDim_eq_natCast_iff P (n + 1)).mp hdim
    have key := hI.2 P n bs (fun k => (bf k : ℤ) - bg k) f g ⟨geoIsMultiProjPrime hP, hd⟩
      ⟨bf, bg, (VocabMultiHomog.proof F K ι f bf).2 hf, (VocabMultiHomog.proof F K ι g bg).2 hg,
        hfP, hgP, fun k => rfl⟩
    refine key.trans ?_
    have hD : ∀ W, NumbersDVR.ratDiv P f g W = ReciprocityTheory.ChartRestriction.G.AI.I1.ratDiv P f g W := by
      intro W
      simp only [NumbersDVR.ratDiv, ReciprocityTheory.ChartRestriction.G.AI.I1.ratDiv, Finsupp.sub_apply,
        Finsupp.mapRange_apply]
      rw [VocabDivCycle.proof F K ι P f W, VocabDivCycle.proof F K ι P g W]
    simp only [NumbersDVR.cycEval, ReciprocityTheory.ChartRestriction.G.AI.I1.cycEval, hD]
    exact (finsum_mul_eq_sum _ _).symm

theorem isFieldIntersection_intNum (p : ℕ) [Fact p.Prime] :
    ReciprocityTheory.ChartRestriction.G.AI.I1.IsFieldIntersection (F := ZMod p) (ι := ι)
      (fun V _ L => NumbersDVR.intNum (ZMod p) V L) :=
  IntNumIsFieldIntersection.full (ZMod p) K ι

end GeoNumTarget


open GeoNumTarget Bridge.GeoNum in
theorem geoNumStatement {K : Type} [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] :
    ReciprocityTheory.ChartRestriction.G.AI.I1.GeoNumStatement ι := by
  classical
  intro p _ I hI V n a hV hpV hproj
  have hker : RingHom.ker (red (ι := ι) p) ≤ V := by
    rw [ker_red, Ideal.span_le, Set.singleton_subset_iff]
    rw [map_natCast]
    exact hpV
  have hcm : (V.map (red p)).comap (red p) = V := comap_map_eq p hker
  have hdim : ringKrullDim (ReciprocityTheory.ChartRestriction.G.Geo.MRing ι ⧸ V) =
      ((n + Fintype.card K : ℕ) : WithBot ℕ∞) := by
    rw [← hproj.2]
    have := ringKrullDim_eq_of_ringEquiv (quotEquiv p (V.map (red p)))
    rw [hcm] at this
    exact this
  have hC : (C (p : ℤ) : ReciprocityTheory.ChartRestriction.G.Geo.MRing ι) ∈ V := by
    rw [map_natCast]
    exact hpV
  rw [← Bridge.intNum_map_eq_geoNum p n V hV hC hdim a]
  exact (IntNumUnique.full (ZMod p) K ι _ (isIntersectionTheory I hI) _
    (dvrIsMultiProjPrime hproj.1) n ((CutRegular.relDim_eq_natCast_iff _ n).mpr hproj.2) a).symm

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Multilin
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 GroundTheory.Heights₂.Heights.NumbersDVR

universe u

theorem Multilin.of_found
    (hBase : FieldNumbers.IntNumBase.Statement.{u})
    (hCut : FieldNumbers.CutRational.Statement.{u})
    (hEx : FieldNumbers.ExistsForm.Statement.{u})
    (hDiv : FieldNumbers.DivCycleSupport.Statement.{u})
    (hAdd : FieldNumbers.IntNumAdd.Statement.{u})
    {K : Type} [Fintype K] (F : Type u) [Field F] (ι : K → Type) [∀ k, Fintype (ι k)] :
    ReciprocityTheory.ChartRestriction.G.AI.I1.MultilinStatement F ι := by
  classical
  intro I hI V n L j a b hV
  have e : ∀ L' : Fin n → K → ℤ, I V n L' = intNum F V L' := fun L' =>
    Numbers.agree_of hBase hCut hEx hDiv I hI V n L' hV
  have hP : NumbersDVR.IsMultiProjPrime V := (Objects.isMultiProjPrime_iff V).mpr hV.1
  rw [e, e, e]
  exact hAdd F K ι V hP.multiHomog hP.relevant n (relDim_eq_of_ringKrullDim V n hV.2) L j a b

theorem Multilin.full {K : Type} [Fintype K] (F : Type u) [Field F] (ι : K → Type)
    [∀ k, Fintype (ι k)] : ReciprocityTheory.ChartRestriction.G.AI.I1.MultilinStatement F ι :=
  Multilin.of_found FieldNumbers.IntNumBase.full FieldNumbers.CutRational.full
    FieldNumbers.ExistsForm.full FieldNumbers.DivCycleSupport.full FieldNumbers.IntNumAdd.full F ι

end GroundTheory.Heights₂.Heights.Targets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PLelongPolyLimit
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial Filter Topology Matrix
open scoped ContDiff
open GroundTheory.Heights₂.Heights (varInt SmoothNear localMult linEval linForm linForm_single)
open GroundTheory.Heights₂.Heights.ComplexSets (zeroSet)

theorem smoothNear_comp_init {n : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} (p : MvPolynomial (Fin n) ℂ)
    {g : (Fin n → ℂ) → ℝ} (hg : SmoothNear (zeroSet J) g) :
    SmoothNear (zeroSet (graphIdeal J p)) (fun x => g (Fin.init x)) := by
  obtain ⟨U, hU, hJU, hgU⟩ := hg
  have hinit : ContDiff ℝ ∞ (fun x : Fin (n + 1) → ℂ => Fin.init x) :=
    contDiff_pi.2 fun i => contDiff_apply ℝ (fun _ => ℂ) (Fin.castSucc i)
  exact ⟨(fun x => Fin.init x) ⁻¹' U, hU.preimage hinit.continuous,
    fun x hx => hJU (init_mem_zeroSet p hx), hgU.comp hinit.contDiffOn fun _ hx => hx⟩

theorem linEval_single_last {n : ℕ} (x : Fin (n + 1) → ℂ) :
    linEval (Pi.single (Fin.last n) 1) x = x (Fin.last n) := by
  simp [linEval, Pi.single_apply]

end GroundTheory.Heights₂.Heights.Targets
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PSymmRelabel
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open ReciprocityTheory.ChartRestriction.G.AI.I1

universe u v w v' w'

theorem SymmRelabel.proof : SymmRelabel.Statement.{u, v, w, v', w'} := by
  intro F _ K _ ι _ K' _ ι' _ e h hS I hI V n L σ hV
  have key := hS _ (Relabel.isFieldIntersection_pull e h hI) (V.map (Relabel.ringEquiv F e h)) n
    (fun j => L j ∘ e.symm) σ ((Relabel.isProjVarF_map_iff e h V n).2 hV)
  have hL : ∀ L₀ : Fin n → K → ℤ, (fun j => (fun j => L₀ j ∘ e.symm) j ∘ e) = L₀ := fun L₀ => by
    funext j k
    simp
  simp only [Relabel.pullFamily, Relabel.comap_map] at key
  have h1 := hL (L ∘ σ)
  have h2 := hL L
  simp only [Function.comp_apply] at h1 h2 key
  rw [h1, h2] at key
  exact key

theorem SymmStatement.full {K : Type v} [Fintype K] (F : Type u) [Field F] (ι : K → Type w)
    [∀ k, Fintype (ι k)] : SymmStatement F ι :=
  SymmStatement.of_found SymmRelabel.proof F ι

end GroundTheory.Heights₂.Heights.Targets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.SegreAssembly
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

universe u v w

theorem SegreComponent.full : SegreComponent.Statement.{u, v, w} :=
  SegreComponent.proof ChartDimBound.proof ChartFiniteIrrel.proof

theorem SegreDivisor.full : SegreDivisor.Statement.{u, v, w} :=
  SegreDivisor.proof SegreComponent.full

theorem Positivity.full {K : Type u} [Fintype K] (F : Type w) [Field F] (ι : K → Type v)
    [∀ k, Fintype (ι k)] : ReciprocityTheory.ChartRestriction.G.AI.I1.PositivityStatement F ι :=
  Positivity.of_found SegreDivisor.full F ι

end GroundTheory.Heights₂.Heights.Targets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StLelongWeightDiff
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial Filter Topology Matrix
open scoped ContDiff
open GroundTheory.Heights₂.Heights (varInt SmoothNear linEval linForm euclPot logReg)

def LelongWeightDiff.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (u : Fin n → ℂ) (g k : (Fin n → ℂ) → ℝ)
    (φ : Fin d → (Fin n → ℂ) → ℝ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → linForm u ∉ J →
    ContDiff ℝ ∞ g → HasCompactSupport g →
    (∀ j, SmoothNear (ComplexSets.zeroSet J) (φ j)) →
    SmoothNear (ComplexSets.zeroSet J) k → (∀ x ∈ ComplexSets.zeroSet J, 0 < k x) →
      Tendsto (fun ε : ℝ =>
          varInt J (d + 1) (fun x => Real.log (‖linEval u x‖ ^ 2 + ε * k x ^ 2) / 2) (vecCons g φ) -
            varInt J (d + 1) (logReg u ε) (vecCons g φ))
        (𝓝[>] 0) (𝓝 0)

end GroundTheory.Heights₂.Heights.Targets
end
end

