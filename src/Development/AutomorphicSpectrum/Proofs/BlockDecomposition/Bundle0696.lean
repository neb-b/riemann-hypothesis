module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0690
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0689
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.ThetaFixedGlobalOfTraceInputs
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.ConeWeightsNotSecondType
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.StableEigenspaces.FiniteTypes.FintypeHolds
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.HighestVectorsRegularLine
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.ExtraTop
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.InfinitesimalCharacterGlue
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1228
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1192
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.HermitianCellMeasures.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0693
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0302
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0687
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0692
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0691
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0314
public import GroundTheory.AutomorphicForms.Bundle0023

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BoundedDenominatorsCompactIdeleSetStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GroundTheory.Global PositivityTheory.Rg.Base1 GlobalTheory.CompanionTheory.BasePsi
open scoped ENNReal NNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bounded_denominators_compact_idele_set : ∀ (F : Type) [Field F] [NumberField F] (D : Set (AF F)ˣ), IsCompact D → ∀ (S : Finset (HeightOneSpectrum (𝓞 F)))
    (C : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)), (∀ v ∈ S, IsCompact (C v)) →
    ∃ N : ℕ, 0 < N ∧ ∀ u ∈ D, ∀ t : F, (∀ v ∈ S, algebraMap F (Fv F v) t * (u : AF F).2 v ∈ C v) →
      (∀ v, v ∉ S → algebraMap F (Fv F v) t * (u : AF F).2 v ∈ v.adicCompletionIntegers F) →
      ∃ y : 𝓞 F, (y : F) = N * t := by
  first | exact @GlobalTheory.CompanionTheory.BasePsi.Den.common_denominator | exact GlobalTheory.CompanionTheory.BasePsi.Den.common_denominator | (intros; apply GlobalTheory.CompanionTheory.BasePsi.Den.common_denominator <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EopWMemStabAlg
section
noncomputable section

open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.Desc

namespace GlobalTheory.CompanionTheory.TwY

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

abbrev UU (n : ℕ) : Type := Matrix.unitaryGroup (Fin n) ℂ


open Classical in
def singleN (w : InfinitePlace E) : ℂ →ₙ+* Cinf E where
  toFun x := fun v => if v = w then x else 0
  map_mul' x y := by
    funext v
    by_cases hv : v = w <;> simp [hv]
  map_zero' := by
    funext v
    simp
  map_add' x y := by
    funext v
    by_cases hv : v = w <;> simp [hv]

def locInf (w : InfinitePlace E) : PositivityTheory.RgTw.G n →* GL (Fin n) (Cinf E) := cornerGL n (singleN w)

def gAt (w : InfinitePlace E) : PositivityTheory.RgTw.G n →* GA E n := (infGL E n).comp (locInf w)

def kAt (w : InfinitePlace E) : UU n →* GA E n := (gAt w).comp Unitary.toUnits

omit [NumberField E] [IsCMField E] in
theorem one_apply_pi (i j : Fin n) (v : InfinitePlace E) :
    (1 : Matrix (Fin n) (Fin n) (Cinf E)) i j v = (1 : Matrix (Fin n) (Fin n) ℂ) i j := by
  by_cases hij : i = j
  · subst hij; simp
  · simp [Matrix.one_apply_ne hij]

omit [NumberField E] [IsCMField E] in
open Classical in
theorem locInf_apply (w : InfinitePlace E) (g : PositivityTheory.RgTw.G n) (i j : Fin n) (v : InfinitePlace E) :
    ((locInf w g : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) i j v =
      if v = w then (g : Matrix (Fin n) (Fin n) ℂ) i j else (1 : Matrix (Fin n) (Fin n) ℂ) i j := by
  have e : ((locInf w g : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) i j v =
      (1 : Matrix (Fin n) (Fin n) (Cinf E)) i j v - singleN w ((1 : Matrix (Fin n) (Fin n) ℂ) i j) v +
        singleN w ((g : Matrix (Fin n) (Fin n) ℂ) i j) v := rfl
  rw [e, one_apply_pi]
  change _ - (if v = w then _ else 0) + (if v = w then _ else 0) = _
  by_cases hv : v = w <;> simp [hv]

def kInfAt (w : InfinitePlace E) (c : UU n) : Kinf E n :=
  ⟨(locInf w (Unitary.toUnits c) : GL (Fin n) (Cinf E)).val, by
    classical
    refine Matrix.mem_unitaryGroup_iff'.2 ?_
    ext i j v
    have hc : star c.1 * c.1 = 1 := Matrix.mem_unitaryGroup_iff'.1 c.2
    rw [Matrix.mul_apply, Finset.sum_apply, one_apply_pi]
    simp only [Matrix.star_apply, Pi.mul_apply, Pi.star_apply, locInf_apply]
    by_cases hv : v = w
    · simp only [hv, if_true]
      have := congrFun (congrFun hc i) j
      rw [Matrix.mul_apply] at this
      simp only [Matrix.star_apply] at this
      rw [← this]
      rfl
    · simp only [hv, if_false]
      simp [Matrix.one_apply, eq_comm]⟩

theorem infGL_kInfAt (w : InfinitePlace E) (c : UU n) :
    infGL E n (Unitary.toUnits (kInfAt w c)) = kAt w c := by
  unfold kAt gAt
  simp only [MonoidHom.comp_apply]
  congr 1
  exact Units.ext rfl

def sV (π : CuspSub E n) (w : InfinitePlace E) : UU n →* Module.End ℂ π.V where
  toFun c := (rt E n (kAt w c)).restrict fun ψ hψ => by
    have h := π.stable (.cpt (kInfAt w c)) ψ hψ
    have e : rt E n (kAt w c) ψ = cptRep E n (kInfAt w c) ψ := by
      rw [← infGL_kInfAt]; rfl
    rw [e]; exact h
  map_one' := by
    ext ψ; simp
  map_mul' a b := by
    ext ψ; simp

def stabAlg (π : CuspSub E n) : Subalgebra ℂ (Module.End ℂ (Sm E n)) where
  carrier := {T | ∀ ψ ∈ π.V, T ψ ∈ π.V}
  mul_mem' ha hb ψ hψ := ha _ (hb ψ hψ)
  add_mem' ha hb ψ hψ := π.V.add_mem (ha ψ hψ) (hb ψ hψ)
  algebraMap_mem' c ψ hψ := π.V.smul_mem c hψ

theorem Eop_mem_stabAlg (π : CuspSub E n) (τ : E →+* ℂ) (i j : Fin n) : Eop (a := n) τ i j ∈ stabAlg π := by
  have hL : ∀ X, lie E n X ∈ stabAlg π := fun X ψ hψ => π.stable (.lie X) ψ hψ
  exact (stabAlg π).smul_mem ((stabAlg π).sub_mem (hL _) ((stabAlg π).smul_mem (hL _) _)) _

theorem eopW_mem_stabAlg (π : CuspSub E n) (w : InfinitePlace E) (s : Bool) (i j : Fin n) :
    PositivityTheory.RgBcC.Bridge.eopW w s i j ∈ stabAlg π := by
  cases s
  · exact Eop_mem_stabAlg π _ i j
  · exact Eop_mem_stabAlg π _ i j

section Avg

variable [MeasurableSpace (UU n)] (κ : Measure (UU n)) (Em : PositivityTheory.RgBcC.KMod n) (T : Em.V →L[ℂ] Em.V)

end Avg

end GlobalTheory.CompanionTheory.TwY
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFiniteDimCompactStable
section
open scoped Classical InnerProductSpace ComplexConjugate
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.AutomorphicL2Unitary GlobalTheory.SqIntGL
open scoped GlobalTheory.CuspRep.CuspidalL2GL

noncomputable section

namespace GlobalTheory.CompanionTheory.FinDiscKfin

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {M : ℕ}

theorem fin_cpt_apply (u : GL (Fin M) (Af E)) (k : Kinf E M) (a : Sm E M) :
    finRep E M u (cptRep E M k a) = cptRep E M k (finRep E M u a) := by
  have h : finRep E M u * cptRep E M k = cptRep E M k * finRep E M u := by
    change rt E M (finGL E M u) * rt E M (infGL E M (Unitary.toUnits k)) =
      rt E M (infGL E M (Unitary.toUnits k)) * rt E M (finGL E M u)
    rw [← map_mul, ← map_mul, infGL_comm]
  exact LinearMap.congr_fun h a

theorem continuous_coeff (A : Submodule ℂ (Sm E M)) [FiniteDimensional ℂ A]
    (hA : ∀ k, ∀ a ∈ A, cptRep E M k a ∈ A) (ℓ : Sm E M →ₗ[ℂ] ℂ) (a : Sm E M) (ha : a ∈ A) :
    Continuous fun k => ℓ (cptRep E M k a) := by
  let ev : GA E M → Module.Dual ℂ A := fun g =>
    (LinearMap.proj g).comp ((Sm E M).subtype.comp A.subtype)
  have hspan : Submodule.span ℂ (Set.range ev) = ⊤ := by
    have h0 : (Submodule.span ℂ (Set.range ev)).dualCoannihilator = ⊥ := by
      rw [eq_bot_iff]
      intro v hv
      rw [Submodule.mem_dualCoannihilator] at hv
      have h2 : ∀ g, v.1.1 g = 0 := fun g => hv _ (Submodule.subset_span ⟨g, rfl⟩)
      rw [Submodule.mem_bot]
      exact Subtype.ext (Subtype.ext (funext h2))
    rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := Submodule.span ℂ (Set.range ev)), h0,
      Submodule.dualAnnihilator_bot]
  have key : ∀ ξ ∈ Submodule.span ℂ (Set.range ev),
      Continuous fun k => ξ ⟨cptRep E M k a, hA k a ha⟩ := by
    intro ξ hξ
    induction hξ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      exact GlobalTheory.CompanionTheory.AdmDiscFin.continuous_slice a g
    | zero => exact continuous_const
    | add x y _ _ hx hy => exact hx.add hy
    | smul r x _ hx => exact hx.const_smul r
  exact key (ℓ.comp A.subtype) (hspan ▸ Submodule.mem_top)

end GlobalTheory.CompanionTheory.FinDiscKfin

theorem GlobalTheory.CompanionTheory.FinDiscKfin.exists_kfin_subspace :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (V : Submodule ℂ (Sm E N)), IsDiscrete V →
      ∀ L : Subgroup (GL (Fin N) (Af E)), ∀ x ∈ V, (∀ u ∈ L, finRep E N u x = x) →
      ∃ A : Submodule ℂ (Sm E N), FiniteDimensional ℂ A ∧ x ∈ A ∧
        (∀ a ∈ A, a ∈ V ∧ ∀ u ∈ L, finRep E N u a = a) ∧ (∀ k, ∀ a ∈ A, cptRep E N k a ∈ A) ∧
        ∀ ℓ : Sm E N →ₗ[ℂ] ℂ, ∀ a ∈ A, Continuous fun k => ℓ (cptRep E N k a) := by
  intro E _ _ _ N V hV L x hx hL
  haveI hfin : FiniteDimensional ℂ (GlobalTheory.AutGrowth.spanK E N x) := (hV.aut x hx).kfin
  refine ⟨GlobalTheory.AutGrowth.spanK E N x, hfin, GlobalTheory.AutGrowth.self_mem_spanK x, ?_,
    GlobalTheory.AutGrowth.spanK_stable x, fun ℓ a ha =>
      GlobalTheory.CompanionTheory.FinDiscKfin.continuous_coeff _ (GlobalTheory.AutGrowth.spanK_stable x) ℓ a ha⟩
  intro a ha
  refine ⟨?_, fun u hu => ?_⟩
  · induction ha using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨k, rfl⟩ := hy
      exact hV.stable (.cpt k) x hx
    | zero => exact V.zero_mem
    | add y z _ _ hy hz => exact V.add_mem hy hz
    | smul c y _ hy => exact V.smul_mem c hy
  · induction ha using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨k, rfl⟩ := hy
      change finRep E N u (cptRep E N k x) = cptRep E N k x
      rw [GlobalTheory.CompanionTheory.FinDiscKfin.fin_cpt_apply, hL u hu]
    | zero => exact map_zero _
    | add y z _ _ hy hz => rw [map_add (f := _), hy, hz]
    | smul c y _ hy => rw [map_smul, hy]

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFinsetIntOff
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L PositivityTheory.Rg.Rsw.Em

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open IsDedekindDomain NumberField

namespace GlobalTheory.CompanionTheory.ColumnSplitting.YvInt

variable {D : D7} {a b c : ℕ}

theorem cv_cA (v : Pl D) (z : AE D) : cv D v (cA D z) = sigR _ D.sp.cm.sig (cv D v z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [RingHom.map_add (f := _), RingHom.map_add (f := _), RingHom.map_add (f := _), RingHom.map_add (f := _), hx, hy]
  | tmul a x => rfl

theorem intOff_mm {S : Finset (Pl D)} {x : Mx D a b} {y : Mx D b c} (hx : IntOff S x) (hy : IntOff S y) :
    IntOff S (mm x y) := by
  intro v hv i j
  have h : mm x y i j = ∑ k, x i k * y k j := Matrix.mul_apply
  have hs : ∑ k, x i k * y k j ∈ (intLoc D.host.F D.host.E v).comap (cv D v) :=
    Subring.sum_mem _ fun k _ => Subring.mul_mem _ (Subring.mem_comap.2 (hx v hv i k))
      (Subring.mem_comap.2 (hy v hv k j))
  rw [h]
  exact Subring.mem_comap.1 hs

theorem intOff_adj {S : Finset (Pl D)} {x : Mx D a b} (hx : IntOff S x) : IntOff S (adj x) := by
  intro v hv i j
  have h : adj x i j = cA D (x j i) := rfl
  rw [h, cv_cA]
  exact sigR_mem_intLoc _ (hx v hv j i)

theorem exists_finset_intOff (x : Mx D a b) : ∃ S₀ : Finset (Pl D), ∀ S, S₀ ⊆ S → IntOff S x := by
  have hbad : {v : Pl D | ¬ ∀ i j, cv D v (x i j) ∈ intLoc D.host.F D.host.E v}.Finite :=
    GlobalTheory.CompanionTheory.ColumnSplitting.exists_intOff x
  refine ⟨hbad.toFinset, fun S hS v hv => ?_⟩
  by_contra hc
  exact hv (hS (hbad.mem_toFinset.2 hc))

theorem intOff_yv (D : D7) (r t : ℕ) (V : HSp D) (b₀ : HermE D r) :
    ∃ S₀ : Finset (Pl D), ∀ S, S₀ ⊆ S → ∀ z : Mx D V.rank r × Mx D V.rank t,
      IntOff S z.1 → IntOff S z.2 → IntOff S (yv V b₀ z) := by
  classical
  obtain ⟨S₁, h₁⟩ := exists_finset_intOff (rat b₀.1⁻¹ : Mx D r r)
  obtain ⟨S₂, h₂⟩ := exists_finset_intOff (gA V)
  refine ⟨S₁ ∪ S₂, fun S hS z hz₁ hz₂ => ?_⟩
  exact intOff_mm (h₁ S (Finset.union_subset_left hS))
    (intOff_mm (intOff_adj hz₁) (intOff_mm (h₂ S (Finset.union_subset_right hS)) hz₂))

end GlobalTheory.CompanionTheory.ColumnSplitting.YvInt

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsInvariantProjection
section
open scoped Classical InnerProductSpace ComplexConjugate
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.AutomorphicL2Unitary GlobalTheory.SqIntGL
open scoped GlobalTheory.CuspRep.CuspidalL2GL

noncomputable section

namespace GlobalTheory.CompanionTheory.FinDiscAvg

theorem exists_sum_fixed {G W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [AddCommGroup W] [Module ℂ W] (ρ : G →* Module.End ℂ W) (x : W) (ho : IsOpen {k | ρ k x = x}) :
    ∃ R : Finset G, R.Nonempty ∧ ∀ u, ρ u (∑ r ∈ R, ρ r x) = ∑ r ∈ R, ρ r x := by
  let K : Subgroup G :=
    { carrier := {k | ρ k x = x}
      one_mem' := by simp
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [map_mul, Module.End.mul_apply, hb, ha]
      inv_mem' := fun {a} ha => by
        simp only [Set.mem_setOf_eq] at ha ⊢
        have h : ρ a⁻¹ (ρ a x) = x := by
          rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
        rwa [ha] at h }
  have hK : ∀ k, k ∈ K ↔ ρ k x = x := fun _ => Iff.rfl
  obtain ⟨R, hR, hc⟩ := GlobalTheory.compact_finite_leftCoset_reps G K ho Set.univ isCompact_univ
  have hc' : ∀ g : G, ∃ r ∈ R, r⁻¹ * g ∈ K := fun g => hc g (Set.mem_univ g)
  have hne : R.Nonempty := by
    obtain ⟨r, hr, -⟩ := hc' 1
    exact ⟨r, hr⟩
  refine ⟨R, hne, fun u => ?_⟩
  choose! σ hσR hσ using fun r : G => hc' (u * r)
  have hval : ∀ r, ρ (u * r) x = ρ (σ r) x := by
    intro r
    have h := (hK _).1 (hσ r)
    have e : u * r = σ r * ((σ r)⁻¹ * (u * r)) := by group
    rw [e, map_mul, Module.End.mul_apply, h]
  have hinj : Set.InjOn σ R := by
    intro r hr r' hr' e
    refine hR r hr r' hr' ?_
    have h1 := hσ r
    have h2 := hσ r'
    rw [show σ r = σ r' from e] at h1
    have := K.mul_mem (K.inv_mem h1) h2
    have e2 : ((σ r')⁻¹ * (u * r))⁻¹ * ((σ r')⁻¹ * (u * r')) = r⁻¹ * r' := by group
    rwa [e2] at this
  have himg : R.image σ = R := by
    refine Finset.eq_of_subset_of_card_le ?_ ?_
    · intro s hs
      obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 hs
      exact hσR r
    · rw [Finset.card_image_of_injOn hinj]
  calc ρ u (∑ r ∈ R, ρ r x) = ∑ r ∈ R, ρ (σ r) x := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum]
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [← hval, map_mul, Module.End.mul_apply]
    _ = ∑ s ∈ R.image σ, ρ s x := (Finset.sum_image (f := fun s => ρ s x) hinj).symm
    _ = ∑ r ∈ R, ρ r x := by rw [himg]

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {N : ℕ}
  (μ : Measure (GA E N)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]

theorem l2Map_right_translate (k : GL (Fin N) (Af E)) {a : Sm E N} (ha : a ∈ squareIntegrableSmoothSubmoduleGL μ) (hb : finRep E N k a ∈ squareIntegrableSmoothSubmoduleGL μ) :
    l2Map μ (finRep E N k a) = R (latticeGL E N) μ (finGL E N k) (l2Map μ a) := by
  rw [l2Map_apply μ ha, l2Map_apply μ hb, right_translate_toL2]
  rfl

theorem inner_R (g : GA E N) (u v : L2 (latticeGL E N) μ) :
    ⟪R (latticeGL E N) μ g u, R (latticeGL E N) μ g v⟫_ℂ = ⟪u, v⟫_ℂ := by
  let T : L2 (latticeGL E N) μ →ₗᵢ[ℂ] L2 (latticeGL E N) μ :=
    ⟨(R (latticeGL E N) μ g : L2 (latticeGL E N) μ →L[ℂ] L2 (latticeGL E N) μ).toLinearMap, norm_R g⟩
  exact T.inner_map_map u v

theorem exists_avg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (μ : Measure (GA E N)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (V : Submodule ℂ (Sm E N)), IsDiscrete V → ∀ L : Subgroup (GL (Fin N) (Af E)), IsCompact (L : Set (GL (Fin N) (Af E))) → ∀ x ∈ V, ∃ x' ∈ V, (∀ u ∈ L, finRep E N u x' = x') ∧ ∀ y : Sm E N, y ∈ squareIntegrableSmoothSubmoduleGL μ → (∀ u ∈ L, finRep E N u y = y) → ⟪l2Map μ x, l2Map μ y⟫_ℂ = ⟪l2Map μ x', l2Map μ y⟫_ℂ := by
  intro E _ _ _ N μ _ _ V hV L hL x hx
  haveI : CompactSpace L := isCompact_iff_compactSpace.1 hL
  let ρ : L →* Module.End ℂ (Sm E N) := (finRep E N).comp L.subtype
  have hρ : ∀ l : L, ρ l = finRep E N (l : GL (Fin N) (Af E)) := fun _ => rfl
  have ho : IsOpen {k : L | ρ k x = x} :=
    (hV.aut x hx).level.preimage continuous_subtype_val
  obtain ⟨S, hS, hfix⟩ := exists_sum_fixed ρ x ho
  have hn : ((S.card : ℂ)) ≠ 0 := Nat.cast_ne_zero.2 hS.card_pos.ne'
  have hmem : ∀ l : L, ρ l x ∈ V := fun l => hV.stable (.fin _) x hx
  refine ⟨(S.card : ℂ)⁻¹ • ∑ r ∈ S, ρ r x, V.smul_mem _ (V.sum_mem fun r _ => hmem r), ?_, ?_⟩
  · intro u hu
    rw [map_smul, ← hρ ⟨u, hu⟩ , hfix]
  · intro y hy hyL
    have hl2 : ∀ z ∈ V, z ∈ squareIntegrableSmoothSubmoduleGL μ := fun z hz => mem_l2Sub_of_isAutForm μ (hV.aut z hz) (hV.sqInt z hz)
    have hxl := hl2 x hx
    have key : ∀ r : L, ⟪l2Map μ (ρ r x), l2Map μ y⟫_ℂ = ⟪l2Map μ x, l2Map μ y⟫_ℂ := by
      intro r
      have e1 := l2Map_right_translate μ (r : GL (Fin N) (Af E)) hxl (hl2 _ (hmem r))
      have e2 := l2Map_right_translate μ (r : GL (Fin N) (Af E)) hy (by rw [hyL _ r.2]; exact hy)
      rw [hyL _ r.2] at e2
      rw [hρ, e1]
      conv_lhs => rw [e2]
      exact inner_R μ _ _ _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_smul, map_sum, inner_smul_left, sum_inner, Finset.sum_congr rfl fun r _ => key r,
      Finset.sum_const, nsmul_eq_mul, map_inv₀, Complex.conj_natCast, inv_mul_cancel_left₀ hn]

end GlobalTheory.CompanionTheory.FinDiscAvg

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsOpenCompactSubgroupLe
section
open scoped Classical InnerProductSpace ComplexConjugate
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.AutomorphicL2Unitary GlobalTheory.SqIntGL
open scoped GlobalTheory.CuspRep.CuspidalL2GL

namespace GlobalTheory.CompanionTheory.FinDiscOrth

theorem exists_compact_open_level_le (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ)
    (S : Subgroup (GL (Fin N) (Af E))) (hS : IsOpen (S : Set (GL (Fin N) (Af E)))) :
    ∃ L : Subgroup (GL (Fin N) (Af E)), L ≤ S ∧ IsOpen (L : Set (GL (Fin N) (Af E))) ∧
      IsCompact (L : Set (GL (Fin N) (Af E))) := by
  let K : Subgroup (GL (Fin N) (Af E)) := GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E N
  have hKo : IsOpen (K : Set (GL (Fin N) (Af E))) :=
    GroundTheory.Automorphic.AdelicGLn.isOpen_integralFiniteGL E N
  have hKc : IsCompact (K : Set (GL (Fin N) (Af E))) :=
    GroundTheory.Automorphic.AdelicGLn.isCompact_integralFiniteGL E N
  have hSc : IsClosed (S : Set (GL (Fin N) (Af E))) := Subgroup.isClosed_of_isOpen S hS
  refine ⟨S ⊓ K, inf_le_left, ?_, ?_⟩
  · change IsOpen ((S : Set (GL (Fin N) (Af E))) ∩ (K : Set (GL (Fin N) (Af E))))
    exact hS.inter hKo
  · have : ((S ⊓ K : Subgroup _) : Set (GL (Fin N) (Af E))) =
        (K : Set (GL (Fin N) (Af E))) ∩ (S : Set (GL (Fin N) (Af E))) := by
      ext x; simp [and_comm]
    rw [this]
    exact hKc.inter_right hSc

end GlobalTheory.CompanionTheory.FinDiscOrth
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdeleModuleEqNormModule
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter PositivityTheory.Rg.Base1 GroundTheory.Global GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil
open scoped TensorProduct ENNReal NNReal Matrix Classical

namespace GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil

theorem ideleModule_eq_md_of_isNm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (x : (AF F ⊗[F] E)ˣ) (n : (AF F)ˣ), IsNm σ x n → (IdeleGroup.ideleModule E (GroundTheory.BlockD.ThmBHecke.ideleEquiv F E x) : ℝ) = md n := by
  intro F E _ _ _ _ _ σ hcm x n h
  have h1 := _root_.GlobalTheory.CompanionTheory.SW.ModConj.ideleModule_conj F E σ hcm x
  have h2 := _root_.GlobalTheory.CompanionTheory.SW.MdBase.ideleModule_ideleEquiv_ofF F E σ hcm n
  have hu : (ofF n : (AF F ⊗[F] E)ˣ) = Units.map (sigR (AF F) σ).toMonoidHom x * x := Units.ext h
  rw [hu, map_mul, map_mul] at h2
  have h3 : ((IdeleGroup.ideleModule E (GroundTheory.BlockD.ThmBHecke.ideleEquiv F E (Units.map (sigR (AF F) σ).toMonoidHom x)) : ℝ)) *
      (IdeleGroup.ideleModule E (GroundTheory.BlockD.ThmBHecke.ideleEquiv F E x) : ℝ) = md n ^ 2 := h2
  rw [h1] at h3
  have hp : 0 < (IdeleGroup.ideleModule E (GroundTheory.BlockD.ThmBHecke.ideleEquiv F E x) : ℝ) :=
    (IdeleGroup.ideleModule E (GroundTheory.BlockD.ThmBHecke.ideleEquiv F E x)).2
  have hq : 0 < md n := (IdeleGroup.ideleModule F n).2
  nlinarith [sq_nonneg ((IdeleGroup.ideleModule E (GroundTheory.BlockD.ThmBHecke.ideleEquiv F E x) : ℝ) - md n)]

end GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LambdaInvolutionNegStatement
section
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4 GlobalTheory.CompanionTheory.TorusCh
open scoped Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lambda_involution_neg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (d : GL (Fin n) E) (e : Matrix (Fin n) (Fin n) E), e * e = e → ∀ t : GA E n, t ∈ adCent d → t.val * rm e = rm e * t.val → t.val * rm (sg d e) = rm (sg d e) * t.val → lam (sg d e) t = - lam e t := by
  first | exact @GlobalTheory.CompanionTheory.TorusAdj.lam_sg | exact GlobalTheory.CompanionTheory.TorusAdj.lam_sg | (intros; apply GlobalTheory.CompanionTheory.TorusAdj.lam_sg <;> assumption)
end

