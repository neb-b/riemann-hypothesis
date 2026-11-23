module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.Bundle0003
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.Bundle0001
public import Formalism.PeriodIntegrals.Bundle0013
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalDualGenerator.Bundle0001
public import Formalism.PeriodIntegrals.Bundle0007
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0006

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.ChiZeroRight
section
noncomputable section

namespace PI.UnitaryGroupMassFormula.LocJacTyp.Sd

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain Topology Filter PI.LocJacTyp
open PI.VolStabSW.SdUniqW
open scoped TensorProduct

attribute [local instance] PI.VolStabSW.secondCountable_Fv PI.VolStabSW.locallyCompact_Fv finDim

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F)) (ψ : AddChar (AF F) ℂ)

def chi (ι : Type) [Fintype ι] (x y : ι → Fv F v ⊗[F] E) : ℂ :=
  psiV F ψ v (∑ i, Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (x i * y i))

open Classical in
theorem sdE_eq (ι : Type) [Fintype ι] :
    sdE (E := E) ψ v ι = if h : ∃ μ : Measure (ι → Fv F v ⊗[F] E), SelfDual μ (chi (E := E) v ψ ι)
      then h.choose else 0 := rfl

theorem chi_add_left (ι : Type) [Fintype ι] (x t y : ι → Fv F v ⊗[F] E) :
    chi (E := E) v ψ ι (t + x) y = chi (E := E) v ψ ι t y * chi (E := E) v ψ ι x y := by
  simp only [chi, Pi.add_apply, add_mul, map_add (f := _), Finset.sum_add_distrib, psiV_add']

theorem chi_symm (ι : Type) [Fintype ι] (x y : ι → Fv F v ⊗[F] E) :
    chi (E := E) v ψ ι x y = chi (E := E) v ψ ι y x := by
  simp only [chi, mul_comm]

theorem chi_zero_right (ι : Type) [Fintype ι] (x : ι → Fv F v ⊗[F] E) :
    chi (E := E) v ψ ι x 0 = 1 := by
  simp [chi, psiV_zero]

theorem chi_smul (ι : Type) [Fintype ι] (c : Fv F v) (x y : ι → Fv F v ⊗[F] E) :
    chi (E := E) v ψ ι (c • x) y = chi (E := E) v ψ ι x (c • y) := by
  simp only [chi, Pi.smul_apply, smul_mul_assoc, mul_smul_comm]

def D1 : Set (Fv F v ⊗[F] E) :=
  {y | ∀ x ∈ OEv (E := E) v, psiV F ψ v (Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (x * y)) = 1}

def Dbox (ι : Type) : Set (ι → Fv F v ⊗[F] E) := Set.univ.pi fun _ => D1 (E := E) v ψ

theorem ann_obox (ι : Type) [Fintype ι] :
    ann (chi (E := E) v ψ ι) (Obox (E := E) v ι) = Dbox (E := E) v ψ ι := by
  classical
  ext y
  constructor
  · intro hy i _ x hx
    have h := hy (Pi.single i x) (fun j _ => by
      by_cases hj : j = i
      · subst hj; simpa using hx
      · simpa [Pi.single_apply, hj] using oev_zero v)
    have hs : ∑ j, Algebra.trace (Fv F v) (Fv F v ⊗[F] E) ((Pi.single i x : ι → Fv F v ⊗[F] E) j * y j) =
        Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (x * y i) := by
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hj
        simp [Pi.single_apply, hj]
      · simp
    simp only [chi] at h
    rwa [hs] at h
  · intro hy x hx
    simp only [chi]
    rw [psiV_sum]
    exact Finset.prod_eq_one fun i _ => hy i trivial (x i) (hx i trivial)

def ObS (ι : Type) : AddSubgroup (ι → Fv F v ⊗[F] E) := AddSubgroup.pi Set.univ fun _ => Osub (E := E) v

theorem coe_ObS (ι : Type) : (ObS (E := E) v ι : Set (ι → Fv F v ⊗[F] E)) = Obox (E := E) v ι := by
  simp [ObS, AddSubgroup.coe_pi, Obox, Osub]

theorem isCompact_obox (ι : Type) [Fintype ι] : IsCompact (Obox (E := E) v ι) :=
  isCompact_univ_pi fun _ => isCompact_oev v

theorem isOpen_obox (ι : Type) [Fintype ι] : IsOpen (Obox (E := E) v ι) :=
  isOpen_set_pi Set.finite_univ fun _ _ => isOpen_oev v

theorem zero_mem_obox (ι : Type) : (0 : ι → Fv F v ⊗[F] E) ∈ Obox (E := E) v ι :=
  fun _ _ => oev_zero v

variable [SecondCountableTopology (Fv F v ⊗[F] E)]

theorem sd_test (ι : Type) [Fintype ι] (μ : Measure (ι → Fv F v ⊗[F] E))
    (hμ : SelfDual μ (chi (E := E) v ψ ι)) (hA : MeasurableSet (Dbox (E := E) v ψ ι))
    (hfin : μ (Dbox (E := E) v ψ ι) < ⊤) :
    μ.real (Obox (E := E) v ι) * μ.real (Dbox (E := E) v ψ ι) = 1 := by
  have := hμ.1
  set L := ObS (E := E) v ι
  have hLo : IsOpen (L : Set (ι → Fv F v ⊗[F] E)) := by rw [coe_ObS]; exact isOpen_obox v ι
  have hLc : IsCompact (L : Set (ι → Fv F v ⊗[F] E)) := by rw [coe_ObS]; exact isCompact_obox v ι
  have hcl : IsClopen (L : Set (ι → Fv F v ⊗[F] E)) := ⟨AddSubgroup.isClosed_of_isOpen L hLo, hLo⟩
  set Φ : (ι → Fv F v ⊗[F] E) → ℂ := (L : Set (ι → Fv F v ⊗[F] E)).indicator (fun _ => (1 : ℂ))
  have hΦc : Continuous Φ := by
    classical
    rw [show Φ = (L : Set _).piecewise (fun _ => (1 : ℂ)) (fun _ => 0) from
      (Set.piecewise_eq_indicator).symm]
    exact continuous_const.piecewise (by simp [hcl.frontier_eq]) continuous_const
  have hΦs : HasCompactSupport Φ := HasCompactSupport.intro hLc fun x hx => Set.indicator_of_notMem hx _
  have hχ : ∀ x t y, chi (E := E) v ψ ι (t + x) y = chi (E := E) v ψ ι t y * chi (E := E) v ψ ι x y :=
    chi_add_left v ψ ι
  have hT : ∀ y, ∫ x, Φ x * chi (E := E) v ψ ι x y ∂μ =
      (Dbox (E := E) v ψ ι).indicator (fun _ => ((μ.real (Obox (E := E) v ι) : ℝ) : ℂ)) y := by
    intro y
    have h := PI.VolStabSW.SdUniqW.transform_indicator μ (chi (E := E) v ψ ι) hχ L hLo y
    rw [coe_ObS, ann_obox] at h
    exact h
  have hI : Integrable (fun y => ∫ x, Φ x * chi (E := E) v ψ ι x y ∂μ) μ := by
    simp only [hT]
    rw [integrable_indicator_iff hA]
    exact integrableOn_const hfin.ne
  have h := hμ.2 Φ hΦc hΦs hI 0
  simp only [hT] at h
  simp only [chi_zero_right, mul_one, neg_zero] at h
  rw [integral_indicator_const _ hA] at h
  have h0 : Φ 0 = 1 := by simp [Φ, L.zero_mem]
  rw [h0] at h
  have h2 : ((μ.real (Dbox (E := E) v ψ ι) * μ.real (Obox (E := E) v ι) : ℝ) : ℂ) = 1 := by
    rw [← h]; simp [Complex.real_smul]
  have h3 : μ.real (Dbox (E := E) v ψ ι) * μ.real (Obox (E := E) v ι) = 1 := by exact_mod_cast h2
  linarith

end PI.UnitaryGroupMassFormula.LocJacTyp.Sd
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.KitSplit
section
noncomputable section

namespace PI.UnitaryGroupMassFormula.LocJacTyp

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain PI.LocJacTyp
open scoped TensorProduct

attribute [local instance] PI.VolStabSW.secondCountable_Fv PI.VolStabSW.locallyCompact_Fv
attribute [local instance] Sd.finDim

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F))

structure SD where
  e : Fv F v ⊗[F] E
  he : IsIdempotentElem e
  h0 : e ≠ 0
  h1 : e ≠ 1
  hr : Module.finrank (Fv F v) (Fv F v ⊗[F] E) = 2
  hσ : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ e = 1 - e

namespace SD

variable {σ v} (D : SD σ v)

def p (i : Fin 2) : (Fv F v ⊗[F] E) →ₐ[Fv F v] Fv F v := PI.LocDualGen.EpS.pr D.hr D.e D.he D.h0 D.h1 i

theorem decomp (z : Fv F v ⊗[F] E) : z = D.p 0 z • D.e + D.p 1 z • (1 - D.e) :=
  PI.LocDualGen.EpS.decomp D.hr D.e D.he D.h0 D.h1 z

theorem p_pair (s t : Fv F v) : D.p 0 (s • D.e + t • (1 - D.e)) = s ∧ D.p 1 (s • D.e + t • (1 - D.e)) = t :=
  PI.LocDualGen.EpS.repr_pair D.hr D.e D.he D.h0 D.h1 s t

theorem ext {z w : Fv F v ⊗[F] E} (h0 : D.p 0 z = D.p 0 w) (h1 : D.p 1 z = D.p 1 w) : z = w := by
  rw [D.decomp z, D.decomp w, h0, h1]

theorem p_e : D.p 0 D.e = 1 ∧ D.p 1 D.e = 0 := PI.LocDualGen.EpS.pr_e D.hr D.e D.he D.h0 D.h1

theorem p_f : D.p 0 (1 - D.e) = 0 ∧ D.p 1 (1 - D.e) = 1 := PI.LocDualGen.EpS.pr_f D.hr D.e D.he D.h0 D.h1

theorem p_sc (i : Fin 2) (t : Fv F v) : D.p i (sc (E := E) v t) = t := by
  have : sc (E := E) v t = algebraMap (Fv F v) (Fv F v ⊗[F] E) t := rfl
  rw [this, AlgHom.commutes]; rfl

theorem p_sig (z : Fv F v ⊗[F] E) :
    D.p 0 (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ z) = D.p 1 z ∧ D.p 1 (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ z) = D.p 0 z := by
  have h : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ z = D.p 1 z • D.e + D.p 0 z • (1 - D.e) := by
    conv_lhs => rw [D.decomp z]
    rw [map_add (f := _), sigR_smul, sigR_smul, map_sub, map_one, D.hσ, sub_sub_cancel, add_comm]
  rw [h]
  exact D.p_pair _ _

theorem norm_eq (z : Fv F v ⊗[F] E) : Algebra.norm (Fv F v) z = D.p 0 z * D.p 1 z := by
  rw [Algebra.norm_eq_matrix_det (PI.LocDualGen.EpS.bas D.hr D.e D.he D.h0 D.h1) z, Matrix.det_fin_two,
    Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul,
    Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul,
    PI.LocDualGen.EpS.bas0, PI.LocDualGen.EpS.bas1]
  have h0 := congrArg (fun w => (PI.LocDualGen.EpS.bas D.hr D.e D.he D.h0 D.h1).repr w 0) (PI.LocDualGen.EpS.mul_decomp D.hr D.e D.he D.h0 D.h1 z D.e)
  have h1 := congrArg (fun w => (PI.LocDualGen.EpS.bas D.hr D.e D.he D.h0 D.h1).repr w 1) (PI.LocDualGen.EpS.mul_decomp D.hr D.e D.he D.h0 D.h1 z D.e)
  have h2 := congrArg (fun w => (PI.LocDualGen.EpS.bas D.hr D.e D.he D.h0 D.h1).repr w 0)
    (PI.LocDualGen.EpS.mul_decomp D.hr D.e D.he D.h0 D.h1 z (1 - D.e))
  have h3 := congrArg (fun w => (PI.LocDualGen.EpS.bas D.hr D.e D.he D.h0 D.h1).repr w 1)
    (PI.LocDualGen.EpS.mul_decomp D.hr D.e D.he D.h0 D.h1 z (1 - D.e))
  rw [h0, h1, h2, h3]
  simp only [(PI.LocDualGen.EpS.repr_pair D.hr D.e D.he D.h0 D.h1 _ _).1,
    (PI.LocDualGen.EpS.repr_pair D.hr D.e D.he D.h0 D.h1 _ _).2]
  have pe := D.p_e
  have pf := D.p_f
  simp only [p, PI.LocDualGen.EpS.pr_apply] at pe pf
  rw [pe.1, pe.2, pf.1, pf.2]
  simp only [p, PI.LocDualGen.EpS.pr_apply]
  ring

end SD

def oevSub : Subring (Fv F v ⊗[F] E) where
  carrier := OEv (E := E) v
  mul_mem' := fun hx hy => oev_mul v hx hy
  one_mem' := oev_one v
  add_mem' := fun hx hy => Sd.oev_add v hx hy
  zero_mem' := Sd.oev_zero v
  neg_mem' := fun hx => Sd.oev_neg v hx

theorem tens_iff (x : Fv F v ⊗[F] E) :
    (Algebra.TensorProduct.comm F E (Fv F v)).symm x ∈
        PI.SplitIntLoc.tensInt (F := F) (Fv F v) (PI.SplitIntLoc.intOE E)
          (v.adicCompletionIntegers F).toSubring ↔ x ∈ OEv (E := E) v := by
  constructor
  · intro h
    have hle : PI.SplitIntLoc.tensInt (F := F) (Fv F v) (PI.SplitIntLoc.intOE E)
        (v.adicCompletionIntegers F).toSubring ≤
        (oevSub v).comap (Algebra.TensorProduct.comm F E (Fv F v)).toRingEquiv.toRingHom := by
      apply Subring.closure_le.2
      rintro y (⟨⟨a, ha⟩, rfl⟩ | ⟨⟨t, ht⟩, rfl⟩)
      · obtain ⟨b, rfl⟩ := ha
        show Algebra.TensorProduct.comm F E (Fv F v) (((algebraMap (𝓞 E) E) b) ⊗ₜ[F] (1 : Fv F v)) ∈
          OEv (E := E) v
        simp only [Algebra.TensorProduct.comm_tmul]
        exact Sd.inclR_mem (F := F) v b
      · show Algebra.TensorProduct.comm F E (Fv F v) ((1 : E) ⊗ₜ[F] t) ∈ OEv (E := E) v
        have h1 : Algebra.TensorProduct.comm F E (Fv F v) ((1 : E) ⊗ₜ[F] t) = t • (1 : Fv F v ⊗[F] E) := by
          simp [Algebra.TensorProduct.one_def, TensorProduct.smul_tmul']
        rw [h1]
        exact Sd.oev_smul v ht (oev_one v)
    have h2 := Subring.mem_comap.1 (hle h)
    have h3 : (Algebra.TensorProduct.comm F E (Fv F v)).toRingEquiv.toRingHom
        ((Algebra.TensorProduct.comm F E (Fv F v)).symm x) = x := by simp
    rw [h3] at h2
    exact h2
  · intro hx
    change x ∈ Submodule.span _ _ at hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, -, rfl⟩ := hy
      apply Subring.subset_closure
      left
      exact ⟨⟨(a : E), ⟨a, rfl⟩⟩, by simp [inclR]⟩
    | zero => simpa using zero_mem _
    | add y z _ _ hy hz => simpa only [map_add] using add_mem hy hz
    | smul t y _ hy =>
      have h1 : t • y = ((t : Fv F v) ⊗ₜ[F] (1 : E)) * y := by
        rw [show t • y = (t : Fv F v) • y from rfl, Algebra.smul_def]
        rfl
      rw [h1, map_mul]
      refine mul_mem ?_ hy
      apply Subring.subset_closure
      right
      exact ⟨⟨t, t.2⟩, by simp⟩

variable {σ v}

namespace SD

variable (D : SD σ v)

theorem mem_iff (x : Fv F v ⊗[F] E) :
    x ∈ OEv (E := E) v ↔ D.p 0 x ∈ v.adicCompletionIntegers F ∧ D.p 1 x ∈ v.adicCompletionIntegers F := by
  let f : (Fv F v ⊗[F] E) →ₐ[Fv F v] Fv F v × Fv F v := (D.p 0).prod (D.p 1)
  have hinj : Function.Injective f := fun z w h => D.ext (congrArg Prod.fst h) (congrArg Prod.snd h)
  have hsurj : Function.Surjective f := fun ab =>
    ⟨ab.1 • D.e + ab.2 • (1 - D.e), Prod.ext (D.p_pair _ _).1 (D.p_pair _ _).2⟩
  let spl : E ⊗[F] Fv F v ≃+* Fv F v × Fv F v :=
    (Algebra.TensorProduct.comm F E (Fv F v)).toRingEquiv.trans (RingEquiv.ofBijective f ⟨hinj, hsurj⟩)
  have hspl : ∀ a : Fv F v, spl ((1 : E) ⊗ₜ[F] a) = (a, a) := by
    intro a
    have h1 : spl ((1 : E) ⊗ₜ[F] a) = f (Algebra.TensorProduct.comm F E (Fv F v) ((1 : E) ⊗ₜ[F] a)) := rfl
    rw [h1, Algebra.TensorProduct.comm_tmul,
      show (a ⊗ₜ[F] (1 : E) : Fv F v ⊗[F] E) = algebraMap (Fv F v) (Fv F v ⊗[F] E) a from rfl,
      AlgHom.commutes]
    rfl
  have key := split_integral_local F E v spl hspl ((Algebra.TensorProduct.comm F E (Fv F v)).symm x)
  have hx : spl ((Algebra.TensorProduct.comm F E (Fv F v)).symm x) = f x := by
    show f (Algebra.TensorProduct.comm F E (Fv F v) ((Algebra.TensorProduct.comm F E (Fv F v)).symm x)) = f x
    rw [AlgEquiv.apply_symm_apply]
  rw [hx, tens_iff] at key
  exact key

end SD

theorem sigR_eq_congr (hfin : Module.finrank F E = 2) :
    ∃ τ : E ≃ₐ[F] E, ∀ z, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ z =
      Algebra.TensorProduct.congr (AlgEquiv.refl : Fv F v ≃ₐ[F] Fv F v) τ z := by
  have : Module.Finite F E := Module.finite_of_finrank_pos (by omega)
  refine ⟨AlgEquiv.ofBijective σ (AlgHom.bijective σ), fun z => rfl⟩

theorem exists_SD (hS : SplitHyp σ v) : Nonempty (SD σ v) := by
  obtain ⟨hfin, hσ, e, hee, he0, he1⟩ := hS
  have hr : Module.finrank (Fv F v) (Fv F v ⊗[F] E) = 2 := by
    rw [Module.finrank_baseChange]; exact hfin
  have he : IsIdempotentElem e := hee
  let P := PI.LocDualGen.EpS.pr hr e he he0 he1
  have dec := PI.LocDualGen.EpS.decomp hr e he he0 he1
  have pair := PI.LocDualGen.EpS.repr_pair hr e he he0 he1
  obtain ⟨τ, hτ⟩ := sigR_eq_congr (σ := σ) (v := v) hfin
  have hinj : Function.Injective (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ) := by
    intro z w h
    rw [hτ, hτ] at h
    exact (Algebra.TensorProduct.congr (AlgEquiv.refl : Fv F v ≃ₐ[F] Fv F v) τ).injective h
  set f := Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ e with hfdef
  have hfi : f * f = f := by rw [hfdef, ← map_mul, hee]
  have h01 : ∀ i, P i f = 0 ∨ P i f = 1 := by
    intro i
    have : P i f * P i f = P i f := by rw [← map_mul, hfi]
    have h2 : P i f * (P i f - 1) = 0 := by rw [mul_sub, this, mul_one, sub_self]
    rcases mul_eq_zero.1 h2 with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.1 h)
  have hfdec : f = P 0 f • e + P 1 f • (1 - e) := dec f
  refine ⟨⟨e, he, he0, he1, hr, ?_⟩⟩
  rcases h01 0 with a0 | a1 <;> rcases h01 1 with b0 | b1
  · exfalso
    apply he0
    apply hinj
    rw [map_zero, ← hfdef, hfdec, a0, b0]; simp
  · rw [← hfdef, hfdec, a0, b1]; simp
  · exfalso
    apply hσ
    have hfe : f = e := by rw [hfdec, a1, b0]; simp
    have hfix : ∀ z, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ z = z := by
      intro z
      conv_lhs => rw [dec z]
      rw [map_add, sigR_smul, sigR_smul, (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ).map_sub,
        (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ).map_one, ← hfdef, hfe, ← dec z]
    ext x
    have h1 := hfix ((1 : Fv F v) ⊗ₜ[F] x)
    have h2 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ ((1 : Fv F v) ⊗ₜ[F] x) = (1 : Fv F v) ⊗ₜ[F] (σ x) := by
      simp [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR]
    rw [h2] at h1
    exact Algebra.TensorProduct.includeRight_injective (algebraMap F (Fv F v)).injective h1
  · exfalso
    apply he1
    apply hinj
    rw [map_one, ← hfdef, hfdec, a1, b1]; simp

end PI.UnitaryGroupMassFormula.LocJacTyp
end
end

