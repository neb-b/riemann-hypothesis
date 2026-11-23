module

public import Mathlib
public import Formalism.PeriodIntegrals.Bundle0021
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FiniteAdelicComparison.MemLocFrom

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FiniteAdelicComparison.AdelicLatticeToLocalLattices
section
noncomputable section

namespace PI.FinKW.LocTo

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct
open Formalism.MainNotions.S (AutInst)

theorem psiV_tmul (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (e : I.E) (a : Formalism.MainNotions.S.Af I.F) :
    psiV I v (e ⊗ₜ[I.F] a) = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV I.F v a ⊗ₜ[I.F] e := by
  first
    | rfl
    | simp [psiV]

theorem psiV_inclE (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (e : I.E) :
    psiV I v (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F) e) =
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) e := by
  show psiV I v (e ⊗ₜ[I.F] (1 : Formalism.MainNotions.S.Af I.F)) = _
  rw [psiV_tmul, map_one]
  rfl

theorem ov_smul_eq (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (c : v.adicCompletionIntegers I.F)
    (t : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E) :
    c • t = ((c : v.adicCompletion I.F) ⊗ₜ[I.F] (1 : I.E)) * t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x e =>
    rw [TensorProduct.smul_tmul', Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    rfl
  | add a b ha hb => rw [smul_add, ha, hb, mul_add]

theorem ov_smul_vec (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (c : v.adicCompletionIntegers I.F)
    (z : Fin I.n → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E) :
    c • z = ((c : v.adicCompletion I.F) ⊗ₜ[I.F] (1 : I.E)) • z := by
  funext i
  exact ov_smul_eq I v c (z i)

def mulSet (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) : Subring (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) where
  carrier := {c | ∀ z ∈ Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E)),
    psiV I v c • z ∈ Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E))}
  mul_mem' := fun {a b} ha hb z hz => by
    rw [map_mul, mul_smul]
    exact ha _ (hb z hz)
  one_mem' := fun z hz => by
    rw [map_one, one_smul]
    exact hz
  add_mem' := fun {a b} ha hb z hz => by
    rw [map_add (f := _), add_smul]
    exact add_mem (ha z hz) (hb z hz)
  zero_mem' := fun z _ => by
    rw [map_zero, zero_smul]
    exact zero_mem _
  neg_mem' := fun {a} ha z hz => by
    rw [map_neg, neg_smul]
    exact neg_mem (ha z hz)

theorem inclR_smul_mem (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (o : 𝓞 I.E)
    (z : Fin I.n → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E)
    (hz : z ∈ Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E))) :
    ((1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) ⊗ₜ[I.F] (algebraMap (𝓞 I.E) I.E o)) • z ∈
      Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E)) := by
  induction hz using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨l, hl, rfl⟩ := hy
    have heq : ((1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) ⊗ₜ[I.F] (algebraMap (𝓞 I.E) I.E o)) •
        Formalism.L2.SG.Sub.ratV (F := I.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) l =
        Formalism.L2.SG.Sub.ratV (F := I.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) (o • l) := by
      funext i
      simp only [Formalism.L2.SG.Sub.ratV, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR, Pi.smul_apply, smul_eq_mul]
      show _ * ((1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) ⊗ₜ[I.F] l i) = (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) ⊗ₜ[I.F] (o • l) i
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, Pi.smul_apply, Algebra.smul_def]
    rw [heq]
    exact Submodule.subset_span ⟨o • l, I.L.smul_mem o hl, rfl⟩
  | zero => simp
  | add x y _ _ hx hy =>
    rw [smul_add]
    exact add_mem hx hy
  | smul c x _ hx =>
    rw [ov_smul_vec I v c x, smul_smul, mul_comm, ← smul_smul, ← ov_smul_vec I v c]
    exact Submodule.smul_mem _ c hx

theorem intAf_le_mulSet (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) :
    Formalism.MainNotions.S.IntAf I.F I.E ≤ mulSet I v := by
  rw [Formalism.MainNotions.S.IntAf, Formalism.UG.tensInt, Subring.closure_le]
  rintro _ (⟨⟨e, he⟩, rfl⟩ | ⟨⟨a, ha⟩, rfl⟩)
  · obtain ⟨o, rfl⟩ := he
    intro z hz
    rw [psiV_tmul, map_one]
    exact inclR_smul_mem I v o z hz
  · intro z hz
    rw [psiV_tmul]
    have h := Submodule.smul_mem _ (⟨a v, ha v⟩ : v.adicCompletionIntegers I.F) hz
    rw [ov_smul_vec] at h
    exact h

theorem mem_local_lattice_iff : PI.FinKW.MemLocTo := by
  intro I x hx v
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨l, rfl⟩ := hy
    have heq : PI.FinKW.vecV I v (fun i => Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F) ((l : Fin I.n → I.E) i)) =
        Formalism.L2.SG.Sub.ratV (F := I.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) (l : Fin I.n → I.E) := by
      funext i
      exact psiV_inclE I v _
    rw [heq]
    exact Submodule.subset_span ⟨l, l.2, rfl⟩
  | zero =>
    have h0 : PI.FinKW.vecV I v 0 = 0 := by
      funext i
      exact map_zero _
    rw [h0]
    exact zero_mem _
  | add a b _ _ ha hb =>
    have h0 : PI.FinKW.vecV I v (a + b) = PI.FinKW.vecV I v a + PI.FinKW.vecV I v b := by
      funext i
      exact map_add _ _ _
    rw [h0]
    exact add_mem ha hb
  | smul c y _ hy =>
    have h0 : PI.FinKW.vecV I v (c • y) = psiV I v (c : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) • PI.FinKW.vecV I v y := by
      funext i
      exact map_mul _ _ _
    rw [h0]
    exact intAf_le_mulSet I v c.2 _ hy

end PI.FinKW.LocTo
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FiniteAdelicComparison.LocFrom
section
noncomputable section

namespace PI.FinKW

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct
open Formalism.MainNotions.S (AutInst)

theorem ratV_add' {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    {n : ℕ} (a b : Fin n → E) :
    Formalism.L2.SG.Sub.ratV (F := F) R (a + b) = Formalism.L2.SG.Sub.ratV (F := F) R a + Formalism.L2.SG.Sub.ratV (F := F) R b := by
  funext i
  simp [Formalism.L2.SG.Sub.ratV]

theorem ratV_zero' {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    {n : ℕ} : Formalism.L2.SG.Sub.ratV (F := F) R (0 : Fin n → E) = 0 := by
  funext i
  simp [Formalism.L2.SG.Sub.ratV]

theorem ratV_zsmul' {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    {n : ℕ} (k : ℤ) (a : Fin n → E) :
    Formalism.L2.SG.Sub.ratV (F := F) R (k • a) = k • Formalism.L2.SG.Sub.ratV (F := F) R a := by
  funext i
  simp [Formalism.L2.SG.Sub.ratV]

theorem psiV_entry (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (a : Formalism.MainNotions.S.Af I.F) (e : I.E) :
    psiV I v (((1 : I.E) ⊗ₜ[I.F] a) * (e ⊗ₜ[I.F] (1 : Formalism.MainNotions.S.Af I.F))) =
      (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV I.F v a) ⊗ₜ[I.F] e := by
  simp [psiV, Algebra.TensorProduct.tmul_mul_tmul]

theorem smul_one_tmul' (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (r : v.adicCompletionIntegers I.F)
    (e : I.E) :
    r • ((1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) ⊗ₜ[I.F] e) = ((r : v.adicCompletion I.F) ⊗ₜ[I.F] e) := by
  rw [TensorProduct.smul_tmul']
  congr 1
  rw [Algebra.smul_def, mul_one]
  rfl

theorem memLocFrom_of (hI : InjV) : MemLocFrom := by
  intro I x hx
  obtain ⟨s, hs⟩ := Submodule.FG.restrictScalars (R := ℤ) I.L_fg
  let g : s → (Fin I.n → I.E) := fun j => (j : Fin I.n → I.E)
  have hgL : ∀ j, g j ∈ I.L := fun j => by
    have : (j : Fin I.n → I.E) ∈ I.L.restrictScalars ℤ := hs ▸ Submodule.subset_span j.2
    exact this
  have hloc : ∀ v : HeightOneSpectrum (𝓞 I.F), ∃ c : s → v.adicCompletionIntegers I.F,
      ∑ j, c j • Formalism.L2.SG.Sub.ratV (F := I.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) (g j) = vecV I v x := by
    intro v
    rw [← Submodule.mem_span_range_iff_exists_fun]
    have hle : Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E)) ≤
        Submodule.span (v.adicCompletionIntegers I.F)
          (Set.range fun j => Formalism.L2.SG.Sub.ratV (F := I.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) (g j)) := by
      rw [Formalism.L2.SG.Sub.latLoc, Submodule.span_le]
      rintro _ ⟨l, hl, rfl⟩
      have hl' : l ∈ Submodule.span ℤ (s : Set (Fin I.n → I.E)) := by rw [hs]; exact hl
      clear hl
      induction hl' using Submodule.span_induction with
      | mem y hy => exact Submodule.subset_span ⟨⟨y, hy⟩, rfl⟩
      | zero => rw [ratV_zero']; exact zero_mem _
      | add a b _ _ ha hb => rw [ratV_add']; exact add_mem ha hb
      | smul k a _ ha => rw [ratV_zsmul']; exact zsmul_mem ha k
    exact hle (hx v)
  choose c hc using hloc
  let α : s → Formalism.MainNotions.S.Af I.F := fun j =>
    RestrictedProduct.mk (fun v => ((c v j : v.adicCompletionIntegers I.F) : v.adicCompletion I.F))
      (Filter.Eventually.of_forall fun v => (c v j).2)
  have hαint : ∀ j, α j ∈ Formalism.UG.intAd I.F := fun j v => (c v j).2
  have hαmem : ∀ j, (1 : I.E) ⊗ₜ[I.F] α j ∈ Formalism.MainNotions.S.IntAf I.F I.E := fun j =>
    Subring.subset_closure (Or.inr ⟨⟨α j, hαint j⟩, rfl⟩)
  let y : Fin I.n → I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F :=
    ∑ j, (⟨_, hαmem j⟩ : Formalism.MainNotions.S.IntAf I.F I.E) •
      (fun i => Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F) (g j i))
  have hy : y ∈ I.Lf := Submodule.sum_mem _ fun j _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨g j, hgL j⟩, rfl⟩)
  have hyx : y = x := by
    funext i
    rw [← sub_eq_zero]
    apply hI I
    intro v
    rw [map_sub, sub_eq_zero]
    have hci := congrFun (hc v) i
    simp only [vecV] at hci
    rw [← hci]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [y, Finset.sum_apply, map_sum, Pi.smul_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Subring.smul_def, smul_eq_mul]
    change psiV I v (((1 : I.E) ⊗ₜ[I.F] α j) * (g j i ⊗ₜ[I.F] (1 : Formalism.MainNotions.S.Af I.F))) = _
    rw [psiV_entry]
    change _ = c v j • ((1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) ⊗ₜ[I.F] g j i)
    rw [smul_one_tmul']
    rfl
  exact hyx ▸ hy

end PI.FinKW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FiniteAdelicComparison.LocInj
section
noncomputable section

namespace PI.FinKW

open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.MainNotions.S (AutInst)

theorem psiV_tmul (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (x : I.E) (a : Formalism.MainNotions.S.Af I.F) :
    psiV I v (x ⊗ₜ[I.F] a) = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV I.F v a ⊗ₜ[I.F] x := by
  simp [psiV]


open Classical in
theorem coeff_psiV (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (z : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)
    (j : Module.Basis.ofVectorSpaceIndex I.F I.E) :
    TensorProduct.equivFinsuppOfBasisRight (Module.Basis.ofVectorSpace I.F I.E) (psiV I v z) j =
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV I.F v
        (TensorProduct.equivFinsuppOfBasisLeft (Module.Basis.ofVectorSpace I.F I.E) z j) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x a =>
    rw [psiV_tmul, TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply,
      TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply, map_smul]
  | add z w hz hw => simp only [map_add (f := _), Finsupp.add_apply, hz, hw]

theorem local_vector_injective : InjV := by
  classical
  intro I z hz
  apply (TensorProduct.equivFinsuppOfBasisLeft (Module.Basis.ofVectorSpace I.F I.E)).injective
  rw [map_zero]
  refine Finsupp.ext fun j => ?_
  rw [Finsupp.zero_apply]
  have hj : ∀ v, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV I.F v
      (TensorProduct.equivFinsuppOfBasisLeft (Module.Basis.ofVectorSpace I.F I.E) z j) = 0 := by
    intro v
    rw [← coeff_psiV, hz v, map_zero, Finsupp.zero_apply]

  apply RestrictedProduct.ext
  intro v
  exact hj v

end PI.FinKW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FiniteAdelicComparison.VecVMulVec
section
noncomputable section

namespace PI.FinKW

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct
open Formalism.MainNotions.S (AutInst)
open Formalism.L2.SG.AdBridge

theorem psiV_tauF (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F))
    (z : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F ⊗[I.F] I.E) :
    psiV I v (tauF I z) =
      Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV I.F v) (AlgHom.id I.F I.E) (prF I z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    rw [tauF_tmul]
    simp only [psiV, prF, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sndA, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgHom.coe_coe, Algebra.TensorProduct.comm_tmul,
      Algebra.TensorProduct.map_tmul]
    rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem vecV_mulVec (I : AutInst) (h : HAd I) (v : HeightOneSpectrum (𝓞 I.F))
    (x : Fin I.n → I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) :
    vecV I v (ofHAFin I h *ᵥ x) =
      ((Formalism.L2.SG.Sub.compV v (Formalism.UG.bc (prF I)
        (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig I.J h)) :
          GL (Fin I.n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E)) : Matrix _ _ _) *ᵥ vecV I v x := by
  funext i
  simp only [vecV]
  have := RingHom.map_mulVec (psiV I v).toRingHom (ofHAFin I h) x i
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at this
  rw [this]
  congr 1
  ext a b
  simp [ofHAFin, Formalism.L2.SG.Sub.compV, Formalism.UG.bc, psiV_tauF]

theorem finK_of (hT : MemLocTo) (hF : MemLocFrom) (hS : LiftV) : PI.AdBridgeSteps.FinK := by
  intro I h
  have hL : ∀ x, x ∈ I.Lf ↔ ∀ v, vecV I v x ∈ Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E)) :=
    fun x => ⟨hT I x, hF I x⟩
  constructor
  · intro hst v y
    obtain ⟨x, hxv, hxw⟩ := hS I v y
    have ex : x ∈ I.Lf ↔ y ∈ Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E)) := by
      rw [hL x]
      constructor
      · intro H
        have := H v
        rwa [hxv] at this
      · intro H w
        by_cases hw : w = v
        · subst hw
          rwa [hxv]
        · rw [hxw w hw]
          exact zero_mem _
    have egx : ofHAFin I h *ᵥ x ∈ I.Lf ↔
        ((Formalism.L2.SG.Sub.compV v (Formalism.UG.bc (prF I)
          (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig I.J h)) :
            GL (Fin I.n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E)) : Matrix _ _ _) *ᵥ y ∈
          Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E)) := by
      rw [hL]
      constructor
      · intro H
        have := H v
        rwa [vecV_mulVec, hxv] at this
      · intro H w
        rw [vecV_mulVec]
        by_cases hw : w = v
        · subst hw
          rwa [hxv]
        · rw [hxw w hw, Matrix.mulVec_zero]
          exact zero_mem _
    exact ex.symm.trans ((hst x).trans egx)
  · intro hK x
    rw [hL x, hL (ofHAFin I h *ᵥ x)]
    refine forall_congr' fun v => ?_
    rw [vecV_mulVec]
    exact hK v (vecV I v x)

end PI.FinKW
end
end

