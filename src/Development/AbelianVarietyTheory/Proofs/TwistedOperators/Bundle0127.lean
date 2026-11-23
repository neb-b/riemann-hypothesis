module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmRep
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0106
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RelativeJacquetPiExteriorTensorEquivNormalized
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PiTensorSmoothRepsExactEachFactor
section
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.SmGL

def piTensorHom {α : Type} {Γ : α → Type} [∀ i, Group (Γ i)] [∀ i, TopologicalSpace (Γ i)]
    {X Y : ∀ i, SmRep (Γ i)} (f : ∀ a, (X a).ρ.IntertwiningMap (Y a).ρ) :
    (piTensor fun a => (X a).ρ).IntertwiningMap (piTensor fun a => (Y a).ρ) where
  toLinearMap := PiTensorProduct.map fun a => (f a).toLinearMap
  isIntertwining' g := by
    ext x
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, piTensor_tprod,
      PiTensorProduct.map_tprod]
    congr 1
    funext a
    exact LinearMap.congr_fun ((f a).isIntertwining' (g a)) (x a)

theorem piTensorMap_add_eq_id {α : Type} [DecidableEq α] {Y : α → Type} [∀ a, AddCommGroup (Y a)]
    [∀ a, Module ℂ (Y a)] (i : α) (u v : ∀ a, Y a →ₗ[ℂ] Y a) (hu : ∀ a, a ≠ i → u a = LinearMap.id)
    (hv : ∀ a, a ≠ i → v a = LinearMap.id) (h : u i + v i = LinearMap.id) :
    PiTensorProduct.map u + PiTensorProduct.map v = LinearMap.id := by
  ext x
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.add_apply, PiTensorProduct.map_tprod,
    LinearMap.id_apply]

  have hx : ∀ w : ∀ a, Y a →ₗ[ℂ] Y a, (∀ a, a ≠ i → w a = LinearMap.id) →
      (fun a => w a (x a)) = Function.update x i (w i (x i)) := by
    intro w hw
    funext a
    by_cases ha : a = i
    · subst ha
      simp
    · rw [Function.update_of_ne ha, hw a ha, LinearMap.id_apply]
  rw [hx u hu, hx v hv, ← MultilinearMap.map_update_add, ← LinearMap.add_apply, h,
    LinearMap.id_apply, Function.update_eq_self]

theorem piTensor_exact_position : ∀ (α : Type) [Fintype α] [DecidableEq α] (Γ : α → Type) [∀ i, Group (Γ i)] [∀ i, TopologicalSpace (Γ i)] (A : ∀ i, GlobalTheory.SmGL.SmRep (Γ i)) (i : α) (B B₁ B₂ : GlobalTheory.SmGL.SmRep (Γ i)) (ι : B₁.ρ.IntertwiningMap B.ρ) (p : B.ρ.IntertwiningMap B₂.ρ), Function.Injective ι → Function.Surjective p → (∀ u, p (ι u) = 0) → (∀ v, p v = 0 → ∃ u, ι u = v) → ∃ (ι' : (GlobalTheory.SmGL.piTensor fun a => (Function.update A i B₁ a).ρ).IntertwiningMap (GlobalTheory.SmGL.piTensor fun a => (Function.update A i B a).ρ)) (p' : (GlobalTheory.SmGL.piTensor fun a => (Function.update A i B a).ρ).IntertwiningMap (GlobalTheory.SmGL.piTensor fun a => (Function.update A i B₂ a).ρ)), Function.Injective ι' ∧ Function.Surjective p' ∧ (∀ u, p' (ι' u) = 0) ∧ (∀ v, p' v = 0 → ∃ u, ι' u = v) := by
  intro α _ _ Γ _ _ A i B B₁ B₂ ι p hι hp hpι hker

  have key : ∀ a, ∃ (f : (Function.update A i B₁ a).ρ.IntertwiningMap (Function.update A i B a).ρ)
      (g : (Function.update A i B a).ρ.IntertwiningMap (Function.update A i B₂ a).ρ)
      (s : (Function.update A i B a).V →ₗ[ℂ] (Function.update A i B₁ a).V)
      (t : (Function.update A i B₂ a).V →ₗ[ℂ] (Function.update A i B a).V),
      s ∘ₗ f.toLinearMap = LinearMap.id ∧ g.toLinearMap ∘ₗ t = LinearMap.id ∧
      (a ≠ i → f.toLinearMap ∘ₗ s = LinearMap.id ∧ t ∘ₗ g.toLinearMap = LinearMap.id) ∧
      (a = i → f.toLinearMap ∘ₗ s + t ∘ₗ g.toLinearMap = LinearMap.id ∧
        g.toLinearMap ∘ₗ f.toLinearMap = 0) := by
    intro a
    by_cases ha : a = i
    · subst ha
      rw [Function.update_self, Function.update_self, Function.update_self]
      obtain ⟨t, ht⟩ := p.toLinearMap.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hp)
      obtain ⟨s₀, hs₀⟩ := ι.toLinearMap.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 hι)
      have hs₀' : ∀ u, s₀ (ι u) = u := fun u => LinearMap.congr_fun hs₀ u
      have ht' : ∀ z, p (t z) = z := fun z => LinearMap.congr_fun ht z
      refine ⟨ι, p, s₀ ∘ₗ (LinearMap.id - t ∘ₗ p.toLinearMap), t, ?_, ht, fun h => absurd rfl h,
        fun _ => ⟨?_, ?_⟩⟩
      · ext u
        simp [hpι, hs₀']
      · ext y

        obtain ⟨u, hu⟩ := hker (y - t (p y)) (by simp [ht'])
        simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply,
          Representation.IntertwiningMap.coe_toLinearMap]
        rw [← hu, hs₀', hu, sub_add_cancel]
      · ext u
        simp [hpι]
    · rw [Function.update_of_ne ha, Function.update_of_ne ha, Function.update_of_ne ha]
      exact ⟨Representation.IntertwiningMap.id _, Representation.IntertwiningMap.id _, LinearMap.id, LinearMap.id, by ext; rfl,
        by ext; rfl, fun _ => ⟨by ext; rfl, by ext; rfl⟩, fun h => absurd h ha⟩
  choose f g s t hsf hgt hne heq using key
  have hF : ∀ x, piTensorHom f x = PiTensorProduct.map (fun a => (f a).toLinearMap) x := fun _ => rfl
  have hG : ∀ x, piTensorHom g x = PiTensorProduct.map (fun a => (g a).toLinearMap) x := fun _ => rfl
  have hSF : PiTensorProduct.map s ∘ₗ PiTensorProduct.map (fun a => (f a).toLinearMap) = LinearMap.id := by
    rw [← PiTensorProduct.map_comp, funext hsf, PiTensorProduct.map_id]
  have hGT : PiTensorProduct.map (fun a => (g a).toLinearMap) ∘ₗ PiTensorProduct.map t = LinearMap.id := by
    rw [← PiTensorProduct.map_comp, funext hgt, PiTensorProduct.map_id]
  have hsum : PiTensorProduct.map (fun a => (f a).toLinearMap) ∘ₗ PiTensorProduct.map s +
      PiTensorProduct.map t ∘ₗ PiTensorProduct.map (fun a => (g a).toLinearMap) = LinearMap.id := by
    rw [← PiTensorProduct.map_comp, ← PiTensorProduct.map_comp]
    exact piTensorMap_add_eq_id i _ _ (fun a ha => (hne a ha).1) (fun a ha => (hne a ha).2)
      (heq i rfl).1
  have hGF : PiTensorProduct.map (fun a => (g a).toLinearMap) ∘ₗ
      PiTensorProduct.map (fun a => (f a).toLinearMap) = 0 := by
    rw [← PiTensorProduct.map_comp]
    ext x
    simp only [LinearMap.compMultilinearMap_apply, PiTensorProduct.map_tprod, LinearMap.zero_apply]

    exact MultilinearMap.map_coord_zero _ i (by rw [(heq i rfl).2, LinearMap.zero_apply])
  refine ⟨piTensorHom f, piTensorHom g, ?_, ?_, ?_, ?_⟩
  · intro x y hxy
    have := congrArg (PiTensorProduct.map s) hxy
    rw [hF, hF] at this
    simpa using (LinearMap.congr_fun hSF x).symm.trans (this.trans (LinearMap.congr_fun hSF y))
  · intro z
    exact ⟨PiTensorProduct.map t z, by rw [hG]; exact LinearMap.congr_fun hGT z⟩
  · intro u
    rw [hG, hF]
    exact LinearMap.congr_fun hGF u
  · intro v hv
    refine ⟨PiTensorProduct.map s v, ?_⟩
    rw [hG] at hv
    have := LinearMap.congr_fun hsum v
    simp only [LinearMap.add_apply, LinearMap.comp_apply, hv, map_zero, add_zero,
      LinearMap.id_apply] at this
    rw [hF]
    exact this

end GlobalTheory.SmGL
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RationalZeroIffRationalSubspace
section
noncomputable section

open Module

namespace GlobalTheory.QPosCompare

section Rat

variable {K X E : Type} [Field K] [AddCommGroup X] [Module K X] [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  {σ : K →+* ℂ} (j : X →ₛₗ[σ] E)

structure IsForm : Prop where
  basis : ∃ (n : ℕ) (b : Basis (Fin n) K X), LinearIndependent ℂ (fun i => j (b i)) ∧ Submodule.span ℂ (Set.range j) = ⊤
  inner : ∀ x y, ∃ a : K, inner ℂ (j x) (j y) = σ a

variable {j}

theorem IsForm.linInd (h : IsForm j) {ι : Type} [Fintype ι] {v : ι → X} (hv : LinearIndependent K v) :
    LinearIndependent ℂ fun i => j (v i) := by
  obtain ⟨n, b, hb, -⟩ := h.basis
  let _ := σ.toAlgebra
  have h1 : LinearIndependent K fun i => b.equivFun (v i) :=
    hv.map' (b.equivFun : X →ₗ[K] (Fin n → K)) b.equivFun.ker
  have h2 := (linearIndependent_algebraMap_comp_iff (S := ℂ)).2 h1
  have h3 := h2.map' (Fintype.linearCombination ℂ fun i => j (b i))
    (LinearMap.ker_eq_bot'.2 fun c hc => funext (Fintype.linearIndependent_iff.1 hb c
      (by simpa [Fintype.linearCombination_apply] using hc)))
  suffices he : (fun i => j (v i)) = (Fintype.linearCombination ℂ fun i => j (b i)) ∘
      fun i => (algebraMap K ℂ) ∘ b.equivFun (v i) by rw [he]; exact h3
  funext i
  simp only [Function.comp, Fintype.linearCombination_apply]
  conv_lhs => rw [← b.sum_equivFun (v i)]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smulₛₗ]; rfl

end Rat

section Twist

open Formalism.IndefR.Links

variable {E E' : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [NormedAddCommGroup E'] [InnerProductSpace ℂ E'] (s : Bool)

theorem tw_map_sub (V : Submodule ℂ E) : V.map (Tw.mkL s E) = Tw.sub s V := by
  ext x
  exact ⟨fun ⟨y, hy, h⟩ => h ▸ hy, fun hx => ⟨Tw.out x, hx, rfl⟩⟩

theorem tw_span (S : Set E) : Submodule.span ℂ (Tw.mk s '' S) = Tw.sub s (Submodule.span ℂ S) := by
  rw [← tw_map_sub, Submodule.map_span]; rfl

variable [FiniteDimensional ℂ E] [FiniteDimensional ℂ E'] {K X : Type} [Field K] [AddCommGroup X] [Module K X] {σ σ' : K →+* ℂ}
  (h : ∀ a, σ' a = cj s (σ a)) (j : X →ₛₗ[σ] E) (f : E →ₗ[ℂ] E')

end Twist

theorem isForm_of_pres {G Γ W K : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W] [Field K] [NumberField K]
    [StarRing K] {ι : Γ →* G} {S : Formalism.L2.DIV.CSD K} {σ : K →+* ℂ} {ρ : Γ →* Module.End ℂ W} {J : Subgroup G} {χ : J →* ℂˣ}
    (P : Formalism.IndefR.Bridge.ClassPres ι S σ ρ J χ) (M : Formalism.IndefR.Links.HMod (G → W))
    (hM : M.Is (Formalism.IndefR.Bridge.AdForms ι ρ J χ) (Formalism.IndefR.Bridge.adInner ι J P.y))
    (j : S.Forms →ₛₗ[σ] M.H) (hj : ∀ x, M.e (j x) = P.extL x) : IsForm j := by
  obtain ⟨hinj, hr, hip⟩ := hM
  obtain ⟨-, ⟨hli, hsp⟩, hiso⟩ := GlobalTheory.classPres_extMem_extBij_isom _ _ _ _ _ _ _ _ _ _ P
  refine ⟨⟨_, S.basis, ?_, ?_⟩, fun x y => ⟨S.csum x y, ?_⟩⟩
  · refine LinearIndependent.of_comp M.e ?_
    have : (M.e ∘ fun i => j (S.basis i)) = fun i => P.extL (S.basis i) := funext fun i => hj _
    rw [this]; exact hli
  · apply Submodule.map_injective_of_injective hinj
    rw [Submodule.map_span, Submodule.map_top, hr, ← Set.range_comp]
    have : (M.e ∘ j) = P.extL := funext hj
    rw [this]; exact hsp
  · rw [hip, hj, hj]; exact hiso x y

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S NumberField IsDedekindDomain Polynomial
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open GlobalTheory.IndefiniteRowSideFullHecke.PositiveDimensionTuples

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Compare

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A)

theorem lPos_iff_ne_bot : R.LPos F ↔ ∀ b, (A.fam.R A.μ0).inV0 (F.lvl b) ((R.toCx F).Z A.μ0) ≠ ⊥ :=
  forall_congr' fun b => pos_iff_ne_bot R F b


variable {R} in
theorem isForm_jX (h : R.IsModels) (t : T) : IsForm (R.jX t) :=
  isForm_of_pres (R.B.R t).pres (R.HX t) (h.HX t) (R.jX t) (h.jX t)

end Compare

end GlobalTheory.QPosCompare

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelativeJacquetFunctorPiTensorEquiv
section
open GlobalTheory.PRep GlobalTheory.SmGL
open GlobalTheory.JacPiTensor (qlift mk_qlift descend descend_mk)
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.RelJacTensor

section Spec

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [LinearOrder β]
  {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]
  {c : α → β → Type} [∀ i j, Fintype (c i j)] [∀ i j, DecidableEq (c i j)]
  (e' : ∀ i, (Σ j, c i j) ≃ m i) {X : α → Type} [∀ a, AddCommGroup (X a)]
  [∀ a, Module ℂ (X a)] (ρ : ∀ a, Representation ℂ (GL (m a) k) (X a))

theorem piTensor_mulSingle (a : α) (g : GL (m a) k) (x : ∀ j, X j) :
    piTensor ρ (Pi.mulSingle a g) (PiTensorProduct.tprod ℂ x) =
      PiTensorProduct.tprod ℂ (Function.update x a (ρ a g (x a))) := by
  rw [piTensor_tprod]
  congr 1
  funext j
  by_cases h : j = a
  · subst h
    simp
  · simp [h]

def qf : (∀ a, X a) →ₘₗ[ℂ] Jacquet (piTensor ρ) (relUnip k e') :=
  (twKer (piTensor ρ) (relUnip k e') 1).mkQ.compMultilinearMap (PiTensorProduct.tprod ℂ)

theorem qf_update (v : ∀ a, X a) (i : α) (w : X i)
    (hw : w ∈ twKer (ρ i) (unipRad k (e' i)) 1) : qf e' ρ (Function.update v i w) = 0 := by
  unfold twKer at hw
  induction hw using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨n, y, rfl⟩ := hz
    have hu : (Pi.mulSingle (M := fun a => GL (m a) k) i (n : GL (m i) k)) ∈ relUnip k e' := by
      simp only [relUnip, Subgroup.mem_pi]
      intro j _
      by_cases h : j = i
      · subst h
        simpa using n.2
      · rw [Pi.mulSingle_eq_of_ne h]
        exact one_mem _
    have h1 : PiTensorProduct.tprod ℂ (Function.update v i (ρ i (n : GL (m i) k) y)) =
        piTensor ρ (Pi.mulSingle (M := fun a => GL (m a) k) i (n : GL (m i) k))
          (PiTensorProduct.tprod ℂ (Function.update v i y)) := by
      rw [piTensor_mulSingle]
      simp
    rw [qf, LinearMap.compMultilinearMap_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
      MonoidHom.one_apply, Units.val_one, one_smul, MultilinearMap.map_update_sub, h1]
    exact Submodule.subset_span ⟨⟨_, hu⟩, PiTensorProduct.tprod ℂ (Function.update v i y), by simp⟩
  | zero => simp [qf]
  | add z z' _ _ hz hz' => rw [MultilinearMap.map_update_add, hz, hz', add_zero]
  | smul r z _ hz => rw [MultilinearMap.map_update_smul, hz, smul_zero]

end Spec

section Spec2

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [LinearOrder β]
  {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]
  {c : α → β → Type} [∀ i j, Fintype (c i j)] [∀ i j, DecidableEq (c i j)]
  (e' : ∀ i, (Σ j, c i j) ≃ m i) {X : α → Type} [∀ a, AddCommGroup (X a)]
  [∀ a, Module ℂ (X a)] (ρ : ∀ a, Representation ℂ (GL (m a) k) (X a))

def qmap : (⨂[ℂ] a, X a) →ₗ[ℂ] ⨂[ℂ] a, Jacquet (ρ a) (unipRad k (e' a)) :=
  PiTensorProduct.map fun a => (twKer (ρ a) (unipRad k (e' a)) 1).mkQ

theorem qmap_tprod (x : ∀ a, X a) :
    qmap e' ρ (PiTensorProduct.tprod ℂ x) =
      PiTensorProduct.tprod ℂ fun a => (Submodule.Quotient.mk (x a) : Jacquet (ρ a) (unipRad k (e' a))) := by
  simp only [qmap, PiTensorProduct.map_tprod, Submodule.mkQ_apply]

theorem qmap_comp (u : ∀ a, GL (m a) k) (hu : u ∈ relUnip k e') :
    qmap e' ρ ∘ₗ piTensor ρ u = qmap e' ρ := by
  have hu' : ∀ a, u a ∈ unipRad k (e' a) := by
    intro a
    have h := hu
    simp only [relUnip, Subgroup.mem_pi] at h
    exact h a (Set.mem_univ a)
  refine PiTensorProduct.ext (MultilinearMap.ext fun x => ?_)
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, piTensor_tprod, qmap_tprod]
  congr 1
  funext a
  rw [Submodule.Quotient.eq]
  exact Submodule.subset_span ⟨⟨u a, hu' a⟩, x a, by simp⟩

theorem twKer_le_ker : twKer (piTensor ρ) (relUnip k e') 1 ≤ LinearMap.ker (qmap e' ρ) := by
  rw [twKer, Submodule.span_le]
  rintro _ ⟨n, y, rfl⟩
  simp only [SetLike.mem_coe, LinearMap.mem_ker, MonoidHom.one_apply, Units.val_one, one_smul, map_sub,
    sub_eq_zero]
  exact LinearMap.congr_fun (qmap_comp e' ρ (n : ∀ a, GL (m a) k) n.2) y

def fwd : Jacquet (piTensor ρ) (relUnip k e') →ₗ[ℂ] ⨂[ℂ] a, Jacquet (ρ a) (unipRad k (e' a)) :=
  (twKer (piTensor ρ) (relUnip k e') 1).liftQ (qmap e' ρ) (twKer_le_ker e' ρ)

def bwd : (⨂[ℂ] a, Jacquet (ρ a) (unipRad k (e' a))) →ₗ[ℂ] Jacquet (piTensor ρ) (relUnip k e') :=
  PiTensorProduct.lift (descend (qf e' ρ) (qf_update e' ρ))

theorem bwd_tprod (q : ∀ a, Jacquet (ρ a) (unipRad k (e' a))) :
    bwd e' ρ (PiTensorProduct.tprod ℂ q) = Submodule.Quotient.mk (PiTensorProduct.tprod ℂ
      fun i => qlift (fun a => twKer (ρ a) (unipRad k (e' a)) 1) i (q i)) := by
  rw [bwd, PiTensorProduct.lift.tprod]
  rfl

theorem bwd_tprod_mk (x : ∀ a, X a) :
    bwd e' ρ (PiTensorProduct.tprod ℂ fun a => (Submodule.Quotient.mk (x a) : Jacquet (ρ a) (unipRad k (e' a)))) =
      Submodule.Quotient.mk (PiTensorProduct.tprod ℂ x) := by
  rw [bwd, PiTensorProduct.lift.tprod, descend_mk]
  rfl

theorem fwd_mk_tprod' (x : ∀ a, X a) :
    fwd e' ρ (Submodule.Quotient.mk (PiTensorProduct.tprod ℂ x)) =
      PiTensorProduct.tprod ℂ fun a => (Submodule.Quotient.mk (x a) : Jacquet (ρ a) (unipRad k (e' a))) := by
  rw [fwd, Submodule.liftQ_apply, qmap_tprod]

def jacEquiv : Jacquet (piTensor ρ) (relUnip k e') ≃ₗ[ℂ] ⨂[ℂ] a, Jacquet (ρ a) (unipRad k (e' a)) :=
  LinearEquiv.ofLinear (fwd e' ρ) (bwd e' ρ)
    (by
      refine PiTensorProduct.ext (MultilinearMap.ext fun q => ?_)
      rw [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, bwd_tprod, fwd_mk_tprod']
      simp only [mk_qlift, LinearMap.compMultilinearMap_apply, LinearMap.id_apply])
    (by
      refine Submodule.linearMap_qext _ (PiTensorProduct.ext (MultilinearMap.ext fun x => ?_))
      rw [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, LinearMap.comp_apply, Submodule.mkQ_apply,
        fwd_mk_tprod', bwd_tprod_mk, LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, LinearMap.id_apply,
        Submodule.mkQ_apply])

theorem relJac_piTensor :
    Nonempty ((relJac e' (piTensor ρ)).Equiv (piTensor fun a => GlobalTheory.SmGL.jac (e' a) (ρ a))) := by
  refine ⟨Representation.Equiv.mk (jacEquiv e' ρ) fun g => ?_⟩
  refine Submodule.linearMap_qext _ (PiTensorProduct.ext (MultilinearMap.ext fun x => ?_))
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, Submodule.mkQ_apply,
    LinearEquiv.coe_coe, jacEquiv, LinearEquiv.ofLinear_apply, relJac_mk, piTensor_tprod, relEmb_apply,
    map_smul, fwd_mk_tprod', jac_mk, MultilinearMap.map_smul_univ, RingHom.id_apply, relDeltaHalf_apply]
  congr 1
  rw [← Finset.prod_inv_distrib, Units.coe_prod]

end Spec2

theorem relJac_piTensor_equiv : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (α β : Type) [Fintype α] [Fintype β] [LinearOrder β]
    (m : α → Type) [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]
    (c : α → β → Type) [∀ i j, Fintype (c i j)] [∀ i j, DecidableEq (c i j)]
    (f : ∀ i, (Σ j, c i j) ≃ m i) (X : α → Type) [∀ i, AddCommGroup (X i)] [∀ i, Module ℂ (X i)]
    (ρ : ∀ i, Representation ℂ (GL (m i) k) (X i)),
    Nonempty ((relJac f (piTensor ρ)).Equiv (piTensor fun i => GlobalTheory.SmGL.jac (f i) (ρ i))) := by
  intro k _ _ _ _ α β _ _ _ m _ _ c _ _ f X _ _ ρ
  classical
  exact relJac_piTensor f ρ

end GlobalTheory.RelJacTensor
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TensorProductDeterminesFactorClasses
section
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.TensorFactorUnique

open GlobalTheory.SmGL

variable {β : Type} [Fintype β] [DecidableEq β] {X : β → Type} [∀ a, AddCommGroup (X a)]
  [∀ a, Module ℂ (X a)]

def contr (l : ∀ a, X a →ₗ[ℂ] ℂ) (j : β) : (PiTensorProduct ℂ X) →ₗ[ℂ] X j := GlobalTheory.MultilinearContraction.contract l j

theorem contr_tprod (l : ∀ a, X a →ₗ[ℂ] ℂ) (j : β) (x : ∀ a, X a) :
    contr l j (PiTensorProduct.tprod ℂ x) = (∏ i ∈ Finset.univ.erase j, l i (x i)) • x j :=
  GlobalTheory.MultilinearContraction.contract_tprod l j x

theorem exists_contr_ne_zero (j : β) {y : PiTensorProduct ℂ X} (hy : y ≠ 0) :
    ∃ l : ∀ a, X a →ₗ[ℂ] ℂ, contr l j y ≠ 0 := by
  let b := fun a => Module.Free.chooseBasis ℂ (X a)
  let B := Basis.piTensorProduct b
  obtain ⟨p, hp⟩ : ∃ p, B.repr y p ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hy (B.repr.map_eq_zero_iff.1 (Finsupp.ext hcon))
  refine ⟨fun a => (b a).coord (p a), fun h => hp ?_⟩
  have e : (b j).coord (p j) ∘ₗ contr (fun a => (b a).coord (p a)) j = B.coord p := by
    ext w
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, contr_tprod, map_smul,
      Module.Basis.coord_apply, B, Basis.piTensorProduct_repr_tprod_apply, smul_eq_mul]
    exact Finset.prod_erase_mul _ _ (Finset.mem_univ j)
  have := LinearMap.congr_fun e y
  rw [LinearMap.comp_apply, h, map_zero] at this
  exact this.symm

variable {Γ : β → Type} [∀ a, Group (Γ a)]

theorem contr_mulSingle (ρ : ∀ a, Representation ℂ (Γ a) (X a)) (l : ∀ a, X a →ₗ[ℂ] ℂ) (j : β)
    (g : Γ j) (y : PiTensorProduct ℂ X) :
    contr l j (piTensor ρ (Pi.mulSingle j g) y) = ρ j g (contr l j y) := by
  induction y using PiTensorProduct.induction_on with
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | smul_tprod c x =>
    simp only [map_smul, piTensor_tprod, contr_tprod, Pi.mulSingle_eq_same]
    congr 2
    exact Finset.prod_congr rfl fun a ha => by
      rw [Pi.mulSingle_eq_of_ne (Finset.ne_of_mem_erase ha), map_one, Module.End.one_apply]


omit [Fintype β] in
theorem tprod_update_mulSingle (ρ : ∀ a, Representation ℂ (Γ a) (X a)) (x : ∀ a, X a) (j : β)
    (g : Γ j) (v : X j) :
    PiTensorProduct.tprod ℂ (Function.update x j (ρ j g v)) =
      piTensor ρ (Pi.mulSingle j g) (PiTensorProduct.tprod ℂ (Function.update x j v)) := by
  rw [piTensor_tprod]
  congr 1
  funext a
  by_cases h : a = j
  · subst h; simp
  · simp [h, Pi.mulSingle_eq_of_ne h]

theorem cl_eq_of_piTensor_equiv : ∀ (β : Type) [Fintype β] (Γ : β → Type) [∀ j, Group (Γ j)] [∀ j, TopologicalSpace (Γ j)] (s s' : ∀ j, GlobalTheory.SmGL.IrrRep (Γ j)), Nonempty ((GlobalTheory.SmGL.piTensor fun j => (s j).ρ).Equiv (GlobalTheory.SmGL.piTensor fun j => (s' j).ρ)) → ∀ j, (s j).cl = (s' j).cl := by
  intro β _ Γ _ _ s s' ⟨φ⟩ j
  classical
  haveI := fun a => nontrivial_of_irreducible (s a).irr
  let b := fun a => Module.Free.chooseBasis ℂ (s a).V
  let p : ∀ a, Module.Free.ChooseBasisIndex ℂ (s a).V := fun a => (b a).index_nonempty.some
  let x : ∀ a, (s a).V := fun a => b a (p a)
  have hx : PiTensorProduct.tprod ℂ x ≠ 0 := by
    have := (Basis.piTensorProduct b).ne_zero p
    rwa [Basis.piTensorProduct_apply] at this
  have hy : φ (PiTensorProduct.tprod ℂ x) ≠ 0 := fun h => hx ((map_eq_zero_iff φ φ.injective).1 h)
  obtain ⟨l, hl⟩ := exists_contr_ne_zero j hy
  let ψ : (s j).ρ.IntertwiningMap (s' j).ρ :=
    { toLinearMap := contr l j ∘ₗ φ.toLinearMap ∘ₗ (PiTensorProduct.tprod ℂ).toLinearMap x j
      isIntertwining' := fun g => by
        ext v
        simp only [LinearMap.comp_apply, MultilinearMap.toLinearMap_apply]
        rw [tprod_update_mulSingle (fun a => (s a).ρ), ← contr_mulSingle (fun a => (s' a).ρ)]
        congr 1
        exact LinearMap.congr_fun (φ.isIntertwining' (Pi.mulSingle j g)) _ }
  have hψ : ψ ≠ 0 := fun h => hl (by
    have : ψ (x j) = 0 := by rw [h]; rfl
    rw [← this]
    show _ = contr l j (φ (PiTensorProduct.tprod ℂ (Function.update x j (x j))))
    rw [Function.update_eq_self])
  haveI := (s j).irr
  haveI := (s' j).irr
  have hb := (Representation.IsIrreducible.bijective_or_eq_zero ψ).resolve_right hψ
  exact IrrRep.cl_eq_iff.2 ⟨ψ.ofBijective hb⟩

end GlobalTheory.TensorFactorUnique
end
end

