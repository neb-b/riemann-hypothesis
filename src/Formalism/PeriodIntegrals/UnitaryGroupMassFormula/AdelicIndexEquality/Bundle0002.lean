module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicIndexEquality.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicIndexEquality.Commensurated
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FiniteAdelicComparison.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FiniteAdelicComparison.LocLift
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicIndexEquality.InertGen

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicIndexEquality.Assemble
section
noncomputable section

namespace PI.UnitaryGroupMassFormula.AdIndexEq

open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.MainNotions.S

theorem mod_q_hom : ModQHom := by
  unfold ModQHom
  intro G _ K hK
  have hk1 : ∀ k ∈ K, dIdx K k = 1 := by
    intro k hk
    unfold dIdx
    rw [Subgroup.relIndex_eq_one]
    intro y hy
    refine Subgroup.mem_map.2 ⟨k⁻¹ * y * k, K.mul_mem (K.mul_mem (K.inv_mem hk) hy) hk, ?_⟩
    simp [MulAut.conj_apply, mul_assoc]
  refine ⟨fun x y => modQ_mul K hK x y, fun k hk => ?_, fun x hx => ?_⟩
  · unfold modQ
    rw [hk1 k hk, hk1 k⁻¹ (K.inv_mem hk)]
    norm_num
  · unfold modQ at hx
    have hne : (dIdx K x⁻¹ : ℚ) ≠ 0 := by exact_mod_cast hK x⁻¹
    rw [div_eq_one_iff_eq hne] at hx
    exact_mod_cast hx

section Lift

variable (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F))

def liftFn (hL : LiftU) (g : Uv I v) : I.Gf := Classical.choose (hL I v g g.2)

theorem liftFn_spec (hL : LiftU) (g : Uv I v) :
    matV I v ((liftFn I v hL g : I.Gf) : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) = g ∧ SuppAt I v (liftFn I v hL g) :=
  Classical.choose_spec (hL I v g g.2)

theorem eq_liftFn (hL : LiftU) (hJ : MatVInj) (g : Uv I v) (y : I.Gf)
    (hy : matV I v (y : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) = g) (hs : SuppAt I v y) :
    y = liftFn I v hL g := by
  apply hJ I
  intro w
  by_cases hw : w = v
  · rw [hw, hy, (liftFn_spec I v hL g).1]
  · rw [hs w hw, (liftFn_spec I v hL g).2 w hw]

def liftHom (hL : LiftU) (hJ : MatVInj) : Uv I v →* I.Gf where
  toFun := liftFn I v hL
  map_one' := by
    symm
    apply eq_liftFn I v hL hJ 1 1
    · simp
    · intro w _
      simp
  map_mul' := by
    intro g h
    symm
    apply eq_liftFn I v hL hJ (g * h)
    · simp only [Subgroup.coe_mul, map_mul, Subgroup.coe_mul]
      rw [(liftFn_spec I v hL g).1, (liftFn_spec I v hL h).1]
    · intro w hw
      simp only [Subgroup.coe_mul, map_mul]
      rw [(liftFn_spec I v hL g).2 w hw, (liftFn_spec I v hL h).2 w hw, one_mul]

theorem liftHom_apply (hL : LiftU) (hJ : MatVInj) (g : Uv I v) :
    liftHom I v hL hJ g = liftFn I v hL g := rfl

def chiV (hC : KComm) (hL : LiftU) (hJ : MatVInj) : Uv I v →* ℚ where
  toFun g := modQ (PI.AdIndexEq.Ksub I) (liftHom I v hL hJ g)
  map_one' := by simp [modQ_one]
  map_mul' g h := by simp only [map_mul]; exact modQ_mul _ (hC I) _ _

private theorem modQ_eq_one_of_central {G : Type} [Group G] (K : Subgroup G) (y : G)
    (hy : ∀ x : G, y * x * y⁻¹ = x) : modQ K y = 1 := by
  have h1 : ∀ z : G, (∀ x : G, z * x * z⁻¹ = x) → dIdx K z = 1 := by
    intro z hz
    unfold dIdx
    rw [Subgroup.relIndex_eq_one]
    intro k hk
    exact Subgroup.mem_map.2 ⟨k, hk, by simp [MulAut.conj_apply, hz k]⟩
  have h2 : ∀ x : G, y⁻¹ * x * y⁻¹⁻¹ = x := by
    intro x
    have hx := hy x
    rw [inv_inv]
    calc y⁻¹ * x * y = y⁻¹ * (y * x * y⁻¹) * y := by rw [hx]
      _ = x := by group
  unfold modQ
  rw [h1 y hy, h1 y⁻¹ h2]
  norm_num

theorem chiV_props (hC : KComm) (hL : LiftU) (hJ : MatVInj) (hU : MatVU) (hK : KLocGlob) :
    (∀ g, 0 < chiV I v hC hL hJ g) ∧
    (∀ s : Uv I v, (∀ t : Uv I v, s * t = t * s) → chiV I v hC hL hJ s = 1) ∧
    (∀ s : Uv I v, (∃ m : ℕ, 1 ≤ m ∧
        (((s ^ m : Uv I v) : GL (Fin I.n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E)) ∈ Kv I v)) →
        chiV I v hC hL hJ s = 1) := by
  have hM := mod_q_hom I.Gf (PI.AdIndexEq.Ksub I) (hC I)
  have hpos : ∀ g, 0 < chiV I v hC hL hJ g := by
    intro g
    show 0 < modQ (PI.AdIndexEq.Ksub I) (liftHom I v hL hJ g)
    unfold modQ
    apply div_pos
    · exact_mod_cast Nat.pos_of_ne_zero (hC I _)
    · exact_mod_cast Nat.pos_of_ne_zero (hC I _)
  refine ⟨hpos, fun s hs => ?_, fun s hs => ?_⟩
  · show modQ (PI.AdIndexEq.Ksub I) (liftHom I v hL hJ s) = 1
    have hyv : matV I v ((liftHom I v hL hJ s : I.Gf) : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) = s := by
      rw [liftHom_apply]
      exact (liftFn_spec I v hL s).1
    have hys : SuppAt I v (liftHom I v hL hJ s) := by
      rw [liftHom_apply]
      exact (liftFn_spec I v hL s).2
    apply modQ_eq_one_of_central
    intro x
    apply hJ I
    intro w
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]
    by_cases hw : w = v
    · rw [hw]
      have hc := congrArg Subtype.val (hs ⟨_, hU I v x⟩)
      simp only [Subgroup.coe_mul, Subgroup.coe_mk] at hc
      rw [hyv, hc, mul_inv_cancel_right]
    · rw [hys w hw, one_mul, inv_one, mul_one]
  · obtain ⟨m, hm, hsm⟩ := hs
    have hpow : chiV I v hC hL hJ (s ^ m) = 1 := by
      show modQ (PI.AdIndexEq.Ksub I) (liftHom I v hL hJ (s ^ m)) = 1
      apply hM.2.1
      refine (hK I _).2 fun w => ?_
      rw [liftHom_apply]
      by_cases hw : w = v
      · rw [hw, (liftFn_spec I v hL (s ^ m)).1]
        exact hsm
      · rw [(liftFn_spec I v hL (s ^ m)).2 w hw]
        exact (Kv I w).one_mem
    rw [map_pow] at hpow
    exact (pow_eq_one_iff_of_nonneg (hpos s).le (by omega)).1 hpow

theorem modQ_of_supp (hC : KComm) (hL : LiftU) (hJ : MatVInj) (hU : MatVU) (y : I.Gf) (hy : SuppAt I v y) :
    modQ (PI.AdIndexEq.Ksub I) y = chiV I v hC hL hJ ⟨_, hU I v y⟩ := by
  show modQ (PI.AdIndexEq.Ksub I) y = modQ (PI.AdIndexEq.Ksub I) (liftHom I v hL hJ ⟨_, hU I v y⟩)
  rw [liftHom_apply, ← eq_liftFn I v hL hJ ⟨_, hU I v y⟩ y rfl hy]

end Lift

theorem locInert_of (hC : KComm) (hL : LiftU) (hJ : MatVInj) (hU : MatVU) (hK : KLocGlob)
    (h : LocInertChi) : LocInert := by
  unfold LocInert
  intro I v hv y hy
  obtain ⟨h1, h2, h3⟩ := chiV_props I v hC hL hJ hU hK
  rw [modQ_of_supp I v hC hL hJ hU y hy]
  exact h I v hv _ h1 h2 h3 _

theorem locSplit_of (hC : KComm) (hL : LiftU) (hJ : MatVInj) (hU : MatVU) (hK : KLocGlob)
    (h : LocSplitChi) : LocSplit := by
  unfold LocSplit
  intro I v hv y hy
  obtain ⟨h1, h2, h3⟩ := chiV_props I v hC hL hJ hU hK
  rw [modQ_of_supp I v hC hL hJ hU y hy]
  exact h I v hv _ h1 h2 h3 _

theorem indexEq_of_loc (hC : KComm) (hL : LiftU) (hJ : MatVInj) (hU : MatVU) (hK : KLocGlob)
    (hR : ReduceLoc) (hS : LocSplitChi) (hI : LocInertChi) : PI.AdIndexEq.IndexEq := by
  unfold PI.AdIndexEq.IndexEq
  intro I x
  have hM := mod_q_hom I.Gf (PI.AdIndexEq.Ksub I) (hC I)
  have hloc : ∀ v (y : I.Gf), SuppAt I v y → modQ (PI.AdIndexEq.Ksub I) y = 1 := by
    intro v y hy
    by_cases hv : IsFieldAt I v
    · exact locInert_of hC hL hJ hU hK hI I v hv y hy
    · exact locSplit_of hC hL hJ hU hK hS I v hv y hy
  have hxm := hR I x
  have hx : modQ (PI.AdIndexEq.Ksub I) x = 1 := by
    induction hxm using Subgroup.closure_induction with
    | mem y hy =>
      rcases hy with ⟨v, hv⟩ | hy
      · exact hloc v y hv
      · exact hM.2.1 y hy
    | one => exact modQ_one _
    | mul a b _ _ ha hb => rw [hM.1, ha, hb, one_mul]
    | inv a _ ha =>
      have h1 := hM.1 a a⁻¹
      rw [mul_inv_cancel, modQ_one, ha, one_mul] at h1
      exact h1.symm
  exact hM.2.2 x hx

end PI.UnitaryGroupMassFormula.AdIndexEq

end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicIndexEquality.CompactLocalGlobal
section
noncomputable section

namespace PI.UnitaryGroupMassFormula.AdIndexEq

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct
open Formalism.MainNotions.S

theorem matV_coe (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F))
    (g : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) :
    ((matV I v g : GL (Fin I.n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E)) : Matrix _ _ _) =
      (g : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)).map (PI.FinKW.psiV I v).toRingHom := rfl

private theorem eq_of_forall_evalV_eq {F : Type} [Field F] [NumberField F] (a b : Af F)
    (h : ∀ v, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v a = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v b) : a = b :=
  Subtype.ext (funext fun v => h v)

private theorem tensorBasis_repr_psiV_eq_evalV_repr_comm (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F))
    (z : I.E ⊗[I.F] Af I.F) (i : Module.Free.ChooseBasisIndex I.F I.E) :
    (Algebra.TensorProduct.basis (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) (Module.Free.chooseBasis I.F I.E)).repr
        (PI.FinKW.psiV I v z) i =
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV I.F v
        ((Algebra.TensorProduct.basis (Af I.F) (Module.Free.chooseBasis I.F I.E)).repr
          (Algebra.TensorProduct.comm I.F I.E (Af I.F) z) i) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul e a =>
    simp [PI.FinKW.psiV, Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply,
      Finsupp.mapRange_apply, map_mul, AlgHom.commutes]
  | add x y hx hy => simp only [map_add (f := _), Finsupp.add_apply, hx, hy]

theorem mat_ext_of_psiV (I : AutInst) (M N : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F))
    (h : ∀ v, M.map (PI.FinKW.psiV I v).toRingHom = N.map (PI.FinKW.psiV I v).toRingHom) :
    M = N := by
  ext i j
  have hij : ∀ v, PI.FinKW.psiV I v (M i j) = PI.FinKW.psiV I v (N i j) := fun v => by
    have := congrFun (congrFun (h v) i) j
    simpa [Matrix.map_apply] using this
  apply (Algebra.TensorProduct.comm I.F I.E (Af I.F)).injective
  apply (Algebra.TensorProduct.basis (Af I.F) (Module.Free.chooseBasis I.F I.E)).repr.injective
  refine Finsupp.ext fun k => ?_
  apply eq_of_forall_evalV_eq
  intro v
  rw [← tensorBasis_repr_psiV_eq_evalV_repr_comm, ← tensorBasis_repr_psiV_eq_evalV_repr_comm, hij v]

theorem matrix_v_injective : MatVInj := by
  unfold MatVInj
  intro I y z h
  apply Subtype.ext
  apply Units.ext
  apply mat_ext_of_psiV I
  intro v
  have := congrArg Units.val (h v)
  simpa only [matV_coe] using this

theorem psiV_sigR (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (z : I.E ⊗[I.F] Af I.F) :
    PI.FinKW.psiV I v (Formalism.UG.sigR I.cm.sig (Af I.F) z) = sigV I v (PI.FinKW.psiV I v z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul e a => simp [PI.FinKW.psiV, Formalism.UG.sigR, sigV]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem psiV_inclE (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (e : I.E) :
    PI.FinKW.psiV I v (Formalism.UG.inclE (F := I.F) (Af I.F) e) = inclV I v e := by
  simp [PI.FinKW.psiV, Formalism.UG.inclE, inclV]

theorem map_cT {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (σ : A →+* A) (τ : B →+* B)
    (hf : ∀ a, f (σ a) = τ (f a)) {m p : Type} (M : Matrix m p A) :
    (Formalism.UG.cT σ M).map f = Formalism.UG.cT τ (M.map f) := by
  ext i j
  simp [Formalism.UG.cT, hf]

theorem mapJ (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) :
    (I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F))).map (PI.FinKW.psiV I v).toRingHom =
      I.J.map (inclV I v) := by
  ext i j
  simp only [Matrix.map_apply]
  exact psiV_inclE I v _

theorem map_unitary (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F))
    (M : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) :
    (Formalism.UG.cT (Formalism.UG.sigR I.cm.sig (Af I.F)) M * I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F)) * M).map
              (PI.FinKW.psiV I v).toRingHom =
      Formalism.UG.cT (sigV I v) (M.map (PI.FinKW.psiV I v).toRingHom) * I.J.map (inclV I v) *
        M.map (PI.FinKW.psiV I v).toRingHom := by
  rw [Matrix.map_mul, Matrix.map_mul,
    map_cT (PI.FinKW.psiV I v).toRingHom (Formalism.UG.sigR I.cm.sig (Af I.F)) (sigV I v)
      (fun a => psiV_sigR I v a), mapJ]

theorem mem_Uv_iff (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F))
    (g : GL (Fin I.n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E)) :
    g ∈ Uv I v ↔ Formalism.UG.cT (sigV I v) g.val * I.J.map (inclV I v) * g.val = I.J.map (inclV I v) := Iff.rfl

theorem mem_Gf_iff (I : AutInst) (g : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) :
    g ∈ Formalism.UG.UPts I.cm.sig I.J (Af I.F) ↔
      Formalism.UG.cT (Formalism.UG.sigR I.cm.sig (Af I.F)) g.val * I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F)) *
        g.val = I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F)) := Iff.rfl

theorem matrix_v_unitary : MatVU := by
  unfold MatVU
  intro I v y
  rw [mem_Uv_iff, matV_coe]
  have hy := (mem_Gf_iff I y).1 y.2
  rw [← map_unitary, hy]
  exact mapJ I v

theorem vecV_mulVec' (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F))
    (M : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) (x : Fin I.n → I.E ⊗[I.F] Af I.F) :
    PI.FinKW.vecV I v (M *ᵥ x) = M.map (PI.FinKW.psiV I v).toRingHom *ᵥ PI.FinKW.vecV I v x := by
  funext i
  set_option synthInstance.maxHeartbeats 100000 in
    simp [PI.FinKW.vecV, Matrix.mulVec, dotProduct, map_sum]

theorem stab_iff_loc (I : AutInst) (g : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) :
    g ∈ Formalism.UG.stabGL I.Lf ↔ ∀ v, matV I v g ∈ Kv I v := by
  have hL : ∀ x, x ∈ I.Lf ↔
      ∀ v, PI.FinKW.vecV I v x ∈ Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E)) :=
    fun x => ⟨PI.FinKW.LocTo.mem_local_lattice_iff I x, PI.FinKW.memLocFrom_of PI.FinKW.local_vector_injective I x⟩
  constructor
  · intro hst v y
    obtain ⟨x, hxv, hxw⟩ := PI.FinKW.local_vector_lift I v y
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
    have egx : (g : Matrix _ _ _) *ᵥ x ∈ I.Lf ↔
        ((matV I v g : GL (Fin I.n) _) : Matrix _ _ _) *ᵥ y ∈
          Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E)) := by
      rw [hL, matV_coe]
      constructor
      · intro H
        have := H v
        rwa [vecV_mulVec', hxv] at this
      · intro H w
        rw [vecV_mulVec']
        by_cases hw : w = v
        · subst hw
          rwa [hxv]
        · rw [hxw w hw, Matrix.mulVec_zero]
          exact zero_mem _
    exact ex.symm.trans ((hst x).trans egx)
  · intro hK x
    show x ∈ I.Lf ↔ (g : Matrix _ _ _) *ᵥ x ∈ I.Lf
    rw [hL x, hL ((g : Matrix _ _ _) *ᵥ x)]
    refine forall_congr' fun v => ?_
    rw [vecV_mulVec', ← matV_coe]
    exact hK v (PI.FinKW.vecV I v x)

theorem compact_local_global : KLocGlob := by
  unfold KLocGlob
  intro I y
  rw [PI.AdIndexEq.Ksub, Subgroup.mem_comap]
  exact stab_iff_loc I _

end PI.UnitaryGroupMassFormula.AdIndexEq

end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicIndexEquality.InertQRG
section
noncomputable section

namespace PI.UnitaryGroupMassFormula.AdIndexEq

open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.MainNotions.S

theorem sigV_tmul (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (x : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v)
    (e : I.E) : sigV I v (x ⊗ₜ e) = x ⊗ₜ star e := by
  change (Algebra.TensorProduct.map (AlgHom.id I.F _) I.cm.sig) (x ⊗ₜ e) = _
  exact Algebra.TensorProduct.map_tmul _ _ _ _

theorem sigV_invol (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F))
    (a : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E) : sigV I v (sigV I v a) = a := by
  induction a using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul x e => rw [sigV_tmul, sigV_tmul, star_star]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

theorem sigV_inclV (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (e : I.E) :
    sigV I v (inclV I v e) = inclV I v (star e) := by
  exact sigV_tmul I v 1 e

theorem herm_V (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) :
    Formalism.UG.cT (sigV I v) (I.J.map (inclV I v)) = I.J.map (inclV I v) := by
  funext i j
  have h : starRingEnd I.E (I.J j i) = I.J i j := congrFun (congrFun I.J_herm i) j
  show sigV I v (inclV I v (I.J j i)) = inclV I v (I.J i j)
  rw [sigV_inclV]
  exact congrArg (inclV I v) h

theorem q_reflection_generation : QReflGen := by
  intro I v hv g
  let _ : Field (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E) := hv.toField
  have hinj : Function.Injective (inclV I v) := (inclV I v).injective
  have hdet : (I.J.map (inclV I v)).det ≠ 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    intro h
    exact I.J_det (hinj (by rw [h, map_zero]))
  have h2 : (2 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E) ≠ 0 := by
    intro h
    have : inclV I v 2 = inclV I v 0 := by rw [map_ofNat, map_zero]; exact h
    exact two_ne_zero (hinj this)
  exact QRG.mem_S (sigV I v) (I.J.map (inclV I v)) (sigV_invol I v) (herm_V I v) hdet h2 g

theorem locInertChi_of_qReflPow (hP : QReflPow) : LocInertChi := by
  intro I v hv χ _ _ hK g
  have hq : {s : Uv I v | IsQRefl I v s} ⊆ (χ.ker : Set (Uv I v)) := by
    intro s hs
    obtain ⟨m, hm, hmK⟩ := hP I v hv s hs
    exact MonoidHom.mem_ker.mpr (hK s ⟨m, hm, hmK⟩)
  exact MonoidHom.mem_ker.mp ((Subgroup.closure_le _).mpr hq (q_reflection_generation I v hv g))

end PI.UnitaryGroupMassFormula.AdIndexEq

end
end

