module

public import Mathlib
public import Formalism.PeriodIntegrals.Bundle0020

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeReferenceFrame.Development
section
noncomputable section

open NumberField Formalism.MainNotions.S IsDedekindDomain
open scoped TensorProduct

namespace PI.ScRefExists.Sk

def GE (I : Formalism.MainNotions.S.AutInst) (g : ℕ) (x : I.E) : Prop := ∃ t : 𝓞 I.E, x = (g : I.E) * (t : I.E)

def hG (I : Formalism.MainNotions.S.AutInst) (x y : Fin I.n → I.E) : I.E := Formalism.UG.hform (starRingEnd I.E) I.J x y

def SplitG (I : Formalism.MainNotions.S.AutInst) (g : ℕ) : Prop :=
  ∀ v : HeightOneSpectrum (𝓞 I.F), (g : 𝓞 I.F) ∈ v.asIdeal →
    Nat.card {w : HeightOneSpectrum (𝓞 I.E) //
      w.asIdeal.comap (algebraMap (𝓞 I.F) (𝓞 I.E)) = v.asIdeal} = 2

def IsTheta (I : Formalism.MainNotions.S.AutInst) (g : ℕ) (θ : 𝓞 I.E) : Prop :=
  GE I g ((θ : I.E) * θ - θ) ∧ GE I g ((θ : I.E) * star (θ : I.E)) ∧
    GE I g (1 - (θ : I.E) - star (θ : I.E))

def ThetaEx : Prop :=
  ∀ (I : Formalism.MainNotions.S.AutInst) (g : ℕ), 1 ≤ g → SplitG I g → ∃ θ : 𝓞 I.E, IsTheta I g θ

def IdemLift : Prop :=
  ∀ (I : Formalism.MainNotions.S.AutInst) (g : ℕ) (θ : 𝓞 I.E), 1 ≤ g → SplitG I g → IsTheta I g θ →
    ∃ ε : I.E ⊗[I.F] Af I.F, ε ∈ IntAf I.F I.E ∧ ε * ε = ε ∧ ε * sigA I ε = 0 ∧
      ZMod' I g (ε - Formalism.UG.inclE (F := I.F) (Af I.F) (θ : I.E))

def LocGlob : Prop :=
  ∀ (I : Formalism.MainNotions.S.AutInst) (t : I.E), Formalism.UG.inclE (F := I.F) (Af I.F) t ∈ IntAf I.F I.E →
    ∃ s : 𝓞 I.E, (s : I.E) = t

def gL (I : Formalism.MainNotions.S.AutInst) (g : ℕ) : Submodule (𝓞 I.E) (Fin I.n → I.E) :=
  Submodule.span (𝓞 I.E) {y | ∃ x ∈ I.L, y = (g : I.E) • x}

def GlobW : Prop :=
  ∀ (I : Formalism.MainNotions.S.AutInst) (g r k : ℕ) (θ : 𝓞 I.E) (e f : Fin r → Fin I.n → I.E) (M : ℕ),
    1 ≤ g → SplitG I g → IsTheta I g θ → I.n = 2 * r + k + 1 →
    (∀ a b, hG I (e a) (e b) = 0) → (∀ a b, hG I (f a) (f b) = 0) →
    (∀ a b, hG I (e a) (f b) = if a = b then 1 else 0) →
    Nat.Coprime M g → (∀ a, M • e a ∈ I.L ∧ M • f a ∈ I.L) →
    ∃ (z : Fin I.n → I.E) (b bd : Fin k → Fin I.n → I.E),
      z ∈ I.L ∧ (∀ i, b i ∈ I.L ∧ bd i ∈ I.L) ∧
      (∀ a, hG I (e a) z = 0 ∧ hG I (f a) z = 0) ∧
      (∀ a i, hG I (e a) (b i) = 0 ∧ hG I (f a) (b i) = 0 ∧
        hG I (e a) (bd i) = 0 ∧ hG I (f a) (bd i) = 0) ∧
      GE I g (hG I z z + 1) ∧
      (∀ i, GE I g ((θ : I.E) * hG I z (b i)) ∧ GE I g (star (θ : I.E) * hG I z (bd i))) ∧
      (∀ i j, GE I g ((θ : I.E) * (hG I (bd i) (b j) - if i = j then 1 else 0))) ∧
      ∀ y ∈ I.L, y ∈ Submodule.span (𝓞 I.E)
        (Set.range (fun a => M • e a) ∪ Set.range (fun a => M • f a) ∪ {z} ∪
          Set.range (fun i => (θ : I.E) • b i) ∪ Set.range (fun i => star (θ : I.E) • bd i)) ⊔ gL I g

def Glue : Prop := ThetaEx → IdemLift → LocGlob → GlobW → PI.ScRefExists.Target

theorem target_of_steps (h0 : Glue) (h1 : ThetaEx) (h2 : IdemLift) (h3 : LocGlob) (h4 : GlobW) :
    PI.ScRefExists.Target := h0 h1 h2 h3 h4

end PI.ScRefExists.Sk
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeReferenceFrame.HANegRight
section
noncomputable section

open NumberField Formalism.MainNotions.S
open scoped TensorProduct

namespace PI.ScRefExists.GlueA

variable (I : Formalism.MainNotions.S.AutInst)

theorem inclE_tmul (a : I.E) : Formalism.UG.inclE (F := I.F) (Af I.F) a = a ⊗ₜ[I.F] (1 : Af I.F) := rfl

theorem star_int (t : 𝓞 I.E) : star (t : I.E) ∈ (algebraMap (𝓞 I.E) I.E).range := by
  have h : IsIntegral ℤ (star (t : I.E)) :=
    (NumberField.RingOfIntegers.isIntegral_coe t).map (starRingEnd I.E).toIntAlgHom
  exact ⟨⟨star (t : I.E), h⟩, rfl⟩

theorem inclE_mem {a : I.E} (ha : a ∈ (algebraMap (𝓞 I.E) I.E).range) :
    Formalism.UG.inclE (F := I.F) (Af I.F) a ∈ IntAf I.F I.E := by
  rw [inclE_tmul]
  exact Subring.subset_closure (Set.mem_union_left _ ⟨⟨a, ha⟩, rfl⟩)

theorem inclE_mem' (t : 𝓞 I.E) :
    Formalism.UG.inclE (F := I.F) (Af I.F) (t : I.E) ∈ IntAf I.F I.E := inclE_mem I ⟨t, rfl⟩

theorem sigA_inclE (a : I.E) :
    sigA I (Formalism.UG.inclE (F := I.F) (Af I.F) a) = Formalism.UG.inclE (F := I.F) (Af I.F) (star a) := by
  rw [inclE_tmul, inclE_tmul]
  first
    | exact Algebra.TensorProduct.map_tmul _ _ _ _
    | rfl

theorem sigA_sigA (x : (I.E ⊗[I.F] Af I.F)) : sigA I (sigA I x) = x := by
  have e : ∀ (c : I.E) (d : Af I.F), sigA I (c ⊗ₜ[I.F] d) = star c ⊗ₜ[I.F] d := fun c d => by
    first
      | exact Algebra.TensorProduct.map_tmul _ _ _ _
      | rfl
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul a b => rw [e, e, star_star]
  | add y z hy hz => rw [map_add (f := _), map_add (f := _), hy, hz]

theorem sigA_mem {x : (I.E ⊗[I.F] Af I.F)} (hx : x ∈ IntAf I.F I.E) : sigA I x ∈ IntAf I.F I.E := by
  have e1 : ∀ r : Af I.F, sigA I ((1 : I.E) ⊗ₜ[I.F] r) = (1 : I.E) ⊗ₜ[I.F] r := fun r => by
    first
      | simp only [sigA, Formalism.UG.sigR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
          Algebra.TensorProduct.map_tmul, map_one, AlgHom.coe_id, id_eq]
      | (show Algebra.TensorProduct.map I.cm.sig (AlgHom.id I.F (Af I.F)) ((1 : I.E) ⊗ₜ[I.F] r) = _
         rw [Algebra.TensorProduct.map_tmul, map_one]
         rfl)
      | simp [sigA, Formalism.UG.sigR]
  have h : IntAf I.F I.E ≤ (IntAf I.F I.E).comap (sigA I) := by
    show Subring.closure _ ≤ _
    rw [Subring.closure_le]
    rintro y (⟨⟨e, he⟩, rfl⟩ | ⟨⟨r, hr⟩, rfl⟩)
    · show sigA I (e ⊗ₜ[I.F] (1 : Af I.F)) ∈ IntAf I.F I.E
      rw [← inclE_tmul, sigA_inclE]
      obtain ⟨t, rfl⟩ := he
      exact inclE_mem I (star_int I t)
    · show sigA I ((1 : I.E) ⊗ₜ[I.F] (r : Af I.F)) ∈ IntAf I.F I.E
      rw [e1]
      exact Subring.subset_closure (Set.mem_union_right _ ⟨⟨r, hr⟩, rfl⟩)
  exact h hx

theorem natCast_eq (m : ℕ) : (m : (I.E ⊗[I.F] Af I.F)) = Formalism.UG.inclE (F := I.F) (Af I.F) (m : I.E) := by
  rw [map_natCast]

theorem hA_smul_left (c : (I.E ⊗[I.F] Af I.F)) (x y : VA I) : hA I (c • x) y = sigA I c * hA I x y := by
  simp only [hA, Formalism.UG.hform, sigA, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul, map_mul]
  ring

theorem hA_smul_right (c : (I.E ⊗[I.F] Af I.F)) (x y : VA I) : hA I x (c • y) = c * hA I x y := by
  simp only [hA, Formalism.UG.hform, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem incl_add (x y : Fin I.n → I.E) : incl I (x + y) = incl I x + incl I y := by
  funext i
  simp only [incl, Pi.add_apply, map_add (f := _)]

theorem incl_sub (x y : Fin I.n → I.E) : incl I (x - y) = incl I x - incl I y := by
  funext i
  simp only [incl, Pi.sub_apply, map_sub]

theorem incl_zero : incl I 0 = 0 := by
  funext i
  simp only [incl, Pi.zero_apply, map_zero]

theorem incl_smul (c : I.E) (x : Fin I.n → I.E) :
    incl I (c • x) = Formalism.UG.inclE (F := I.F) (Af I.F) c • incl I x := by
  funext i
  simp only [incl, Pi.smul_apply, smul_eq_mul, map_mul]

theorem incl_nsmul (m : ℕ) (x : Fin I.n → I.E) : incl I (m • x) = (m : (I.E ⊗[I.F] Af I.F)) • incl I x := by
  funext i
  simp only [incl, Pi.smul_apply, nsmul_eq_mul, smul_eq_mul, map_mul, map_natCast]

theorem hA_incl (x y : Fin I.n → I.E) :
    hA I (incl I x) (incl I y) =
      Formalism.UG.inclE (F := I.F) (Af I.F) (Formalism.UG.hform (starRingEnd I.E) I.J x y) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hA, Formalism.UG.hform, incl, Matrix.map_apply, map_sum, map_mul, starRingEnd_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have h := sigA_inclE I (x i)
  simp only [sigA] at h
  rw [h]

theorem incl_mem_Lf {x : Fin I.n → I.E} (hx : x ∈ I.L) : incl I x ∈ I.Lf := Submodule.subset_span ⟨⟨x, hx⟩, rfl⟩

theorem hG_int {x y : Fin I.n → I.E} (hx : x ∈ I.L) (hy : y ∈ I.L) :
    Formalism.UG.hform (starRingEnd I.E) I.J x y ∈ (algebraMap (𝓞 I.E) I.E).range := (I.L_dual y).mp hy x hx

theorem smul_mem_Lf {c : (I.E ⊗[I.F] Af I.F)} (hc : c ∈ IntAf I.F I.E) {x : VA I} (hx : x ∈ I.Lf) : c • x ∈ I.Lf := Submodule.smul_mem _ (⟨c, hc⟩ : IntAf I.F I.E) hx

end PI.ScRefExists.GlueA

end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeReferenceFrame.HypsNonvacuous
section
noncomputable section

open NumberField Formalism.MainNotions.S
open scoped TensorProduct

namespace PI.ScRefExists.UnitaryGroupMassFormula

variable (I : Formalism.MainNotions.S.AutInst)

theorem hA_zero_left (y : VA I) : hA I 0 y = 0 := by
  simp [hA, Formalism.UG.hform]

theorem zmod_one_of_mem {c : I.E ⊗[I.F] Af I.F} (h : c ∈ IntAf I.F I.E) : ZMod' I 1 c := by
  unfold ZMod'
  exact ⟨c, h, by simp⟩

theorem mL_one : mL I 1 = I.Lf := by
  unfold mL
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro y ⟨x, hx, rfl⟩
    simpa using hx
  · intro x hx
    exact Submodule.subset_span ⟨x, hx, by simp⟩

theorem ite_mem_int {p : Prop} [Decidable p] (x : I.E ⊗[I.F] Af I.F) (hx : x ∈ IntAf I.F I.E) :
    (if p then x else 0) ∈ IntAf I.F I.E := by
  split_ifs
  · exact hx
  · exact zero_mem _

def frameOne (r k : ℕ) (e f : Fin r → Fin I.n → I.E)
    (he : ∀ a, InAt I 1 1 (incl I (e a)) ∧ InAt I 1 1 (incl I (f a))) : RefData I 1 r k e f where
  e0 := fun _ => 0
  f0 := fun _ => 0
  z0 := 0
  bw := fun _ => 0
  bwd := fun _ => 0
  ew := 0
  vectorsInLattice := ⟨fun _ => ⟨zero_mem _, zero_mem _⟩, zero_mem _, fun _ => ⟨zero_mem _, zero_mem _⟩⟩
  basisApprox := by
    intro a
    constructor
    · obtain ⟨c, hc, hm⟩ := (he a).1
      exact ⟨c, hc, by rw [zero_sub, smul_neg]; exact neg_mem hm⟩
    · obtain ⟨c, hc, hm⟩ := (he a).2
      exact ⟨c, hc, by rw [zero_sub, smul_neg]; exact neg_mem hm⟩
  gramIntegral := by
    intro a b
    refine ⟨zmod_one_of_mem I ?_, zmod_one_of_mem I ?_, zmod_one_of_mem I ?_⟩
    · rw [hA_zero_left]; exact zero_mem _
    · rw [hA_zero_left]; exact zero_mem _
    · rw [hA_zero_left, zero_sub]; exact neg_mem (ite_mem_int I 1 (one_mem _))
  formsAtZero := by
    refine ⟨zmod_one_of_mem I ?_, fun a => ⟨zmod_one_of_mem I ?_, zmod_one_of_mem I ?_⟩⟩
    · rw [hA_zero_left, zero_add]; exact one_mem _
    · rw [hA_zero_left]; exact zero_mem _
    · rw [hA_zero_left]; exact zero_mem _
  weightVectorsIntegral := by
    intro i
    refine ⟨zmod_one_of_mem I ?_, zmod_one_of_mem I ?_, fun a => ⟨zmod_one_of_mem I ?_,
      zmod_one_of_mem I ?_, zmod_one_of_mem I ?_, zmod_one_of_mem I ?_⟩⟩ <;>
      (rw [hA_zero_left]; exact zero_mem _)
  ew_idem := by simp
  ew_orth := by simp
  ew_int := zero_mem _
  ew_full := by
    intro y hy
    rw [map_zero, sub_zero, sub_zero, one_smul, mL_one]
    exact hy
  bw_w := fun _ => by simp
  bwd_w := fun _ => by simp
  bw_dual := by
    intro i j
    apply zmod_one_of_mem
    rw [hA_zero_left, zero_sub]
    exact neg_mem (ite_mem_int I 0 (zero_mem _))
  latticeSpan := by
    intro y hy
    apply Submodule.mem_sup_right
    rw [mL_one]
    exact hy

theorem refData_one (r k : ℕ) (e f : Fin r → Fin I.n → I.E)
    (he : ∀ a, InAt I 1 1 (incl I (e a)) ∧ InAt I 1 1 (incl I (f a))) :
    Nonempty (RefData I 1 r k e f) := ⟨frameOne I r k e f he⟩

def TargetTwo : Prop :=
  ∀ (I : Formalism.MainNotions.S.AutInst) (g r k : ℕ) (e f : Fin r → Fin I.n → I.E), 2 ≤ g →
    (∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 I.F), (g : 𝓞 I.F) ∈ v.asIdeal →
      Nat.card {w : IsDedekindDomain.HeightOneSpectrum (𝓞 I.E) //
        w.asIdeal.comap (algebraMap (𝓞 I.F) (𝓞 I.E)) = v.asIdeal} = 2) →
    I.n = 2 * r + k + 1 →
    (∀ a b, Formalism.UG.hform (starRingEnd I.E) I.J (e a) (e b) = 0) →
    (∀ a b, Formalism.UG.hform (starRingEnd I.E) I.J (f a) (f b) = 0) →
    (∀ a b, Formalism.UG.hform (starRingEnd I.E) I.J (e a) (f b) = if a = b then 1 else 0) →
    (∀ a, InAt I g 1 (incl I (e a)) ∧ InAt I g 1 (incl I (f a))) →
    Nonempty (RefData I g r k e f)

theorem target_of_two (h : TargetTwo) : Target := by
  unfold TargetTwo at h
  unfold Target
  intro J g r k e f hg hs hn he hf hef hin
  rcases Nat.lt_or_ge g 2 with hlt | hge
  · obtain rfl : g = 1 := by omega
    exact refData_one J r k e f hin
  · exact h J g r k e f hge hs hn he hf hef hin

end PI.ScRefExists.UnitaryGroupMassFormula

end
end

