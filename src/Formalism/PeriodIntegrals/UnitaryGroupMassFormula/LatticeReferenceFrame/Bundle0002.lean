module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeReferenceFrame.Bundle0001
public import Formalism.PeriodIntegrals.Bundle0020

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeReferenceFrame.GlobWIff
section
noncomputable section

open NumberField Formalism.MainNotions.S IsDedekindDomain
open scoped TensorProduct

namespace PI.ScRefExists.Sk

def Concl (I : Formalism.MainNotions.S.AutInst) (g r k : ℕ) (θ : 𝓞 I.E) (e f : Fin r → Fin I.n → I.E) (M : ℕ) : Prop :=
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

def Hyp (I : Formalism.MainNotions.S.AutInst) (g r k : ℕ) (θ : 𝓞 I.E) (e f : Fin r → Fin I.n → I.E) (M : ℕ) : Prop :=
  1 ≤ g ∧ SplitG I g ∧ IsTheta I g θ ∧ I.n = 2 * r + k + 1 ∧
    (∀ a b, hG I (e a) (e b) = 0) ∧ (∀ a b, hG I (f a) (f b) = 0) ∧
    (∀ a b, hG I (e a) (f b) = if a = b then 1 else 0) ∧
    Nat.Coprime M g ∧ (∀ a, M • e a ∈ I.L ∧ M • f a ∈ I.L)

def GWpp : Prop :=
  ∀ (I : Formalism.MainNotions.S.AutInst) (p m r k : ℕ) (θ : 𝓞 I.E) (e f : Fin r → Fin I.n → I.E) (M : ℕ),
    p.Prime → 1 ≤ m → Hyp I (p ^ m) r k θ e f M → Concl I (p ^ m) r k θ e f M

def GWcrt : Prop :=
  ∀ (I : Formalism.MainNotions.S.AutInst) (g₁ g₂ r k : ℕ) (θ : 𝓞 I.E) (e f : Fin r → Fin I.n → I.E) (M : ℕ),
    Nat.Coprime g₁ g₂ → Hyp I (g₁ * g₂) r k θ e f M →
    Concl I g₁ r k θ e f M → Concl I g₂ r k θ e f M → Concl I (g₁ * g₂) r k θ e f M

end PI.ScRefExists.Sk
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeReferenceFrame.HGNsmulRight
section
noncomputable section

open NumberField Formalism.MainNotions.S
open scoped TensorProduct

namespace PI.ScRefExists.GlueB

open PI.ScRefExists PI.ScRefExists.GlueA PI.ScRefExists.Sk

section Lemmas

variable (I : Formalism.MainNotions.S.AutInst) (g : ℕ)

theorem zmod_zero : ZMod' I g 0 := ⟨0, zero_mem _, by simp⟩

theorem zmod_of_GE {x : I.E} (h : GE I g x) : ZMod' I g (Formalism.UG.inclE (F := I.F) (Af I.F) x) := by
  obtain ⟨t, rfl⟩ := h
  exact ⟨Formalism.UG.inclE (F := I.F) (Af I.F) (t : I.E), inclE_mem' I t, by rw [map_mul, map_natCast]⟩

theorem zmod_add {x y : I.E ⊗[I.F] Af I.F} (h1 : ZMod' I g x) (h2 : ZMod' I g y) :
    ZMod' I g (x + y) := by
  obtain ⟨a, ha, rfl⟩ := h1
  obtain ⟨b, hb, rfl⟩ := h2
  exact ⟨a + b, add_mem ha hb, (mul_add _ _ _).symm⟩

theorem zmod_mul_int {x y : I.E ⊗[I.F] Af I.F} (h : ZMod' I g x) (hy : y ∈ IntAf I.F I.E) :
    ZMod' I g (x * y) := by
  obtain ⟨a, ha, rfl⟩ := h
  exact ⟨a * y, mul_mem ha hy, mul_assoc _ _ _⟩

theorem zmod_eps {ε : I.E ⊗[I.F] Af I.F} {θ : I.E}
    (hε : ZMod' I g (ε - Formalism.UG.inclE (F := I.F) (Af I.F) θ)) {x : I.E}
    (hx : x ∈ (algebraMap (𝓞 I.E) I.E).range) (h : GE I g (θ * x)) :
    ZMod' I g (ε * Formalism.UG.inclE (F := I.F) (Af I.F) x) := by
  obtain ⟨s, rfl⟩ := hx
  have h1 := zmod_mul_int I g hε (inclE_mem' I s)
  have h2 := zmod_add I g h1 (zmod_of_GE I g h)
  convert h2 using 1
  rw [map_mul]
  have e : algebraMap (𝓞 I.E) I.E s = (s : I.E) := rfl
  rw [e]
  ring

theorem zmod_sig {ε : I.E ⊗[I.F] Af I.F} {θ : I.E}
    (hε : ZMod' I g (ε - Formalism.UG.inclE (F := I.F) (Af I.F) θ)) :
    ZMod' I g (sigA I ε - Formalism.UG.inclE (F := I.F) (Af I.F) (star θ)) := by
  obtain ⟨t, ht, he⟩ := hε
  have hinc : ∀ a : I.E, sigA I (Formalism.UG.inclE (F := I.F) (Af I.F) a) =
      Formalism.UG.inclE (F := I.F) (Af I.F) (star a) := by
    intro a
    show (Algebra.TensorProduct.map I.cm.sig (AlgHom.id I.F (Af I.F))) (a ⊗ₜ[I.F] (1 : Af I.F)) =
      (star a) ⊗ₜ[I.F] (1 : Af I.F)
    rw [Algebra.TensorProduct.map_tmul]
    rfl
  have hcl : Subring.closure (Set.range (fun x : Formalism.UG.intOE I.E => (x : I.E) ⊗ₜ[I.F] (1 : Af I.F)) ∪
      Set.range (fun y : Formalism.UG.intAd I.F => (1 : I.E) ⊗ₜ[I.F] (y : Af I.F))) ≤
      (IntAf I.F I.E).comap (sigA I) := by
    rw [Subring.closure_le]
    rintro _ (⟨⟨s, hs⟩, rfl⟩ | ⟨⟨y, hy⟩, rfl⟩)
    · obtain ⟨s', rfl⟩ := hs
      show sigA I (Formalism.UG.inclE (F := I.F) (Af I.F) (algebraMap (𝓞 I.E) I.E s')) ∈ IntAf I.F I.E
      rw [hinc]
      have hi : IsIntegral ℤ (star (algebraMap (𝓞 I.E) I.E s')) :=
        IsIntegral.map (starRingEnd I.E).toIntAlgHom (NumberField.RingOfIntegers.isIntegral_coe s')
      exact inclE_mem' I ⟨_, hi⟩
    · show (Algebra.TensorProduct.map I.cm.sig (AlgHom.id I.F (Af I.F))) ((1 : I.E) ⊗ₜ[I.F] (y : Af I.F)) ∈
        IntAf I.F I.E
      rw [Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply]
      exact Subring.subset_closure (Or.inr ⟨⟨y, hy⟩, rfl⟩)
  refine ⟨sigA I t, hcl ht, ?_⟩
  rw [← hinc, ← map_sub, he, map_mul, map_natCast]

theorem hG_nsmul_left (m : ℕ) (x y : Fin I.n → I.E) :
    Formalism.UG.hform (starRingEnd I.E) I.J (m • x) y = (m : I.E) * Formalism.UG.hform (starRingEnd I.E) I.J x y := by
  simp only [Formalism.UG.hform, Pi.smul_apply, nsmul_eq_mul, map_mul, map_natCast, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hG_nsmul_right (m : ℕ) (x y : Fin I.n → I.E) :
    Formalism.UG.hform (starRingEnd I.E) I.J x (m • y) = (m : I.E) * Formalism.UG.hform (starRingEnd I.E) I.J x y := by
  simp only [Formalism.UG.hform, Pi.smul_apply, nsmul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem mem_mL {x : VA I} (hx : x ∈ I.Lf) : ((g : ℕ) : I.E ⊗[I.F] Af I.F) • x ∈ mL I g :=
  Submodule.subset_span ⟨x, hx, rfl⟩

theorem incl_osmul (c : 𝓞 I.E) (x : Fin I.n → I.E) :
    incl I (c • x) = (⟨Formalism.UG.inclE (F := I.F) (Af I.F) (c : I.E), inclE_mem' I c⟩ : IntAf I.F I.E) •
      incl I x := by
  funext i
  simp only [incl, Pi.smul_apply, Subring.smul_def, smul_eq_mul, Algebra.smul_def, map_mul]
  rfl

theorem mem_L_of (h3 : LocGlob) {x : Fin I.n → I.E} (hx : incl I x ∈ I.Lf) : x ∈ I.L := by
  refine (I.L_dual x).mpr fun y hy => ?_
  let H : VA I → I.E ⊗[I.F] Af I.F := fun v =>
    ∑ i, ∑ j, Formalism.UG.inclE (F := I.F) (Af I.F) (starRingEnd I.E (y i) * I.J i j) * v j
  have hinc : ∀ z : Fin I.n → I.E, H (incl I z) =
      Formalism.UG.inclE (F := I.F) (Af I.F) (Formalism.UG.hform (starRingEnd I.E) I.J y z) := by
    intro z
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [H, incl, Formalism.UG.hform, map_sum, map_mul]
  have key : ∀ v ∈ I.Lf, H v ∈ IntAf I.F I.E := by
    intro v hv
    change v ∈ Submodule.span _ _ at hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨z, rfl⟩ := hv
      change H (incl I (z : Fin I.n → I.E)) ∈ IntAf I.F I.E
      obtain ⟨s, hs⟩ := (I.L_dual z).mp z.2 y hy
      rw [hinc, ← hs]
      exact inclE_mem' I s
    | zero => simp [H]
    | add a b _ _ ha hb =>
      have e : H (a + b) = H a + H b := by
        simp only [H, Pi.add_apply, mul_add, Finset.sum_add_distrib]
      rw [e]
      exact add_mem ha hb
    | smul a v _ hv =>
      have e : H (a • v) = (a : I.E ⊗[I.F] Af I.F) * H v := by
        simp only [H, Pi.smul_apply, Subring.smul_def, smul_eq_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        ring
      rw [e]
      exact mul_mem a.2 hv
  have hm := key _ hx
  rw [hinc x] at hm
  obtain ⟨s, hs⟩ := h3 I _ hm
  exact ⟨s, hs⟩

theorem incl_nsmul' (m : ℕ) (x : Fin I.n → I.E) : incl I (m • x) = m • incl I x := by
  funext i
  simp only [incl, Pi.smul_apply, map_nsmul]

theorem ge_of_nat {x : I.E} (m : ℕ) (h : x = (g : I.E) * (m : I.E)) : GE I g x :=
  ⟨(m : 𝓞 I.E), by rw [h]; exact congrArg _ (map_natCast (algebraMap (𝓞 I.E) I.E) m).symm⟩

end Lemmas

end PI.ScRefExists.GlueB

end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeReferenceFrame.IdemLiftOfSteps
section
noncomputable section

open NumberField Formalism.MainNotions.S IsDedekindDomain
open scoped TensorProduct

namespace PI.ScRefExists.Id

def LocIdem : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (g : ℕ)
    (α β : v.adicCompletion F), 1 ≤ g → Valued.v ((g : ℕ) : v.adicCompletion F) < 1 →
    Valued.v α ≤ 1 → Valued.v β ≤ 1 →
    ∃ c₁ c₂ : v.adicCompletion F, Valued.v c₁ ≤ 1 ∧ Valued.v c₂ ≤ 1 ∧
      (1 + (g : v.adicCompletion F) * α) * (1 + g * c₁) ^ 2 - 2 * (1 + g * c₁) * (g * c₂) = 1 + g * c₁ ∧
      (g * c₂) ^ 2 - g * β * (1 + g * c₁) ^ 2 = -(g * c₂) ∧
      (g * c₂) ^ 2 - (1 + g * α) * (g * c₂) * (1 + g * c₁) + g * β * (1 + g * c₁) ^ 2 = 0

def AdIdem : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (g : ℕ) (α β : Af F), 1 ≤ g →
    α ∈ Formalism.UG.intAd F → β ∈ Formalism.UG.intAd F →
    ∃ C₁ C₂ : Af F, C₁ ∈ Formalism.UG.intAd F ∧ C₂ ∈ Formalism.UG.intAd F ∧
      (1 + (g : Af F) * α) * (1 + g * C₁) ^ 2 - 2 * (1 + g * C₁) * (g * C₂) = 1 + g * C₁ ∧
      (g * C₂) ^ 2 - g * β * (1 + g * C₁) ^ 2 = -(g * C₂) ∧
      (g * C₂) ^ 2 - (1 + g * α) * (g * C₂) * (1 + g * C₁) + g * β * (1 + g * C₁) ^ 2 = 0

def AdOfLoc : Prop := LocIdem → AdIdem

def FixInt : Prop :=
  ∀ (I : Formalism.MainNotions.S.AutInst) (s : 𝓞 I.E), star (s : I.E) = s →
    ∃ a : 𝓞 I.F, algebraMap I.F I.E (a : I.F) = s

def TenStep : Prop := AdIdem → FixInt → PI.ScRefExists.Sk.IdemLift

theorem idemLift_of_steps (h1 : LocIdem) (h2 : AdOfLoc) (h3 : FixInt) (h4 : TenStep) :
    PI.ScRefExists.Sk.IdemLift := h4 (h2 h1) h3

end PI.ScRefExists.Id
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeReferenceFrame.LocGlob
section
noncomputable section

open NumberField Formalism.MainNotions.S IsDedekindDomain
open scoped TensorProduct nonZeroDivisors

namespace PI.ScRefExists.LG

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem int_mem_intAd (r : 𝓞 F) : algebraMap F (Af F) (algebraMap (𝓞 F) F r) ∈ Formalism.UG.intAd F := by
  intro v
  show ((algebraMap (𝓞 F) F r : F) : v.adicCompletion F) ∈ v.adicCompletionIntegers F
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  exact v.valuation_le_one r

theorem int_of_mem_intAd (x : F) (h : algebraMap F (Af F) x ∈ Formalism.UG.intAd F) :
    x ∈ (algebraMap (𝓞 F) F).range := by
  refine HeightOneSpectrum.mem_integers_of_valuation_le_one F x fun v => ?_
  have hv : ((x : F) : v.adicCompletion F) ∈ v.adicCompletionIntegers F := h v
  rwa [HeightOneSpectrum.mem_adicCompletionIntegers,
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at hv

def lam (a : E) : E →ₗ[F] F := (Algebra.trace F E) ∘ₗ (LinearMap.mulLeft F a)

def Phi (a : E) : E ⊗[F] Af F →ₗ[F] Af F :=
  (TensorProduct.lid F (Af F)).toLinearMap ∘ₗ TensorProduct.map (lam a) LinearMap.id

omit [NumberField E] in
theorem Phi_tmul (a x : E) (c : Af F) :
    Phi a (x ⊗ₜ[F] c) = algebraMap F (Af F) (Algebra.trace F E (a * x)) * c := by
  simp [Phi, lam, Algebra.smul_def]

def Gens : Submonoid (E ⊗[F] Af F) where
  carrier := {x | ∃ o : 𝓞 E, ∃ c ∈ Formalism.UG.intAd F, x = (algebraMap (𝓞 E) E o) ⊗ₜ[F] c}
  one_mem' := ⟨1, 1, one_mem _, by simp [Algebra.TensorProduct.one_def]⟩
  mul_mem' := by
    rintro _ _ ⟨o, c, hc, rfl⟩ ⟨o', c', hc', rfl⟩
    exact ⟨o * o', c * c', mul_mem hc hc', by simp [Algebra.TensorProduct.tmul_mul_tmul]⟩

theorem Phi_mem (a : E) (ha : ∀ o : 𝓞 E, Algebra.trace F E (a * algebraMap (𝓞 E) E o) ∈
    (algebraMap (𝓞 F) F).range) {y : E ⊗[F] Af F} (hy : y ∈ IntAf F E) :
    Phi a y ∈ Formalism.UG.intAd F := by
  have hy' : y ∈ AddSubgroup.closure ((Submonoid.closure
      (Set.range (fun x : Formalism.UG.intOE E => (x : E) ⊗ₜ[F] (1 : Af F)) ∪
        Set.range (fun y : Formalism.UG.intAd F => (1 : E) ⊗ₜ[F] (y : Af F))) : Set _)) :=
    Subring.mem_closure_iff.mp hy
  have hle : Submonoid.closure
      (Set.range (fun x : Formalism.UG.intOE E => (x : E) ⊗ₜ[F] (1 : Af F)) ∪
        Set.range (fun y : Formalism.UG.intAd F => (1 : E) ⊗ₜ[F] (y : Af F))) ≤ (Gens : Submonoid _) := by
    rw [Submonoid.closure_le]
    rintro _ (⟨⟨x, o, rfl⟩, rfl⟩ | ⟨⟨c, hc⟩, rfl⟩)
    · exact ⟨o, 1, one_mem _, rfl⟩
    · exact ⟨1, c, hc, by simp⟩
  have hy2 := AddSubgroup.closure_mono hle hy'
  clear hy hy' hle
  induction hy2 using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨o, c, hc, rfl⟩ := hx
    rw [Phi_tmul]
    obtain ⟨r, hr⟩ := ha o
    rw [← hr]
    exact mul_mem (int_mem_intAd r) hc
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg]; exact neg_mem hx

theorem locGlob_gen (t : E) (ht : Formalism.UG.inclE (F := F) (Af F) t ∈ IntAf F E) :
    ∃ s : 𝓞 E, algebraMap (𝓞 E) E s = t := by
  have h1 : (1 : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 := one_ne_zero
  have hd : FractionalIdeal.dual (𝓞 F) F (1 : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 :=
    FractionalIdeal.dual_ne_zero (𝓞 F) F h1
  have hmem : t ∈ FractionalIdeal.dual (𝓞 F) F
      (FractionalIdeal.dual (𝓞 F) F (1 : FractionalIdeal (𝓞 E)⁰ E)) := by
    rw [FractionalIdeal.mem_dual hd]
    intro a ha
    rw [FractionalIdeal.mem_dual h1] at ha
    have ha' : ∀ o : 𝓞 E, Algebra.trace F E (a * algebraMap (𝓞 E) E o) ∈
        (algebraMap (𝓞 F) F).range := by
      intro o
      have := ha (algebraMap (𝓞 E) E o) ((FractionalIdeal.mem_one_iff (𝓞 E)⁰).mpr ⟨o, rfl⟩)
      simpa [Algebra.traceForm_apply] using this
    have hP := Phi_mem a ha' ht
    have hx : Phi a (Formalism.UG.inclE (F := F) (Af F) t) =
        algebraMap F (Af F) (Algebra.trace F E (a * t)) := by
      simp [Formalism.UG.inclE, Phi_tmul]
    rw [hx] at hP
    have := int_of_mem_intAd _ hP
    simpa [Algebra.traceForm_apply, mul_comm] using this
  rw [FractionalIdeal.dual_dual] at hmem
  exact (FractionalIdeal.mem_one_iff (𝓞 E)⁰).mp hmem

end Gen

theorem local_global_principle_alt : PI.ScRefExists.Sk.LocGlob := by
  intro I t ht
  exact locGlob_gen t ht

end PI.ScRefExists.LG
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeReferenceFrame.ThetaA
section
noncomputable section

open NumberField Formalism.MainNotions.S IsDedekindDomain
open scoped TensorProduct

namespace PI.ScRefExists.TH

variable (I : Formalism.MainNotions.S.AutInst)

def sg : 𝓞 I.E →+* 𝓞 I.E := NumberField.RingOfIntegers.mapRingHom (starRingEnd I.E)

theorem sg_coe (x : 𝓞 I.E) : ((sg I x : 𝓞 I.E) : I.E) = star (x : I.E) := rfl

theorem sg_sg (x : 𝓞 I.E) : sg I (sg I x) = x := by
  apply NumberField.RingOfIntegers.ext
  rw [sg_coe, sg_coe, star_star]

theorem coe_alg (c : 𝓞 I.F) :
    ((algebraMap (𝓞 I.F) (𝓞 I.E) c : 𝓞 I.E) : I.E) = algebraMap I.F I.E (c : I.F) := by
  show algebraMap (𝓞 I.E) I.E (algebraMap (𝓞 I.F) (𝓞 I.E) c) = _
  rw [← IsScalarTower.algebraMap_apply (𝓞 I.F) (𝓞 I.E) I.E,
    IsScalarTower.algebraMap_apply (𝓞 I.F) I.F I.E]

theorem sg_alg (c : 𝓞 I.F) : sg I (algebraMap (𝓞 I.F) (𝓞 I.E) c) = algebraMap (𝓞 I.F) (𝓞 I.E) c := by
  apply NumberField.RingOfIntegers.ext
  rw [sg_coe]
  have h : ((algebraMap (𝓞 I.F) (𝓞 I.E) c : 𝓞 I.E) : I.E) = algebraMap I.F I.E (c : I.F) := by
    show algebraMap (𝓞 I.E) I.E (algebraMap (𝓞 I.F) (𝓞 I.E) c) = _
    rw [← IsScalarTower.algebraMap_apply (𝓞 I.F) (𝓞 I.E) I.E,
      IsScalarTower.algebraMap_apply (𝓞 I.F) I.F I.E]
  rw [h]
  exact (I.cm.fixed _).2 ⟨_, rfl⟩

theorem fixed_int (y : 𝓞 I.E) (hy : star (y : I.E) = y) :
    ∃ c : 𝓞 I.F, algebraMap (𝓞 I.F) (𝓞 I.E) c = y := by
  obtain ⟨a, ha⟩ := (I.cm.fixed (y : I.E)).1 hy
  have hi : IsIntegral ℤ (algebraMap I.F I.E a) := by
    rw [ha]; exact y.isIntegral_coe
  have hi' : IsIntegral ℤ a := (isIntegral_algebraMap_iff ).mp hi
  let c : 𝓞 I.F := ⟨a, (mem_integralClosure_iff _ _).mpr hi'⟩
  refine ⟨c, ?_⟩
  apply NumberField.RingOfIntegers.ext
  rw [coe_alg]
  exact ha

def cj (P : HeightOneSpectrum (𝓞 I.E)) : HeightOneSpectrum (𝓞 I.E) where
  asIdeal := P.asIdeal.comap (sg I)
  isPrime := Ideal.IsPrime.comap _
  ne_bot := by
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot P.ne_bot
    intro h
    have : sg I x ∈ P.asIdeal.comap (sg I) := by
      rw [Ideal.mem_comap, sg_sg]; exact hx
    rw [h, Ideal.mem_bot] at this
    apply hx0
    rw [← sg_sg I x, this, map_zero]

theorem mem_cj (P : HeightOneSpectrum (𝓞 I.E)) (x : 𝓞 I.E) : x ∈ (cj I P).asIdeal ↔ sg I x ∈ P.asIdeal :=
  Ideal.mem_comap

theorem cj_cj (P : HeightOneSpectrum (𝓞 I.E)) : cj I (cj I P) = P := by
  ext x
  rw [mem_cj, mem_cj, sg_sg]

theorem comap_cj (P : HeightOneSpectrum (𝓞 I.E)) :
    (cj I P).asIdeal.comap (algebraMap (𝓞 I.F) (𝓞 I.E)) = P.asIdeal.comap (algebraMap (𝓞 I.F) (𝓞 I.E)) := by
  ext c
  rw [Ideal.mem_comap, Ideal.mem_comap, mem_cj, sg_alg]

theorem cj_ne (g : ℕ) (hg : 1 ≤ g) (hS : PI.ScRefExists.Sk.SplitG I g) (P : HeightOneSpectrum (𝓞 I.E))
    (hP : (g : 𝓞 I.E) ∈ P.asIdeal) : cj I P ≠ P := by
  intro hfix
  have hg0 : (g : 𝓞 I.F) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hgv : (g : 𝓞 I.F) ∈ P.asIdeal.comap (algebraMap (𝓞 I.F) (𝓞 I.E)) := by
    rw [Ideal.mem_comap, map_natCast]; exact hP
  let v : HeightOneSpectrum (𝓞 I.F) :=
    { asIdeal := P.asIdeal.comap (algebraMap (𝓞 I.F) (𝓞 I.E))
      isPrime := Ideal.IsPrime.comap _
      ne_bot := fun h => hg0 (by rw [h, Ideal.mem_bot] at hgv; exact hgv) }
  have hcard := hS v hgv
  let P' : {w : HeightOneSpectrum (𝓞 I.E) //
      w.asIdeal.comap (algebraMap (𝓞 I.F) (𝓞 I.E)) = v.asIdeal} := ⟨P, rfl⟩
  obtain ⟨x, hx, hxu⟩ := (Nat.card_eq_two_iff' P').mp hcard
  let cx : {w : HeightOneSpectrum (𝓞 I.E) //
      w.asIdeal.comap (algebraMap (𝓞 I.F) (𝓞 I.E)) = v.asIdeal} := ⟨cj I x.1, by rw [comap_cj]; exact x.2⟩
  have hcx : cx ≠ P' := by
    intro h
    apply hx
    apply Subtype.ext
    have h1 : cj I x.1 = P := congrArg Subtype.val h
    rw [← cj_cj I x.1, h1, hfix]
  have hcxx : cj I x.1 = x.1 := congrArg Subtype.val (hxu cx hcx)
  have hne : P.asIdeal ≠ x.1.asIdeal := by
    intro h
    apply hx
    apply Subtype.ext
    exact (HeightOneSpectrum.ext h).symm
  have hnle : ¬ P.asIdeal ≤ x.1.asIdeal := fun h =>
    hne (P.isMaximal.eq_of_le x.1.isPrime.ne_top h)
  obtain ⟨θ, hθP, hθx⟩ := SetLike.not_le_iff_exists.mp hnle
  have hfixy : star ((θ * sg I θ : 𝓞 I.E) : I.E) = ((θ * sg I θ : 𝓞 I.E) : I.E) := by
    show star ((θ : I.E) * (sg I θ : I.E)) = (θ : I.E) * (sg I θ : I.E)
    rw [sg_coe, star_mul, star_star, mul_comm]
  obtain ⟨c, hc⟩ := fixed_int I _ hfixy
  have hyP : θ * sg I θ ∈ P.asIdeal := Ideal.mul_mem_right _ _ hθP
  have hcv : c ∈ x.1.asIdeal.comap (algebraMap (𝓞 I.F) (𝓞 I.E)) := by
    rw [x.2]
    show c ∈ P.asIdeal.comap (algebraMap (𝓞 I.F) (𝓞 I.E))
    rw [Ideal.mem_comap, hc]; exact hyP
  rw [Ideal.mem_comap, hc] at hcv
  rcases x.1.isPrime.mem_or_mem hcv with h | h
  · exact hθx h
  · apply hθx
    have : θ ∈ (cj I x.1).asIdeal := by rw [mem_cj]; exact h
    rwa [hcxx] at this

end PI.ScRefExists.TH
end
end

