module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IrreducibleDistinctUnitary
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0210
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NonemptyDirectSumEquivOfFinrankLe
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0040
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.MinorOrderedEntries

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemDualWeylOfUnitriangularFixed
section
open MvPolynomial Formalism.BasicNotions Formalism.GradedWeylDivisibility GlobalTheory.Branching GlobalTheory.GLDuality
open Formalism.REAL (fockF)
open scoped DirectSum TensorProduct Kronecker Matrix

namespace GlobalTheory.GLDuality

theorem matRep_diagGL_monomial_colChar {n n' : ℕ} (t : Fin n → ℂˣ) (d : Fin n' × Fin n →₀ ℕ) (c : ℂ) :
    matRep n n' (diagGL ℂ n t, 1) (monomial d c) =
      monomial d ((d.prod fun x e => (t x.2 : ℂ) ^ e) * c) := by
  have h : sub (((1 : GL (Fin n') ℂ) : Matrix (Fin n') (Fin n') ℂ) ⊗ₖ
      ((diagGL ℂ n t : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ))ᵀ =
      aeval (fun x : Fin n' × Fin n => C (t x.2 : ℂ) * (X x : MvPolynomial (Fin n' × Fin n) ℂ)) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨a, s⟩
    simp [sub, diagGL, Fintype.sum_prod_type, Matrix.one_apply, Matrix.diagonal_apply, apply_ite C]
  rw [matRep_apply, h, aeval_monomial, monomial_eq]
  simp only [mul_pow, Finsupp.prod, Finset.prod_mul_distrib, map_mul, map_prod, map_pow, algebraMap_eq]
  ring

theorem coeff_matRep_diagGL_colChar {n n' : ℕ} (t : Fin n → ℂˣ) (v : MvPolynomial (Fin n' × Fin n) ℂ)
    (d : Fin n' × Fin n →₀ ℕ) :
    AddMonoidAlgebra.coeff (matRep n n' (diagGL ℂ n t, 1) v) d = (d.prod fun x e => (t x.2 : ℂ) ^ e) * AddMonoidAlgebra.coeff v d := by
  classical
  induction v using MvPolynomial.induction_on' with
  | monomial u a =>
    rw [matRep_diagGL_monomial_colChar, coeff_monomial, coeff_monomial]
    split_ifs with h
    · rw [h]
    · simp
  | add p q hp hq => rw [map_add (f := _), MvPolynomial.coeff_add, MvPolynomial.coeff_add, hp, hq, mul_add]

theorem colAdd_eq_matRep_of_transvection {n n' : ℕ} (l j : Fin n) (c : ℂ) (g : GL (Fin n) ℂ)
    (hg : (g : Matrix (Fin n) (Fin n) ℂ) = Matrix.transvection l j c)
    (v : MvPolynomial (Fin n' × Fin n) ℂ) : colAdd ℂ l j c v = matRep n n' (g, 1) v := by
  have h : sub (((1 : GL (Fin n') ℂ) : Matrix (Fin n') (Fin n') ℂ) ⊗ₖ
      (g : Matrix (Fin n) (Fin n) ℂ))ᵀ = colAdd ℂ (r := n') l j c := by
    apply MvPolynomial.algHom_ext
    rintro ⟨a, s⟩
    rw [hg]
    by_cases hs : s = j
    · subst hs
      simp [sub, colAdd, Fintype.sum_prod_type, Matrix.one_apply, Matrix.transvection, Matrix.single_apply,
        apply_ite C, add_mul, Finset.sum_add_distrib]
    · have hs' : ¬ j = s := fun e => hs e.symm
      simp [sub, colAdd, Fintype.sum_prod_type, Matrix.one_apply, Matrix.transvection, Matrix.single_apply,
        apply_ite C, hs, hs']
  rw [matRep_apply, h]

theorem mem_dualWeyl_of_unitriangular_fixed :
    ∀ (n n' : ℕ) (ν : Fin n → ℕ) (v : MvPolynomial (Fin n' × Fin n) ℂ), (∀ g : GL (Fin n) ℂ, (g : Matrix (Fin n) (Fin n) ℂ).BlockTriangular id → (∀ a, (g : Matrix (Fin n) (Fin n) ℂ) a a = 1) → matRep n n' (g, 1) v = v) → (∀ t : Fin n → ℂˣ, matRep n n' (diagGL ℂ n t, 1) v = (∏ a, (t a : ℂ) ^ ν a) • v) → v ∈ dualWeyl ℂ n' n ν := by
  intro n n' ν v hU hT
  rw [Formalism.GradedWeylDivisibility.dualWeylPoint ℂ n' n ν v]
  refine ⟨fun d hd => ?_, fun l j hlj c => ?_⟩
  · funext i
    let t : Fin n → ℂˣ := fun s => if s = i then Units.mk0 2 two_ne_zero else 1
    have h1 := congrArg (AddMonoidAlgebra.coeff · d) (hT t)
    rw [coeff_matRep_diagGL_colChar, coeff_smul, smul_eq_mul] at h1
    have h2 := mul_right_cancel₀ hd h1
    have h3 : (∏ a, (t a : ℂ) ^ ν a) = 2 ^ ν i := by
      rw [Finset.prod_eq_single i]
      · simp [t]
      · intro b _ hb
        simp [t, hb]
      · simp
    have h4 : (d.prod fun x e => (t x.2 : ℂ) ^ e) = 2 ^ (Finsupp.weight (colW n' n) d i) := by
      rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply, ← Finset.prod_pow_eq_pow_sum, Finsupp.prod]
      refine Finset.prod_congr rfl fun x _ => ?_
      by_cases hx : x.2 = i
      · simp [t, colW, hx]
      · simp [t, colW, hx]
    rw [h3, h4] at h2
    have h5 : (2 : ℕ) ^ (Finsupp.weight (colW n' n) d i) = 2 ^ ν i := by exact_mod_cast h2
    exact Nat.pow_right_injective le_rfl h5
  · have hne : l ≠ j := hlj.ne
    let g : GL (Fin n) ℂ := Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.transvection l j c)
      (by rw [Matrix.det_transvection_of_ne l j hne]; exact one_ne_zero)
    have hg : (g : Matrix (Fin n) (Fin n) ℂ) = Matrix.transvection l j c := rfl
    rw [colAdd_eq_matRep_of_transvection l j c g hg]
    refine hU g ?_ ?_
    · intro a b hab
      have hab' : b < a := hab
      have h1 : ¬ (l = a ∧ j = b) := by
        rintro ⟨rfl, rfl⟩
        exact lt_asymm hlj hab'
      rw [hg]
      simp [Matrix.transvection, h1, Matrix.one_apply_ne hab'.ne']
    · intro a
      have h1 : ¬ (l = a ∧ j = a) := by
        rintro ⟨rfl, rfl⟩
        exact hne rfl
      rw [hg]
      simp [Matrix.transvection, h1]

end GlobalTheory.GLDuality
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NonemptyInvFunEquiv
section
noncomputable section

open MvPolynomial Matrix GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries Formalism.BasicNotions GlobalTheory.Branching
open scoped TensorProduct

namespace GlobalTheory.OneFunctional

section General

variable {G H K V W X : Type} [Monoid G] [Monoid H] [Monoid K] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup X] [Module ℂ X]

def Iso (ρ : Representation ℂ G V) (σ : Representation ℂ G W) : Prop :=
  ∃ e : V ≃ₗ[ℂ] W, ∀ g x, e (ρ g x) = σ g (e x)

theorem Iso.refl (ρ : Representation ℂ G V) : Iso ρ ρ := ⟨LinearEquiv.refl _ _, fun _ _ => rfl⟩

theorem Iso.symm {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (h : Iso ρ σ) : Iso σ ρ := by
  obtain ⟨e, he⟩ := h
  exact ⟨e.symm, fun g x => e.injective (by rw [he]; simp)⟩

theorem Iso.trans {ρ : Representation ℂ G V} {σ : Representation ℂ G W} {τ : Representation ℂ G X} (h : Iso ρ σ)
    (h' : Iso σ τ) : Iso ρ τ := by
  obtain ⟨e, he⟩ := h
  obtain ⟨e', he'⟩ := h'
  exact ⟨e.trans e', fun g x => by simp [he, he']⟩

theorem Iso.comp {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (h : Iso ρ σ) (f : H →* G) :
    Iso (ρ.comp f : Representation ℂ H V) (σ.comp f) := by
  obtain ⟨e, he⟩ := h
  exact ⟨e, fun g x => he (f g) x⟩

theorem Iso.twist {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (h : Iso ρ σ) (χ : G →* ℂˣ) :
    Iso (twist χ ρ) (twist χ σ) := by
  obtain ⟨e, he⟩ := h
  refine ⟨e, fun g x => ?_⟩
  change e ((χ g : ℂ) • ρ g x) = (χ g : ℂ) • σ g (e x)
  rw [map_smul, he]

theorem Iso.tprod {V' W' : Type} [AddCommGroup V'] [Module ℂ V'] [AddCommGroup W'] [Module ℂ W']
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W} {ρ' : Representation ℂ G V'} {σ' : Representation ℂ G W'}
    (h : Iso ρ σ) (h' : Iso ρ' σ') : Iso (ρ.tprod ρ') (σ.tprod σ') := by
  obtain ⟨e, he⟩ := h
  obtain ⟨e', he'⟩ := h'
  refine ⟨TensorProduct.congr e e', fun g x => ?_⟩
  induction x with
  | tmul a b => simp [he, he']
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

theorem Iso.tprod_comm (ρ : Representation ℂ G V) (σ : Representation ℂ G W) : Iso (ρ.tprod σ) (σ.tprod ρ) := by
  refine ⟨TensorProduct.comm ℂ V W, fun g x => ?_⟩
  induction x with
  | tmul a b => simp
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

theorem Iso.dual {G : Type} [Group G] {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (h : Iso ρ σ) :
    Iso ρ.dual σ.dual := by
  obtain ⟨e, he⟩ := h.symm
  refine ⟨e.dualMap, fun g x => ?_⟩
  ext w
  simp [Module.Dual.transpose_apply, he]

theorem Iso.of_equiv {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (e : ρ.Equiv σ) : Iso ρ σ :=
  ⟨e.toLinearEquiv, fun g x => e.toIntertwiningMap.isIntertwining _ _ g x⟩

theorem mem_invFun {ρ : Representation ℂ G V} {l : Module.Dual ℂ V} : l ∈ invFun ρ ↔ ∀ g x, l (ρ g x) = l x := Iff.rfl

theorem Iso.nonempty_invFun_equiv {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (h : Iso ρ σ) :
    Nonempty (invFun ρ ≃ₗ[ℂ] invFun σ) := by
  obtain ⟨e, he⟩ := h.symm
  refine ⟨e.dualMap.ofSubmodules _ _ (le_antisymm ?_ fun l hl => ⟨e.symm.dualMap l, fun g x => ?_, ?_⟩)⟩
  · rintro _ ⟨l, hl, rfl⟩ g x
    change l (e (σ g x)) = l (e x)
    rw [he, hl]
  · obtain ⟨x, rfl⟩ := e.surjective x
    change l (e.symm _) = l (e.symm _)
    rw [← he, e.symm_apply_apply, e.symm_apply_apply, hl]
  · ext x
    simp

theorem Iso.finrank_invFun {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (h : Iso ρ σ) :
    Module.finrank ℂ (invFun ρ) = Module.finrank ℂ (invFun σ) := by
  obtain ⟨e⟩ := h.nonempty_invFun_equiv
  exact e.finrank_eq

theorem Iso.invFun_eq_bot {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (h : Iso ρ σ) (h0 : invFun σ = ⊥) :
    invFun ρ = ⊥ := by
  obtain ⟨e⟩ := h.nonempty_invFun_equiv
  rw [← Submodule.subsingleton_iff_eq_bot] at h0 ⊢
  exact e.toEquiv.subsingleton

def Contracts {F : Type} [AddCommGroup F] [Module ℂ F] (φ : Representation ℂ (H × G) F) (σ : Representation ℂ H V)
    (σ' : Representation ℂ G W) : Prop :=
  ∃ π : F ⊗[ℂ] V →ₗ[ℂ] W, Function.Surjective π ∧
    (∀ h g f v, π (φ (h, g) f ⊗ₜ σ h v) = σ' g (π (f ⊗ₜ v))) ∧
    ∀ l : Module.Dual ℂ (F ⊗[ℂ] V), (∀ h f v, l (φ (h, 1) f ⊗ₜ σ h v) = l (f ⊗ₜ v)) → ∀ x, π x = 0 → l x = 0

theorem Contracts.congr {F F' V' W' : Type} [AddCommGroup F] [Module ℂ F] [AddCommGroup F'] [Module ℂ F']
    [AddCommGroup V'] [Module ℂ V'] [AddCommGroup W'] [Module ℂ W']
    {φ : Representation ℂ (H × G) F} {σ : Representation ℂ H V} {τ : Representation ℂ G W}
    {φ' : Representation ℂ (H × G) F'} {σ' : Representation ℂ H V'} {τ' : Representation ℂ G W'}
    (h : Contracts φ σ τ) (h1 : Iso φ φ') (h2 : Iso σ σ') (h3 : Iso τ τ') : Contracts φ' σ' τ' := by
  obtain ⟨π, hs, he, hk⟩ := h
  obtain ⟨e1, he1⟩ := h1
  obtain ⟨e2, he2⟩ := h2
  obtain ⟨e3, he3⟩ := h3
  refine ⟨e3.toLinearMap ∘ₗ π ∘ₗ (TensorProduct.congr e1 e2).symm.toLinearMap,
    e3.surjective.comp (hs.comp (TensorProduct.congr e1 e2).symm.surjective), fun h g f v => ?_, fun l hl x hx => ?_⟩
  · obtain ⟨f, rfl⟩ := e1.surjective f
    obtain ⟨v, rfl⟩ := e2.surjective v
    simp [← he1, ← he2, he, he3]
  · obtain ⟨x, rfl⟩ := (TensorProduct.congr e1 e2).surjective x
    refine hk (l ∘ₗ (TensorProduct.congr e1 e2).toLinearMap) (fun h f v => ?_) x ?_
    · simp [he1, he2, hl]
    · change e3 (π ((TensorProduct.congr e1 e2).symm ((TensorProduct.congr e1 e2) x))) = 0 at hx
      simpa only [LinearEquiv.symm_apply_apply, LinearEquiv.map_eq_zero_iff] using hx

end General

section Outer

variable {ι G H : Type} [Monoid G] [Monoid H] {V W : ι → Type} [∀ τ, AddCommGroup (V τ)] [∀ τ, Module ℂ (V τ)]
  [∀ τ, AddCommGroup (W τ)] [∀ τ, Module ℂ (W τ)]

def outer (ρ : ∀ τ, Representation ℂ G (V τ)) : Representation ℂ (ι → G) (⨂[ℂ] τ, V τ) :=
  piTprod fun τ => (ρ τ).comp (Pi.evalMonoidHom (fun _ : ι => G) τ)

def outer₂ (ρ : ∀ τ, Representation ℂ (H × G) (V τ)) : Representation ℂ ((ι → H) × (ι → G)) (⨂[ℂ] τ, V τ) :=
  piTprod fun τ => (ρ τ).comp ((Pi.evalMonoidHom (fun _ : ι => H) τ).prodMap (Pi.evalMonoidHom (fun _ : ι => G) τ))

theorem piTprod_apply (ρ : ∀ τ, Representation ℂ G (V τ)) (g : G) :
    piTprod ρ g = PiTensorProduct.map fun τ => ρ τ g := rfl

theorem outer_apply (ρ : ∀ τ, Representation ℂ G (V τ)) (g : ι → G) :
    outer ρ g = PiTensorProduct.map fun τ => ρ τ (g τ) := rfl

theorem outer₂_apply (ρ : ∀ τ, Representation ℂ (H × G) (V τ)) (h : ι → H) (g : ι → G) :
    outer₂ ρ (h, g) = PiTensorProduct.map fun τ => ρ τ (h τ, g τ) := rfl

theorem Iso.outer {ρ : ∀ τ, Representation ℂ G (V τ)} {σ : ∀ τ, Representation ℂ G (W τ)} (h : ∀ τ, Iso (ρ τ) (σ τ)) :
    Iso (outer ρ) (outer σ) := by
  choose e he using h
  refine ⟨PiTensorProduct.congr e, fun g x => ?_⟩
  induction x using PiTensorProduct.induction_on with
  | smul_tprod c v => simp [outer_apply, he]
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

end Outer

abbrev U (n : ℕ) : Type := Matrix.unitaryGroup (Fin n) ℂ

def conjU (n : ℕ) : U n →* U n where
  toFun g := ⟨(star g.1)ᵀ, by
    rw [Matrix.mem_unitaryGroup_iff]
    have h : star g.1 * g.1 = 1 := Matrix.mem_unitaryGroup_iff'.1 g.2
    have e : star (star g.1)ᵀ = (g.1)ᵀ := by ext i j; simp
    rw [e, ← Matrix.transpose_mul, mul_eq_one_comm.1 h, Matrix.transpose_one]⟩
  map_one' := Subtype.ext (by simp)
  map_mul' g h := Subtype.ext (by simp [star_mul, Matrix.transpose_mul])

@[simp] theorem conjU_coe (n : ℕ) (g : U n) : (conjU n g).1 = (star g.1)ᵀ := rfl

abbrev irr (n : ℕ) (lam : DomWeight n) : Representation ℂ (U n) (nablaSq ℂ n lam) := smallRep (unitaryIncl n) lam

def fockOne (a b : ℕ) (α β : ℤ) : Representation ℂ (U a × U b) (MvPolynomial (Fin b × Fin a) ℂ) :=
  twist ((detU a ^ α).comp (MonoidHom.fst _ _) * (detU b ^ β).comp (MonoidHom.snd _ _))
    (GlobalTheory.GLDuality.polyRep ((unitaryIncl a).comp (conjU a)) (unitaryIncl b))

def StepW {a b : ℕ} (α β : ℤ) (lam : DomWeight a) (lam' : DomWeight b) : Prop :=
  ∀ i : Fin b, lam'.w i = if h : i.1 < a then lam.w ⟨i.1, h⟩ + α + β else β

end GlobalTheory.OneFunctional
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.OuterTensorIntertwiningEqZeroOfLeft
section
open MvPolynomial Formalism.BasicNotions Formalism.GradedWeylDivisibility GlobalTheory.Branching GlobalTheory.GLDuality
open Formalism.REAL (fockF)
open scoped DirectSum TensorProduct Kronecker Matrix

namespace GlobalTheory

theorem tensor_eq_zero_of_forall_contract_right {V W : Type} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (z : V ⊗[ℂ] W)
    (h : ∀ l : Module.Dual ℂ W, TensorProduct.rid ℂ V (LinearMap.lTensor V l z) = 0) : z = 0 := by
  classical
  let b := Module.Free.chooseBasis ℂ W
  apply (TensorProduct.equivFinsuppOfBasisRight (M := V) b).injective
  ext i
  simp [TensorProduct.equivFinsuppOfBasisRight_apply, h]

theorem outerTensor_intertwining_eq_zero_of_left :
    ∀ (G H V W V' W' : Type) [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [AddCommGroup V'] [Module ℂ V'] [AddCommGroup W'] [Module ℂ W'] (ρ : Representation ℂ G V) (σ : Representation ℂ H W) (ρ' : Representation ℂ G V') (σ' : Representation ℂ H W'), (∀ ψ : ρ.IntertwiningMap ρ', ψ = 0) → ∀ φ : (Representation.tprod (ρ.comp (MonoidHom.fst G H)) (σ.comp (MonoidHom.snd G H)) : Representation ℂ (G × H) (V ⊗[ℂ] W)).IntertwiningMap (Representation.tprod (ρ'.comp (MonoidHom.fst G H)) (σ'.comp (MonoidHom.snd G H)) : Representation ℂ (G × H) (V' ⊗[ℂ] W')), φ = 0 := by
  intro G H V W V' W' _ _ _ _ _ _ _ _ _ _ ρ σ ρ' σ' h φ

  have hpure : ∀ (v : V) (w : W), φ (v ⊗ₜ[ℂ] w) = 0 := by
    intro v w
    apply tensor_eq_zero_of_forall_contract_right
    intro l
    let f : V →ₗ[ℂ] V' :=
      (TensorProduct.rid ℂ V').toLinearMap ∘ₗ LinearMap.lTensor V' l ∘ₗ φ.toLinearMap ∘ₗ
        (TensorProduct.mk ℂ V W).flip w
    have hf : ∀ (g : G) (x : V), f (ρ g x) = ρ' g (f x) := by
      intro g x
      have key : ∀ y : V' ⊗[ℂ] W', TensorProduct.rid ℂ V'
          (LinearMap.lTensor V' l (TensorProduct.map (ρ' g) (σ' 1) y)) =
          ρ' g (TensorProduct.rid ℂ V' (LinearMap.lTensor V' l y)) := by
        intro y
        induction y using TensorProduct.induction_on with
        | zero => simp
        | tmul a c => simp
        | add a c ha hc => simp only [map_add (f := _), ha, hc]
      have e1 : ρ g x ⊗ₜ[ℂ] w = (Representation.tprod (ρ.comp (MonoidHom.fst G H))
          (σ.comp (MonoidHom.snd G H))) (g, 1) (x ⊗ₜ[ℂ] w) := by
        simp [Representation.tprod_apply]
      have e2 := Representation.IntertwiningMap.isIntertwining _ _ φ (g, 1) (x ⊗ₜ[ℂ] w)
      simp only [f, LinearMap.comp_apply, LinearMap.flip_apply, TensorProduct.mk_apply,
        Representation.IntertwiningMap.toLinearMap_apply, LinearEquiv.coe_coe]
      rw [e1, e2, Representation.tprod_apply]
      exact key _
    have h0 := h (f.intertwiningMap_of_isIntertwiningMap ρ ρ' hf)
    have hv := congrArg (fun ψ : ρ.IntertwiningMap ρ' => ψ v) h0
    simpa [f] using hv
  apply Representation.IntertwiningMap.ext
  apply TensorProduct.ext'
  intro v w
  simp [hpure]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairingEquivariantAndNeZero
section
open MvPolynomial Formalism.BasicNotions Formalism.GradedWeylDivisibility GlobalTheory.Branching GlobalTheory.GLDuality
open Formalism.REAL (fockF)
open scoped DirectSum TensorProduct Kronecker Matrix

noncomputable section

namespace GlobalTheory.GLDuality

def pairLmul {n n' k : ℕ} (x : Matrix (Fin n') (Fin n) ℂ) :
    MvPolynomial (Fin n' × Fin k) ℂ →ₐ[ℂ] MvPolynomial (Fin n × Fin k) ℂ :=
  aeval (fun v : Fin n' × Fin k => ∑ t : Fin n, C (x v.1 t) * (X (t, v.2) : MvPolynomial (Fin n × Fin k) ℂ))

theorem pairLmul_rowAct {n n' k : ℕ} (x : Matrix (Fin n') (Fin n) ℂ) (h : Matrix (Fin n') (Fin n') ℂ)
    (f : MvPolynomial (Fin n' × Fin k) ℂ) : pairLmul x (rowAct ℂ h f) = pairLmul (h * x) f := by
  have : (pairLmul x).comp (rowAct ℂ (n := k) h) = pairLmul (h * x) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨a, s⟩
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [pairLmul, rowAct, AlgHom.comp_apply, aeval_X, map_sum, map_mul, aeval_C, algebraMap_eq,
      Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  rw [← this]; rfl

theorem rowAct_pairLmul {n n' k : ℕ} (x : Matrix (Fin n') (Fin n) ℂ) (g : Matrix (Fin n) (Fin n) ℂ)
    (f : MvPolynomial (Fin n' × Fin k) ℂ) : rowAct ℂ g (pairLmul x f) = pairLmul (x * g) f := by
  have : (rowAct ℂ (n := k) g).comp (pairLmul x) = pairLmul (x * g) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨a, s⟩
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [pairLmul, rowAct, AlgHom.comp_apply, aeval_X, map_sum, map_mul, aeval_C, algebraMap_eq,
      Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  rw [← this]; rfl

theorem pair_map_conj_rowAct {n k : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) (p : MvPolynomial (Fin n × Fin k) ℂ) :
    map (starRingEnd ℂ) (rowAct ℂ g p) = rowAct ℂ (gᵀ)ᴴ (map (starRingEnd ℂ) p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [rowAct]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p v hp =>
    simp only [map_mul, hp, map_X]
    congr 1
    set_option synthInstance.maxHeartbeats 100000 in
      simp [rowAct, map_sum]

theorem pair_map_conj_hw {n k : ℕ} (hn : k ≤ n) (ν : Fin k → ℕ) :
    map (starRingEnd ℂ) (hw ℂ hn ν) = hw ℂ hn ν := by
  simp only [hw, map_prod, map_pow, lpMinor]
  refine Finset.prod_congr rfl fun s _ => ?_
  congr 1
  rw [RingHom.map_det]
  congr 1
  ext p q : 1
  simp

theorem pairLmul_hw {n n' k : ℕ} (hn : k ≤ n) (hn' : k ≤ n') (ν : Fin k → ℕ) :
    pairLmul (Matrix.of fun (a : Fin n') (t : Fin n) => if a.val = t.val then (1 : ℂ) else 0) (hw ℂ hn' ν) =
      hw ℂ hn ν := by
  simp only [hw, map_prod, map_pow, lpMinor]
  refine Finset.prod_congr rfl fun s _ => ?_
  congr 1
  rw [AlgHom.map_det]
  congr 1
  ext p q : 1
  simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, pairLmul, aeval_X]
  rw [Finset.sum_eq_single (Fin.castLE (by have := s.2; omega) p)]
  · simp
  · intro b _ hb
    rw [if_neg]
    · simp
    · intro e
      exact hb (Fin.ext (by simpa using e.symm))
  · simp

theorem pairing_equivariant_and_ne_zero : ∀ (n n' k : ℕ) (T : MvPolynomial (Fin n × Fin k) ℂ →ₗ[ℂ] MvPolynomial (Fin n' × Fin k) ℂ →ₗ[ℂ] MvPolynomial (Fin n' × Fin n) ℂ), (∀ (φ : MvPolynomial (Fin n × Fin k) ℂ) (f : MvPolynomial (Fin n' × Fin k) ℂ) (x : Matrix (Fin n') (Fin n) ℂ), eval (fun v => x v.1 v.2) (T φ f) = fockF φ (map (starRingEnd ℂ) (aeval (fun v : Fin n' × Fin k => ∑ t : Fin n, C (x v.1 t) * (X (t, v.2) : MvPolynomial (Fin n × Fin k) ℂ)) f))) → (∀ (g : GL (Fin n) ℂ) (h : GL (Fin n') ℂ) (φ : MvPolynomial (Fin n × Fin k) ℂ) (f : MvPolynomial (Fin n' × Fin k) ℂ), T (rowAct ℂ (g : Matrix (Fin n) (Fin n) ℂ)ᵀ φ) (rowAct ℂ (h : Matrix (Fin n') (Fin n') ℂ)ᵀ f) = matRep n n' (g, h) (T φ f)) ∧ ∀ (hn : k ≤ n) (hn' : k ≤ n') (ν : Fin k → ℕ), T (hw ℂ hn ν) (hw ℂ hn' ν) ≠ 0 := by
  intro n n' k T hT
  have hT' : ∀ φ f (x : Matrix (Fin n') (Fin n) ℂ),
      eval (fun v => x v.1 v.2) (T φ f) = fockF φ (map (starRingEnd ℂ) (pairLmul x f)) := hT
  refine ⟨fun g h φ f => ?_, fun hn hn' ν h0 => ?_⟩
  · apply MvPolynomial.funext
    intro p
    have hp : p = fun v => (Matrix.of fun a t => p (a, t)) v.1 v.2 := rfl
    rw [hp, eval_matRep, hT', hT', fockRowAdj, pairLmul_rowAct, ← pair_map_conj_rowAct, rowAct_pairLmul]
  · have h1 := hT' (hw ℂ hn ν) (hw ℂ hn' ν)
      (Matrix.of fun (a : Fin n') (t : Fin n) => if a.val = t.val then (1 : ℂ) else 0)
    rw [h0, map_zero, pairLmul_hw hn hn', pair_map_conj_hw] at h1
    have h2 := (fockPos _ _ (hwNe ℂ n k hn ν)).1
    rw [← h1] at h2
    simp at h2

end GlobalTheory.GLDuality
end
end

