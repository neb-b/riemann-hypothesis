module

public import Formalism.LocalToGlobal.HermitianForms.IsLocBasis

@[expose] public section

-- bundled from Formalism.LocalToGlobal.HermitianForms.DetShiftShW
section
namespace Formalism.L2.Forms

open Formalism.BasicNotions

variable {N : ℕ}

def shW (l : DomWeight N) (c : ℤ) : DomWeight N where
  w := fun i => l.w i - c
  anti := fun i j h => by
    have := l.anti h
    show l.w j - c ≤ l.w i - c
    omega

theorem shW_zero (l : DomWeight N) : shW l 0 = l := by
  cases l
  simp only [shW, sub_zero]

theorem detShift_shW (l : DomWeight N) (c : ℤ) (hN : 0 < N) : (shW l c).detShift = l.detShift - c := by
  simp [DomWeight.detShift, hN, shW]

theorem natW_shW (l : DomWeight N) (c : ℤ) : (shW l c).natW = l.natW := by
  funext i
  have hN : 0 < N := lt_of_le_of_lt (Nat.zero_le _) i.2
  simp only [DomWeight.natW, detShift_shW l c hN]
  congr 1
  simp only [shW]
  ring

theorem delSq_shW (R : Type) [CommRing R] (l : DomWeight N) (c : ℤ) : delSq R N (shW l c) = delSq R N l := by
  unfold delSq
  rw [natW_shW]

theorem CSpan_shW {ι : Type} [Fintype ι] (lam : ι → DomWeight N) (c : ι → ℤ) :
    CSpan (fun τ => shW (lam τ) (c τ)) = CSpan lam := by
  simp only [CSpan, delSq_shW]

end Formalism.L2.Forms
end

-- bundled from Formalism.LocalToGlobal.HermitianForms.PsiZeroNontrivialCharacter
section
noncomputable section

namespace Formalism.L2.Forms

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

section Shape

variable {k : Type} [Field k] {n : ℕ}

def blkOf (a t x : ℕ) : ℕ := if x < a then x else a + (x - a) / t

def entN (M : Matrix (Fin n) (Fin n) k) (x y : ℕ) : k := if h : x < n ∧ y < n then M ⟨x, h.1⟩ ⟨y, h.2⟩ else 0

def InJ (a t fc : ℕ) (zl : Bool) (M : Matrix (Fin n) (Fin n) k) : Prop :=
  (∀ x y : Fin n, blkOf a t y < blkOf a t x → M x y = 0) ∧ (∀ x : Fin n, (x : ℕ) < a → M x x = 1) ∧
  (∀ x y : Fin n, (y : ℕ) = fc → M x y = if x = y then 1 else 0) ∧
  (zl = true → ∀ x y : Fin n, (y : ℕ) + 1 = n →
    M x y = (if x = y then 1 else 0) ∧ M y x = (if x = y then 1 else 0))

def blkMat (a t i : ℕ) (M : Matrix (Fin n) (Fin n) k) : Matrix (Fin t) (Fin t) k :=
  fun s s' => entN M (a + i * t + s) (a + i * t + s')

def lamJ (ψ : AddChar k ℂ) (χ : ℕ → MulChar k ℂ) (a t nb skip : ℕ) (M : Matrix (Fin n) (Fin n) k) : ℂ :=
  ψ (∑ x : Fin n, ∑ y : Fin n, if (x : ℕ) + 1 = y ∧ (y : ℕ) < a ∧ (y : ℕ) ≠ skip then M x y else 0) *
    ∏ i ∈ Finset.range nb, χ i (blkMat a t i M).det

end Shape

section Red

variable (F : Type) [Field F] [NumberField F]

abbrev kv (v : HeightOneSpectrum (𝓞 F)) : Type := IsLocalRing.ResidueField (v.adicCompletionIntegers F)


open Classical in
def redM {n : ℕ} (v : HeightOneSpectrum (𝓞 F)) (X : Matrix (Fin n) (Fin n) (v.adicCompletion F)) :
    Matrix (Fin n) (Fin n) (kv F v) :=
  fun a b => if h : X a b ∈ v.adicCompletionIntegers F then
    IsLocalRing.residue (v.adicCompletionIntegers F) ⟨X a b, h⟩ else 0

end Red

section Loc

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

structure GLoc (σ : E →ₐ[F] E) (gp : Fin 2 → ℕ) where

  sp : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp i : 𝓞 F) ∈ v.asIdeal →
    E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F
  sp_sig : ∀ i v h x, sp i v h (sigR σ (v.adicCompletion F) x) = swapR _ (sp i v h x)
  sp_alg : ∀ i v h (a : v.adicCompletion F), sp i v h ((1 : E) ⊗ₜ[F] a) = (a, a)

  piG : Fin 2 → 𝓞 E
  piG_norm : ∀ i, (piG i : E) * σ (piG i : E) = (gp i : E)

  sp_pi : ∀ i v h, Valued.v (sp i v h (inclE (F := F) (v.adicCompletion F) (σ (piG i : E)))).1 < 1

  psi0 : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp i : 𝓞 F) ∈ v.asIdeal → AddChar (kv F v) ℂ
  psi_zero_nontrivial_character : ∀ i v h, psi0 i v h ≠ 1

  chiB : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp i : 𝓞 F) ∈ v.asIdeal → ℕ → MulChar (kv F v) ℂ

variable {F E}
variable {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
  {gp : Fin 2 → ℕ}

def GLoc.phi (G : GLoc F E σ gp) (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)) (h : (gp i : 𝓞 F) ∈ v.asIdeal) :
    E ⊗[F] v.adicCompletion F →+* v.adicCompletion F :=
  (RingHom.fst _ _).comp (G.sp i v h).toRingHom

def GLoc.mat (G : GLoc F E σ gp) (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)) (h : (gp i : 𝓞 F) ∈ v.asIdeal)
    (fr : GL (Fin n) (v.adicCompletion F)) (x : GL (Fin n) (E ⊗[F] v.adicCompletion F)) :
    Matrix (Fin n) (Fin n) (v.adicCompletion F) :=
  ((fr⁻¹ * bc (G.phi i v h) x * fr : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F))

structure GLev (S : StepLevel F E σ J T f bad) (G : GLoc F E σ gp) (a t nb skip fc : ℕ) (zl : Bool) where

  fr : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp i : 𝓞 F) ∈ v.asIdeal → GL (Fin n) (v.adicCompletion F)
  fr_lat : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)) (h : (gp i : 𝓞 F) ∈ v.asIdeal) (x : Fin n → v.adicCompletion F),
    (∃ y ∈ latS (F := F) (v.adicCompletion F) (intV E v) S.Lb, ∀ b, G.phi i v h (y b) = x b) ↔
      ∀ b, (((fr i v h)⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)).mulVec x b ∈
        v.adicCompletionIntegers F

  mem : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)) (h : (gp i : 𝓞 F) ∈ v.asIdeal), ∀ x ∈ levelVL σ J v S.Lb, x ∈ S.Uloc v ↔ InJ a t fc zl (redM F v (G.mat i v h (fr i v h) x))

  chi_eq : ∀ x : S.U, (S.chi x : ℂ) = ∏ i : Fin 2, ∏ᶠ (v : HeightOneSpectrum (𝓞 F)) (h : (gp i : 𝓞 F) ∈ v.asIdeal),
    (lamJ (G.psi0 i v h) (G.chiB i v h) a t nb skip
      (redM F v (G.mat i v h (fr i v h) (bc (prV (E := E) v) x.1))))⁻¹

  chi_unit : ∀ x : S.U, ‖(S.chi x : ℂ)‖ = 1

end Loc

end Formalism.L2.Forms
end
end

-- bundled from Formalism.LocalToGlobal.HermitianForms.TiedBrInj
section
noncomputable section

namespace Formalism.L2.Forms

open MvPolynomial

variable {ι : Type} [Fintype ι] {n : ℕ}

def detAll (ι : Type) [Fintype ι] (n : ℕ) : MvPolynomial (ι × Fin n × Fin n) ℂ :=
  ∏ τ, rename (fun ab : Fin n × Fin n => (τ, ab)) (Matrix.mvPolynomialX (Fin n) (Fin n) ℂ).det

theorem eval_detAll (x : ι × Fin n × Fin n → ℂ) :
    eval x (detAll ι n) = ∏ τ, (Matrix.of fun a b => x (τ, a, b)).det := by
  unfold detAll
  rw [map_prod]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [MvPolynomial.eval_rename, RingHom.map_det]
  congr 1
  ext a b
  simp [Matrix.mvPolynomialX]

theorem detAll_ne_zero : detAll ι n ≠ 0 := by
  intro h
  have e := congrArg (MvPolynomial.eval (fun p : ι × Fin n × Fin n => (1 : Matrix (Fin n) (Fin n) ℂ) p.2.1 p.2.2)) h
  rw [eval_detAll, map_zero] at e
  have e3 : ∀ τ : ι, (Matrix.of fun a b => (1 : Matrix (Fin n) (Fin n) ℂ) a b).det = 1 := fun τ => by
    have h1 : (Matrix.of fun a b => (1 : Matrix (Fin n) (Fin n) ℂ) a b) = 1 := by ext a b; rfl
    rw [h1, Matrix.det_one]
  have e4 : (∏ τ : ι, (Matrix.of fun a b => (1 : Matrix (Fin n) (Fin n) ℂ) a b).det) = 1 :=
    Finset.prod_eq_one fun τ _ => e3 τ
  exact one_ne_zero (e4.symm.trans e)

theorem eq_zero_of_eval_units (P : MvPolynomial (ι × Fin n × Fin n) ℂ)
    (h : ∀ x : ι × Fin n × Fin n → ℂ, (∀ τ, IsUnit (Matrix.of fun a b => x (τ, a, b)).det) → eval x P = 0) : P = 0 := by
  have h2 : P * detAll ι n = 0 := by
    apply MvPolynomial.funext
    intro x
    rw [map_mul, eval_detAll, map_zero]
    by_cases hx : ∀ τ, IsUnit (Matrix.of fun a b => x (τ, a, b)).det
    · rw [h x hx, zero_mul]
    · push_neg at hx
      obtain ⟨τ, hτ⟩ := hx
      rw [isUnit_iff_ne_zero, not_not] at hτ
      rw [Finset.prod_eq_zero (Finset.mem_univ τ) hτ, mul_zero]
  exact (mul_eq_zero.1 h2).resolve_right detAll_ne_zero

theorem fnOf_injective (G : ι → Matrix (Fin n) (Fin n) ℂ) (s : ι → ℤ) (M : ι → Matrix (Fin n) (Fin n) ℂ)
    (hM : ∀ τ, IsUnit (M τ).det) : Function.Injective (fnOf G s M) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro P hP
  apply eq_zero_of_eval_units P
  intro x hx
  let X : ι → Matrix (Fin n) (Fin n) ℂ := fun τ => Matrix.of fun a b => x (τ, a, b)
  have hy : ∀ τ, IsUnit ((M τ)⁻¹ * X τ).det := fun τ => by
    rw [Matrix.det_mul]
    exact (Matrix.isUnit_nonsing_inv_det _ (hM τ)).mul (hx τ)
  let y : Frames G := ⟨fun τ => (M τ)⁻¹ * X τ, hy⟩
  have hMy : ∀ τ, M τ * y.1 τ = X τ := fun τ => Matrix.mul_nonsing_inv_cancel_left _ _ (hM τ)
  have e := congrFun hP y
  simp only [fnOf, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply, hMy] at e
  have hprod : (∏ τ, (X τ).det ^ s τ) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun τ _ => zpow_ne_zero _ (hx τ).ne_zero
  have e2 := (mul_eq_zero.1 e).resolve_left hprod
  simpa [X] using e2

end Formalism.L2.Forms
end
end

-- bundled from Formalism.LocalToGlobal.HermitianForms.Transport
section
namespace Formalism.L2.Forms
open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
  {ι : Type} [Fintype ι]

theorem AdFun_transport (S : StepLevel F E σ J T f bad) (emb : ι → E →+* ℂ)
    (g) (hg : g ∈ AdFun S emb) (γ : GL (Fin n) E) (hγ : γ ∈ UJ (σ : E →+* E) J)
    (x x' : UPts σ J (FiniteAdeleRing (𝓞 F) F)) (κ : S.U)
    (h : bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * x'.1 = x.1 * κ.1)
    (y y' : Frames (gramC J emb)) (hy : IsTr (atInf emb γ) y' y) :
    g x y = ((S.chi κ)⁻¹ : ℂˣ) * g x' y' := by
  have h2 : x.1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * x'.1 * (κ⁻¹ : S.U).1 := by
    rw [h]; simp
  have := hg γ hγ x' x κ⁻¹ h2 y y' hy
  rw [this, map_inv]

end Formalism.L2.Forms
end

