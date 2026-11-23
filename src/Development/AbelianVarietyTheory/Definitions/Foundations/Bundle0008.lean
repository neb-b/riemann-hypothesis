module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0003
public import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0006
public import ReciprocityTheory.GaloisValuations.Global
public import Formalism.GL3MeanSquares.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.Foundations.EeProd
section
noncomputable section

open scoped MatrixGroups

namespace GlobalTheory.Glue

open GlobalTheory.KZ

section Global

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

def CgA (A : ValuationSubring Ω) (l n : ℕ) (x y : Ω) : Prop := ∃ z ∈ A, x - y = (l : Ω) ^ n * z

def theta (s : ℚ) (φ : HahnSeries ℚ Ω) : HahnSeries ℚ Ω where
  coeff r := algebraMap ℚ Ω (s * r) * φ.coeff r
  isPWO_support' := φ.isPWO_support.mono (fun r hr h => hr (by simp [h]))

def Prim (A : ValuationSubring Ω) (φ : HahnSeries ℚ Ω) : Prop :=
  (∀ r, φ.coeff r ∈ A) ∧ ∃ r, φ.coeff r ≠ 0 ∧ (φ.coeff r)⁻¹ ∈ A

def IsDl (X : Tower Ω ε) (A : ValuationSubring Ω) (l n : ℕ) (s : ℚ) (f : X.K) (φ : HahnSeries ℚ Ω) : Prop :=
  (∀ r, φ.coeff r ∈ A) ∧ ∃ (a b : X.K) (κ : Ω), κ ≠ 0 ∧ f * b = algebraMap Ω X.K κ * a ∧ Prim A (X.exp a) ∧ Prim A (X.exp b) ∧
    ∀ r, CgA A l n ((φ * X.exp a * X.exp b).coeff r) ((theta s (X.exp a) * X.exp b - X.exp a * theta s (X.exp b)).coeff r)

def Inv (X : Tower Ω ε) (H : Subgroup SL(2, ℤ)) (f : X.K) : Prop := ∀ γ ∈ H, X.sl (ofSL γ) f = f

def IsThB (X : Tower Ω ε) (A : ValuationSubring Ω) (N l n : ℕ) [Fact l.Prime] (b : X.Fn l) (φ : HahnSeries ℚ Ω) : Prop :=
  ∃ f : X.Kˣ, Inv X (CongruenceSubgroup.Gamma1 (N * l ^ n)) (f : X.K) ∧
    AdicCompletion.eval (idl l) (X.Kl l) n (b ![1, 0]) = X.cls l n f ∧
    (∀ δ ∈ CongruenceSubgroup.Gamma1 N, -δ ∈ CongruenceSubgroup.Gamma (l ^ n) →
      ∃ g : X.K, Inv X (CongruenceSubgroup.Gamma1 (N * l ^ n)) g ∧ (f : X.K) * X.sl (ofSL δ) f = g ^ (l ^ n)) ∧
    IsDl X A l n 1 f φ

def nrmT (X : Tower Ω ε) (M : ℕ) (f : X.K) : X.K := ∏ b ∈ Finset.range M, X.sl (ofSL (ModularGroup.T ^ b)) f

def sgN (X : Tower Ω ε) (c N M : ℕ) (a : ℤ × ℤ) : X.K :=
  X.sl (toGQ !![(N : ℤ), 0; 0, 1]) (siegel X c ![(a.1 : ℚ) / M, (a.2 : ℚ) / M])

def coefQ (M : ℕ) (f : ℕ → Ω) (r : ℚ) : Ω := if 0 ≤ r ∧ (r * M).den = 1 then f (r * M).num.toNat else 0

def IsLamG (ε : Ω →+* ℂ) (l n m : ℕ) (s : Ω ≃ₐ[ℚ] Ω) (t : ZMod (l ^ n)) : Prop :=
  (s ^ (l ^ (n - m))) (eOm ε (1 / (l : ℚ) ^ (2 * n))) = eOm ε (1 / (l : ℚ) ^ n) ^ t.val * eOm ε (1 / (l : ℚ) ^ (2 * n))

end Global

section Local

open GlobalTheory.K5

variable {p : ℕ} [Fact p.Prime] {Ω : Type*} [Field Ω] [Algebra (O0 p) Ω]

structure IsReb (T : GlobalTheory.K5.Tower p Ω) (n : ℕ) (ψ : O0 p →+* Ω) : Prop where
  inj : Function.Injective ψ
  par : ψ (qO p) = T.qq n
  sub : ∀ a b : Lau p, (∀ i : ℤ, b.coeff ((p : ℤ) ^ n * i) = a.coeff i) → (∀ r : ℤ, ¬ (p : ℤ) ^ n ∣ r → b.coeff r = 0) →
    ψ (algebraMap (Lau p) (O0 p) b) = algebraMap (O0 p) Ω (algebraMap (Lau p) (O0 p) a)
  rng : ψ.range = (Algebra.adjoin (O0 p) {T.qq n}).toSubring

def thL (a : Lau p) : Lau p where
  coeff r := (r : ℤ_[p]) * a.coeff r
  isPWO_support' := a.isPWO_support.mono (fun r hr h => hr (by simp [h]))

def zp (Ω : Type*) [Field Ω] [Algebra (O0 p) Ω] (z : ℤ_[p]) : Ω :=
  algebraMap (O0 p) Ω (algebraMap (Lau p) (O0 p) (HahnSeries.single 0 z))

def Ev (ψ : O0 p →+* Ω) (c : ℤ → Ω) (x x' : Ω) : Prop :=
  ∃ (d : ℕ) (e : Fin d → Ω) (a : Fin d → Lau p), (∀ t, IsInt (p := p) (e t) ∧ IsAlgZp (p := p) (e t)) ∧
    (∀ r, c r = ∑ t, e t * zp Ω ((a t).coeff r)) ∧ x = ∑ t, e t * ψ (algebraMap (Lau p) (O0 p) (a t)) ∧
    x' = ∑ t, e t * ψ (algebraMap (Lau p) (O0 p) (thL (a t)))

end Local

end GlobalTheory.Glue
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep
section
noncomputable section

open scoped MatrixGroups TensorProduct
open Matrix

namespace GlobalTheory.KZ

def SSPotA (N l w : ℕ) (lam : Letter → ℂ) : Prop :=
  ∃ P ∈ Algebra.adjoin ℂ (FreeAlgebra.ι ℂ '' {T : Letter | admitted N l T}),
    FreeAlgebra.lift ℂ lam P = 1 ∧ ∀ F ∈ Pot ℂ w (Gam N l), ∀ T : Letter, admitted N l T →
    (opL ℂ N l T - lam T • (1 : Module.End ℂ (ℂ → MvPolynomial (Fin 2) ℂ)))
      (FreeAlgebra.lift ℂ (opL ℂ N l) P F) ∈ Triv ℂ w (Gam N l)

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

namespace SSAdm

variable {R : Type} [CommRing R] {A : Set Letter}

theorem lift_congr {B : Type} [Semiring B] [Algebra R B] {f g : Letter → B} (h : ∀ T ∈ A, f T = g T)
    {P : FreeAlgebra R Letter} (hP : P ∈ Algebra.adjoin R (FreeAlgebra.ι R '' A)) :
    FreeAlgebra.lift R f P = FreeAlgebra.lift R g P := by
  induction hP using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨T, hT, rfl⟩ := hx
    simp [h T hT]
  | algebraMap r => simp
  | add x y _ _ hx hy => simp [hx, hy]
  | mul x y _ _ hx hy => simp [hx, hy]

variable {M : Type} [AddCommGroup M] [Module R M]


open scoped MatrixGroups TensorProduct in
open Matrix in
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} in
variable {R : Type} [CommRing R] {A : Set _root_.GlobalTheory.KZ.Letter} in
variable {M : Type} [AddCommGroup M] [Module R M] in
theorem _root_.GlobalTheory.KZ.SSAdm.lift_sub_smul_mem {f : _root_.GlobalTheory.KZ.Letter → Module.End R M}
    {lam : _root_.GlobalTheory.KZ.Letter → R} {W : Submodule R M}
    (hW : ∀ T ∈ A, ∀ x ∈ W, f T x ∈ W) {x : M} (hx : ∀ T ∈ A, f T x - lam T • x ∈ W)
    {P : FreeAlgebra R _root_.GlobalTheory.KZ.Letter} (hP : P ∈ Algebra.adjoin R (FreeAlgebra.ι R '' A)) :
    FreeAlgebra.lift R f P x - FreeAlgebra.lift R lam P • x ∈ W := by
  have key : ∀ P ∈ Algebra.adjoin R (FreeAlgebra.ι R '' A),
      (∀ y ∈ W, FreeAlgebra.lift R f P y ∈ W) ∧
        FreeAlgebra.lift R f P x - FreeAlgebra.lift R lam P • x ∈ W := by
    intro P hP
    induction hP using Algebra.adjoin_induction with
    | mem P hP =>
      obtain ⟨T, hT, rfl⟩ := hP
      simp only [FreeAlgebra.lift_ι_apply]
      exact ⟨hW T hT, hx T hT⟩
    | algebraMap r =>
      simp only [AlgHom.commutes, Module.algebraMap_end_apply, Algebra.algebraMap_self,
        RingHom.id_apply, sub_self]
      exact ⟨fun y hy => W.smul_mem r hy, W.zero_mem⟩
    | add P Q _ _ hP hQ =>
      refine ⟨fun y hy => ?_, ?_⟩
      · rw [map_add (f := _), LinearMap.add_apply]
        exact W.add_mem (hP.1 y hy) (hQ.1 y hy)
      · convert W.add_mem hP.2 hQ.2 using 1
        simp only [map_add (f := _), LinearMap.add_apply, add_smul]
        abel
    | mul P Q _ _ hP hQ =>
      refine ⟨fun y hy => ?_, ?_⟩
      · rw [map_mul, Module.End.mul_apply]
        exact hP.1 _ (hQ.1 y hy)
      · convert W.add_mem (hP.1 _ hQ.2) (W.smul_mem (FreeAlgebra.lift R lam Q) hP.2) using 1
        simp only [map_mul, Module.End.mul_apply, map_sub, LinearMap.map_smul, smul_sub,
          smul_smul]
        rw [mul_comm (FreeAlgebra.lift R lam Q)]
        abel
  exact (key P hP).2

theorem eigen_of_two_step {f : Letter → Module.End R M} {lam : Letter → R} {Z : Submodule R M}
    (hZ : ∀ T ∈ A, ∀ z ∈ Z, f T z ∈ Z) {P : FreeAlgebra R Letter}
    (hP : P ∈ Algebra.adjoin R (FreeAlgebra.ι R '' A)) (h1 : FreeAlgebra.lift R lam P = 1) {x : M}
    (hPx : ∀ T ∈ A, (f T - lam T • (1 : Module.End R M)) (FreeAlgebra.lift R f P x) ∈ Z)
    (hx : ∀ S ∈ A, ∀ T ∈ A,
      (f S - lam S • (1 : Module.End R M)) ((f T - lam T • (1 : Module.End R M)) x) ∈ Z) :
    ∀ T ∈ A, (f T - lam T • (1 : Module.End R M)) x ∈ Z := by
  let W : Submodule R M := ⨅ T ∈ A, Z.comap (f T - lam T • (1 : Module.End R M))
  have hmem : ∀ y, y ∈ W ↔ ∀ T ∈ A, (f T - lam T • (1 : Module.End R M)) y ∈ Z := by
    intro y; simp only [W, Submodule.mem_iInf, Submodule.mem_comap]
  have hZW : ∀ z ∈ Z, z ∈ W := fun z hz => (hmem z).2 fun T hT => by
    simpa using Z.sub_mem (hZ T hT z hz) (Z.smul_mem _ hz)
  have hW : ∀ T ∈ A, ∀ y ∈ W, f T y ∈ W := fun T hT y hy => by
    have h := W.add_mem (hZW _ ((hmem y).1 hy T hT)) (W.smul_mem (lam T) hy)
    simpa using h
  have hx' : ∀ T ∈ A, f T x - lam T • x ∈ W := fun T hT => (hmem _).2 fun S hS => by
    simpa using hx S hS T hT
  have h2 := lift_sub_smul_mem hW hx' hP
  rw [h1, one_smul] at h2
  have h3 := W.sub_mem ((hmem _).2 hPx) h2
  rw [sub_sub_cancel] at h3
  exact (hmem x).1 h3

end SSAdm

theorem SSPotA_congr {N l w : ℕ} {lam lam' : Letter → ℂ} (h : ∀ T, admitted N l T → lam T = lam' T) :
    SSPotA N l w lam ↔ SSPotA N l w lam' := by
  have key : ∀ {a b : Letter → ℂ}, (∀ T, admitted N l T → a T = b T) → SSPotA N l w a → SSPotA N l w b := by
    rintro a b hab ⟨P, hP, h1, h2⟩
    refine ⟨P, hP, ?_, fun F hF T hT => ?_⟩
    · rw [← SSAdm.lift_congr (A := {T | admitted N l T}) hab hP, h1]
    · rw [← hab T hT]; exact h2 F hF T hT
  exact ⟨key h, key fun T hT => (h T hT).symm⟩

end GlobalTheory.KZ
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Foundations.IsIntegralIff
section
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc

namespace GlobalTheory.HL.Model

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem hf_add_left (L : LocE F E) {n : ℕ} (H : Matrix (Fin n) (Fin n) E) (a b y : Fin n → E) :
    hf L H (a + b) y = hf L H a y + hf L H b y := by
  simp [hf, add_mul, Finset.sum_add_distrib]

theorem hf_smul_left (L : LocE F E) {n : ℕ} (H : Matrix (Fin n) (Fin n) E) (c : E) (a y : Fin n → E) :
    hf L H (c • a) y = c * hf L H a y := by
  simp [hf, Finset.mul_sum, mul_assoc]

theorem hf_add_right (L : LocE F E) {n : ℕ} (H : Matrix (Fin n) (Fin n) E) (a b y : Fin n → E) :
    hf L H y (a + b) = hf L H y a + hf L H y b := by
  simp [hf, map_add (f := _), mul_add, Finset.sum_add_distrib]

theorem hf_smul_right (L : LocE F E) {n : ℕ} (H : Matrix (Fin n) (Fin n) E) (c : E) (a y : Fin n → E) :
    hf L H y (c • a) = L.cj c * hf L H y a := by
  unfold hf
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, map_mul]
  ring

theorem hf_symm (L : LocE F E) {n : ℕ} {H : Matrix (Fin n) (Fin n) E} (h : IsHerm L H)
    (x y : Fin n → E) : hf L H y x = L.cj (hf L H x y) := by
  have hH : ∀ i j, L.cj (H j i) = H i j := fun i j => congrFun (congrFun h i) j
  unfold hf
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, L.cj_cj, hH]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

def stdLat (L : LocE F E) (n : ℕ) : Submodule L.O (Fin n → E) :=
  Submodule.span L.O (Set.range fun i : Fin n => (Pi.single i 1 : Fin n → E))

theorem nontrivial (L : LocE F E) : Nontrivial E := by
  exact Module.nontrivial_of_finrank_pos (R := F) (by rw [L.rank]; norm_num)

end GlobalTheory.HL.Model
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Foundations.IsRootOne
section
noncomputable section

open scoped MatrixGroups TensorProduct
open Matrix

namespace GlobalTheory.KZ.H3

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

def JHol (X : Tower Ω ε) : Prop :=
  ∃ φ : ℂ → ℂ, X.an X.jK = (φ : Mero) ∧ DifferentiableOn ℂ φ Hs

def IsRoot (X : Tower Ω ε) (m : ℕ) (f : X.Kˣ) (a b : ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ a Hs ∧ DifferentiableOn ℂ b Hs ∧ (b : Mero) ≠ 0 ∧
    X.an (f : X.K) * (b : Mero) ^ m = (a : Mero) ^ m

def Kum (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ) (x : X.Khat l) (χ : SL(2, ℤ) → ZMod (l ^ n)) : Prop :=
  ∃ (f : X.Kˣ) (a b : ℂ → ℂ) (M : ℕ), 0 < M ∧ AdicCompletion.eval (idl l) (X.Kl l) n x = X.cls l n f ∧
    IsRoot X (l ^ n) f a b ∧ ∀ δ ∈ CongruenceSubgroup.Gamma M, ∀ z ∈ Hs,
      a (mob (ofSL δ) z) * b z =
        Complex.exp (2 * Real.pi * Complex.I * ((χ δ).val : ℂ) / ((l : ℂ) ^ n)) * (a z * b (mob (ofSL δ) z))

def Near {V : Type} (φ ψ : SL(2, ℤ) → V) : Prop :=
  ∃ M : ℕ, 0 < M ∧ ∀ δ ∈ CongruenceSubgroup.Gamma M, φ δ = ψ δ

def R1 (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (x : X.Khat l) (h : ℂ → ℤ_[l]) : Prop :=
  ∀ n : ℕ, ∃ χ : SL(2, ℤ) → ZMod (l ^ n), Kum X l n x χ ∧ ∃ M : ℕ, 0 < M ∧ ∀ δ ∈ CongruenceSubgroup.Gamma M, ∀ z ∈ Hs,
    PadicInt.toZModPow n (h (mob (ofSL δ) z) - h z) = χ δ

def Rel (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (b : X.Fn l) (F : ℂ → MvPolynomial (Fin 2) ℤ_[l]) : Prop :=
  ∀ u : Fin 2 → ℤ_[l], R1 X l (b u) (fun z => MvPolynomial.eval u (F z))


open scoped Classical in
open Classical in
def cj (m : Matrix (Fin 2) (Fin 2) ℤ) (δ : SL(2, ℤ)) : SL(2, ℤ) :=
  if h : ∃ δ' : SL(2, ℤ), m * (δ : Matrix (Fin 2) (Fin 2) ℤ) = (δ' : Matrix (Fin 2) (Fin 2) ℤ) * m then h.choose else 1

def IsCoc {R : Type} [CommRing R] (w : ℕ) (Γ : Subgroup SL(2, ℤ)) (c : SL(2, ℤ) → MvPolynomial (Fin 2) R) : Prop :=
  (∀ γ ∈ Γ, (c γ).IsHomogeneous w) ∧
    ∀ γ ∈ Γ, ∀ δ ∈ Γ, c (γ * δ) = slP (δ : Matrix (Fin 2) (Fin 2) ℤ) (c γ) + c δ

def IsFam (l w : ℕ) (Γ : Subgroup SL(2, ℤ)) (Φ : (n : ℕ) → SL(2, ℤ) → MvPolynomial (Fin 2) (ZMod (l ^ n))) : Prop :=
  (∀ n δ, (Φ n δ).IsHomogeneous w) ∧
  (∀ n, ∃ M : ℕ, 0 < M ∧ ∀ δ ∈ CongruenceSubgroup.Gamma M, ∀ δ' ∈ CongruenceSubgroup.Gamma M,
    Φ n (δ * δ') = Φ n δ + Φ n δ') ∧
  (∀ n, ∀ γ ∈ Γ, Near (fun δ => slP (γ : Matrix (Fin 2) (Fin 2) ℤ) (Φ n (γ * δ * γ⁻¹))) (Φ n)) ∧
  ∀ n, Near (fun δ => MvPolynomial.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ n)) (ZMod (l ^ n))) (Φ (n + 1) δ)) (Φ n)

def mon (R : Type) [CommRing R] (w : ℕ) (i : Fin (w + 1)) : MvPolynomial (Fin 2) R :=
  MvPolynomial.X 0 ^ (i : ℕ) * MvPolynomial.X 1 ^ (w - (i : ℕ))

def cf (w : ℕ) (m : Matrix (Fin 2) (Fin 2) ℤ) (i k : Fin (w + 1)) : ℤ :=
  AddMonoidAlgebra.coeff (slP m (mon ℤ w k)) (Finsupp.single 0 (i : ℕ) + Finsupp.single 1 (w - (i : ℕ)))

def SSBS (S : Letter → Prop) (X : Tower Ω ε) (N l w : ℕ) [Fact l.Prime] (E : Type) [Field E] [Algebra ℤ_[l] E]
    (lam : Letter → E) : Prop :=
  ∃ P ∈ Algebra.adjoin E (FreeAlgebra.ι E '' {T | S T}), FreeAlgebra.lift E lam P = 1 ∧ ∀ x ∈ X.VB N l w E, ∀ T : Letter, S T →
    (X.opV N l E T - lam T • (1 : Module.End E (E ⊗[ℤ_[l]] X.Fn l))) (FreeAlgebra.lift E (X.opV N l E) P x) = 0

def abelian₂ (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (E : Type) [Field E] [Algebra ℤ_[l] E] :
    Submodule E ((E ⊗[ℤ_[l]] X.Fn l) × (ℂ → MvPolynomial (Fin 2) E)) :=
  Submodule.span E {p | ∃ b F, Rel X l b F ∧
    p = ((1 : E) ⊗ₜ[ℤ_[l]] b, fun z => MvPolynomial.map (algebraMap ℤ_[l] E) (F z))}

def deh : MvPolynomial (Fin 2) ℂ →ₐ[ℂ] Polynomial ℂ := MvPolynomial.aeval ![Polynomial.X, 1]

def cocP (Γ : Subgroup SL(2, ℤ)) (F : ℂ → MvPolynomial (Fin 2) ℂ) : Γ → Polynomial ℂ := fun γ =>
  deh (slP ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) (F (mob (ofSL γ) Complex.I)) - F Complex.I)

theorem isRoot_one (X : Tower Ω ε) (m : ℕ) (h : ((fun _ => 1 : ℂ → ℂ) : Mero) ≠ 0) :
    IsRoot X m 1 (fun _ => 1) (fun _ => 1) :=
  ⟨differentiableOn_const 1, differentiableOn_const 1, h, by simp⟩

end GlobalTheory.KZ.H3
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Foundations.IsScalarTowerMdlOm
section
noncomputable section

open scoped MatrixGroups TensorProduct
open Matrix

namespace GlobalTheory.ZetaB

open GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.NeedB GlobalTheory.KEdge

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

def tInv (l N R : ℕ) : ZMod N := ((l : ZMod N) ^ R)⁻¹

def uIdxMu (l N R : ℕ) (x : ZMod N) : Fin 2 → ℚ := ![1 / (l : ℚ) ^ R + ((x * tInv l N R).val : ℚ) / N, 0]

def vIdxMu (l N R : ℕ) : Fin 2 → ℚ := ![((tInv l N R).val : ℚ) / N, 1 / (l : ℚ) ^ R]

abbrev Om (X : Tower Ω ε) : Type := AlgebraicClosure X.K

attribute [local instance] algMdl

theorem isScalarTower_mdl_om (X : Tower Ω ε) (Γ' : Subgroup SL(2, ℤ)) (S : Subgroup (Ω ≃ₐ[ℚ] Ω)) :
    @IsScalarTower (mdl X Γ' S) (lev X Γ') (Om X) Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

attribute [local instance] isScalarTower_mdl_om





open Classical in
def unitOf (X : Tower Ω ε) (a : X.K) : X.Kˣ :=
  letI := Classical.propDecidable (a = 0)
  if h : a = 0 then 1 else Units.mk0 a h

def clsHat (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (a : X.K) : X.Khat l :=
  AdicCompletion.of (idl l) (X.Kl l) ((1 : ℤ_[l]) ⊗ₜ Additive.ofMul (unitOf X a))

def cR (l N : ℕ) (r₀ : ZMod l) : ℤ := (N : ℤ) * ((-r₀ * (N : ZMod l)⁻¹).val : ℤ)

def gR (l N : ℕ) (r₀ : ZMod l) : SL(2, ℤ) :=
  ⟨!![1, 0; cR l N r₀, 1], by simp [Matrix.det_fin_two]⟩



theorem cR_mod (l N : ℕ) [Fact l.Prime] (hN : (N : ZMod l) ≠ 0) (r₀ : ZMod l) : ((cR l N r₀ : ℤ) : ZMod l) = -r₀ := by
  simp only [cR, Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val]
  rw [mul_comm (-r₀), ← mul_assoc, mul_inv_cancel₀ hN, one_mul]


open scoped MatrixGroups TensorProduct in
open Matrix in
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} in
attribute [local instance] _root_.GlobalTheory.K4.algMdl in
theorem _root_.GlobalTheory.ZetaB.eval_clsHat (X : _root_.GlobalTheory.KZ.Tower Ω ε) (l : ℕ)
    [Fact l.Prime] (n : ℕ) (a : X.K) :
    AdicCompletion.eval (_root_.GlobalTheory.KZ.idl l) (X.Kl l) n
        (_root_.GlobalTheory.ZetaB.clsHat X l a) =
      X.cls l n (_root_.GlobalTheory.ZetaB.unitOf X a) := by
  unfold _root_.GlobalTheory.ZetaB.clsHat
  rw [AdicCompletion.eval_of]
  rfl


open scoped MatrixGroups TensorProduct in
open Matrix in
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} in
attribute [local instance] _root_.GlobalTheory.K4.algMdl in
theorem _root_.GlobalTheory.ZetaB.unitOf_val (X : _root_.GlobalTheory.KZ.Tower Ω ε) {a : X.K}
    (ha : a ≠ 0) : ((_root_.GlobalTheory.ZetaB.unitOf X a : (X.K)ˣ) : X.K) = a := by
  unfold _root_.GlobalTheory.ZetaB.unitOf
  rw [dite_eq_right ha]
  rfl


open scoped MatrixGroups TensorProduct in
open Matrix in
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} in
attribute [local instance] _root_.GlobalTheory.K4.algMdl in
theorem _root_.GlobalTheory.ZetaB.unitOf_zero (X : _root_.GlobalTheory.KZ.Tower Ω ε) :
    _root_.GlobalTheory.ZetaB.unitOf X 0 = 1 := by
  unfold _root_.GlobalTheory.ZetaB.unitOf
  rw [dite_eq_left rfl]

end GlobalTheory.ZetaB
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Foundations.RayPrimes
section
noncomputable section

open Finset ArithmeticFunction NumberField IsDedekindDomain
open scoped nonZeroDivisors

namespace GlobalTheory.Mem.An

def zerosIn {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (t T : ℝ) : Set ℂ :=
  {ρ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im - t| ≤ T ∧ DirichletCharacter.LFunction χ ρ = 0}

def zmult {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (ρ : ℂ) : ℕ :=
  analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ

def zsum {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (t T : ℝ) (f : ℂ → ℂ) : ℂ :=
  ∑ᶠ ρ ∈ zerosIn χ t T, (zmult χ ρ : ℂ) * f ρ

def zsumR {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (t T : ℝ) (f : ℂ → ℝ) : ℝ :=
  ∑ᶠ ρ ∈ zerosIn χ t T, (zmult χ ρ : ℝ) * f ρ

def psiChi {q : ℕ} (χ : DirichletCharacter ℂ q) (u : ℝ) : ℂ :=
  ∑ n ∈ Icc 1 ⌊u⌋₊, ((Λ n : ℝ) : ℂ) * χ (n : ZMod q)

def rayI {K : Type} [Field K] [NumberField K] (𝔮 : Ideal (𝓞 K)) : Subgroup (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
  Subgroup.closure {I | ∃ v : HeightOneSpectrum (𝓞 K), ¬ v.asIdeal ∣ 𝔮 ∧
    (I : FractionalIdeal (𝓞 K)⁰ K) = (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K)}

def rayP {K : Type} [Field K] [NumberField K] (𝔮 : Ideal (𝓞 K)) : Subgroup (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
  Subgroup.closure {I | ∃ a : 𝓞 K, a - 1 ∈ 𝔮 ∧
    (I : FractionalIdeal (𝓞 K)⁰ K) = ((Ideal.span {a} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)}

def rayNo {K : Type} [Field K] [NumberField K] (𝔮 : Ideal (𝓞 K)) : ℕ := (rayP 𝔮).relIndex (rayI 𝔮)

def rayPrimes {K : Type} [Field K] [NumberField K] (𝔮 : Ideal (𝓞 K)) (X : ℝ) : Set (HeightOneSpectrum (𝓞 K)) :=
  {v | ¬ v.asIdeal ∣ 𝔮 ∧ (Ideal.absNorm v.asIdeal : ℝ) ≤ X ∧
    ∃ I ∈ rayP 𝔮, (I : FractionalIdeal (𝓞 K)⁰ K) = (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K)}

def NormOne (d M p : ℕ) : Prop :=
  ∃ A B : ℤ, A ^ 2 + (d : ℤ) * B ^ 2 = 4 * (p : ℤ) ∧ (M : ℤ) ∣ B ∧ (2 * (M : ℤ)) ∣ A - 2 - B


open Classical in
def normPrimes (d M : ℕ) (X Y : ℝ) : Finset ℕ := by
  classical
  exact (Ioc ⌊X⌋₊ ⌊Y⌋₊).filter (fun p => p.Prime ∧ NormOne d M p)

end GlobalTheory.Mem.An
end
end

