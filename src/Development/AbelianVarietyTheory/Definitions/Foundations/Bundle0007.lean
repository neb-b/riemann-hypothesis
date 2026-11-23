module

public import Mathlib
public import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExpUpper
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
section
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc
open scoped Pointwise

namespace GlobalTheory.HL

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

def hf (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) : E :=
  ∑ i, ∑ j, x i * Hm i j * L.cj (y j)

def cT (L : LocE F E) {m n : Type} (A : Matrix m n E) : Matrix n m E := fun i j => L.cj (A j i)

def IsHerm (L : LocE F E) {m : Type} (A : Matrix m m E) : Prop := cT L A = A

def IsHermND (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) : Prop :=
  IsHerm L Hm ∧ IsUnit Hm.det

def IsIntM (L : LocE F E) {m n : Type} (A : Matrix m n E) : Prop := ∀ i j, A i j ∈ L.O

def perp (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (Y : Submodule E (Fin n → E)) :
    Submodule E (Fin n → E) where
  carrier := {x | ∀ y ∈ Y, hf L Hm x y = 0}
  zero_mem' := by intro y _; simp [hf]
  add_mem' := by
    intro a b ha hb y hy
    have h : hf L Hm (a + b) y = hf L Hm a y + hf L Hm b y := by
      simp [hf, add_mul, Finset.sum_add_distrib]
    rw [h, ha y hy, hb y hy, add_zero]
  smul_mem' := by
    intro c a ha y hy
    have h : hf L Hm (c • a) y = c * hf L Hm a y := by
      simp [hf, Finset.mul_sum, mul_assoc]
    rw [h, ha y hy, mul_zero]

def IsLat (L : LocE F E) {n : ℕ} (Λ : Submodule L.O (Fin n → E)) : Prop :=
  Λ.FG ∧ Submodule.span E (Λ : Set (Fin n → E)) = ⊤

def IsSD (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (Λ : Submodule L.O (Fin n → E)) : Prop :=
  IsLat L Λ ∧ ∀ y, (∀ x ∈ Λ, hf L Hm x y ∈ L.O) ↔ y ∈ Λ

def isomG (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) :
    Subgroup ((Fin n → E) ≃ₗ[E] (Fin n → E)) where
  carrier := {g | ∀ x y, hf L Hm (g x) (g y) = hf L Hm x y}
  one_mem' := fun _ _ => rfl
  mul_mem' := by
    intro a b ha hb x y
    exact (ha (b x) (b y)).trans (hb x y)
  inv_mem' := by
    intro a ha x y
    have h := ha (a.symm x) (a.symm y)
    simp only [LinearEquiv.apply_symm_apply] at h
    exact h.symm

def unipOn {n : ℕ} (A B : Submodule E (Fin n → E)) : Subgroup ((Fin n → E) ≃ₗ[E] (Fin n → E)) where
  carrier := {g | (∀ v, g v ∈ A ↔ v ∈ A) ∧ ∀ v ∈ A, g v - v ∈ B}
  one_mem' := ⟨fun _ => Iff.rfl, fun v _ => by simp⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨fun v => (ha (b v)).trans (hb v), fun v hv => ?_⟩
    have h : (a * b) v - v = (a (b v) - b v) + (b v - v) := by simp
    rw [h]
    exact B.add_mem (ha' _ ((hb v).2 hv)) (hb' v hv)
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    have h1 : ∀ v, a.symm v ∈ A ↔ v ∈ A := fun v => by
      have := ha (a.symm v)
      simp only [LinearEquiv.apply_symm_apply] at this
      exact this.symm
    refine ⟨h1, fun v hv => ?_⟩
    have h2 := ha' _ ((h1 v).2 hv)
    simp only [LinearEquiv.apply_symm_apply] at h2
    have h3 : a⁻¹ v - v = -(v - a.symm v) := by
      rw [neg_sub]; rfl
    rw [h3]
    exact B.neg_mem h2

def eich (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (x u : Fin n → E) (s : E)
    (v : Fin n → E) : Fin n → E :=
  v + hf L Hm v u • x - hf L Hm v x • (u + s • x)

def invVol {G : Type*} [Group G] (K0 K : Subgroup G) : ℝ :=
  (K.relIndex K0 : ℝ) / (K0.relIndex K : ℝ)

def resQ (ϖ : 𝒪[F]) : ℕ := Nat.card (𝒪[F] ⧸ Ideal.span {ϖ})

def vE (L : LocE F E) (ϖ : 𝒪[F]) (c : E) : ℤ :=
  sSup {m : ℤ | ∃ y ∈ L.O, c = algebraMap F E ((ϖ : F) ^ m) * y}

def lead {N : ℕ} (Z : Matrix (Fin N) (Fin N) E) (l : Fin (N + 1)) : E :=
  (Z.submatrix (Fin.castLE (Nat.lt_succ_iff.mp l.2)) (Fin.castLE (Nat.lt_succ_iff.mp l.2))).det

end GlobalTheory.HL
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Foundations.OpLDOneSubMemTriv
section
noncomputable section

open scoped MatrixGroups TensorProduct
open Matrix

namespace GlobalTheory.KZ

def slP {R : Type} [CommRing R] (m : Matrix (Fin 2) (Fin 2) ℤ) : MvPolynomial (Fin 2) R →ₐ[R] MvPolynomial (Fin 2) R :=
  MvPolynomial.aeval fun i => (m i 0 : R) • MvPolynomial.X 0 + (m i 1 : R) • MvPolynomial.X 1

def Pot (R : Type) [CommRing R] (w : ℕ) (Γ : Subgroup SL(2, ℤ)) : Set (ℂ → MvPolynomial (Fin 2) R) :=
  {F | (∀ z, (F z).IsHomogeneous w) ∧ ∀ γ ∈ Γ, ∃ p, ∀ z ∈ Hs,
    slP (γ : Matrix (Fin 2) (Fin 2) ℤ) (F (mob (ofSL γ) z)) - F z = p}

def Triv (R : Type) [CommRing R] (w : ℕ) (Γ : Subgroup SL(2, ℤ)) : Set (ℂ → MvPolynomial (Fin 2) R) :=
  {F | ∃ (ψ : ℂ → MvPolynomial (Fin 2) R) (p : MvPolynomial (Fin 2) R),
    (∀ γ ∈ Γ, ∀ z ∈ Hs, slP (γ : Matrix (Fin 2) (Fin 2) ℤ) (ψ (mob (ofSL γ) z)) = ψ z) ∧ ∀ z ∈ Hs, F z = ψ z + p}

def opP (R : Type) [CommRing R] (m : Matrix (Fin 2) (Fin 2) ℤ) :
    (ℂ → MvPolynomial (Fin 2) R) →ₗ[R] (ℂ → MvPolynomial (Fin 2) R) where
  toFun F z := slP m (F (mob (toGQ m) z))
  map_add' F G := by funext z; simp
  map_smul' c F := by funext z; simp

def opL (R : Type) [CommRing R] (N l : ℕ) :
    Letter → ((ℂ → MvPolynomial (Fin 2) R) →ₗ[R] (ℂ → MvPolynomial (Fin 2) R))
  | Letter.T q => (∑ j ∈ Finset.range q, opP R !![1, (j : ℤ); 0, (q : ℤ)]) +
      opP R ((sgD N l q : Matrix (Fin 2) (Fin 2) ℤ) * !![(q : ℤ), 0; 0, 1])
  | Letter.U => ∑ j ∈ Finset.range l, opP R !![1, (j : ℤ); 0, (l : ℤ)]
  | Letter.D d => opP R (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ)

def admitted (N l : ℕ) : Letter → Prop
  | Letter.T q => q.Prime ∧ ¬ q ∣ N * l
  | Letter.U => True
  | Letter.D d => Nat.Coprime d N

def LetAlg (R : Type) [CommRing R] (S : Letter → Prop) : Subalgebra R (FreeAlgebra R Letter) :=
  Algebra.adjoin R (FreeAlgebra.ι R '' {T | S T})

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

def FrobAt (q : ℕ) (s : Ω ≃ₐ[ℚ] Ω) : Prop :=
  ∃ V : ValuationSubring Ω, ((q : ℕ) : Ω) ∈ V.nonunits ∧ ∀ x ∈ V, s x ∈ V ∧ V.valuation (s x - x ^ q) < 1

def Tower.VB (X : Tower Ω ε) (N l w : ℕ) [Fact l.Prime] (E : Type) [Field E] [Algebra ℤ_[l] E] :
    Submodule E (E ⊗[ℤ_[l]] X.Fn l) :=
  LinearMap.range (LinearMap.baseChange E (X.B N l w).subtype)

def Tower.opV (X : Tower Ω ε) (N l : ℕ) [Fact l.Prime] (E : Type) [Field E] [Algebra ℤ_[l] E] (T : Letter) :
    Module.End E (E ⊗[ℤ_[l]] X.Fn l) :=
  LinearMap.baseChange E (X.op N l T)

def Tower.galV (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (E : Type) [Field E] [Algebra ℤ_[l] E] (s : Ω ≃ₐ[ℚ] Ω) :
    Module.End E (E ⊗[ℤ_[l]] X.Fn l) :=
  LinearMap.baseChange E (X.galB l s)

namespace Betti

section Letters

variable {R : Type} [CommRing R] {S : Letter → Prop}

theorem lift_congr {A : Type} [Semiring A] [Algebra R A] {f g : Letter → A} (h : ∀ T, S T → f T = g T)
    {P : FreeAlgebra R Letter} (hP : P ∈ LetAlg R S) : FreeAlgebra.lift R f P = FreeAlgebra.lift R g P := by
  unfold LetAlg at hP
  induction hP using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨T, hT, rfl⟩ := hx
    simp [h T hT]
  | algebraMap r => simp
  | add x y _ _ hx hy => simp [hx, hy]
  | mul x y _ _ hx hy => simp [hx, hy]

end Letters

theorem exists_isDiam {N l d : ℕ} (hN : N ≠ 0) (hl : l ≠ 0) (hd : Nat.Coprime d N) : ∃ γ, IsDiam N l d γ := by
  have : NeZero (N * l) := ⟨Nat.mul_ne_zero hN hl⟩
  have hNl : N ∣ N * l := Dvd.intro l rfl
  obtain ⟨u, hu⟩ := ZMod.unitsMap_surjective hNl (ZMod.unitOfCoprime d hd)
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 (ZMod.val_coe_unit_coprime u)
  have hdet : (!![a, -b; ((N * l : ℕ) : ℤ), ((u : ZMod (N * l)).val : ℤ)]).det = 1 := by
    rw [Matrix.det_fin_two_of]
    linear_combination hab
  obtain ⟨γ, hγ⟩ : ∃ γ : SL(2, ℤ),
      (γ : Matrix (Fin 2) (Fin 2) ℤ) = !![a, -b; ((N * l : ℕ) : ℤ), ((u : ZMod (N * l)).val : ℤ)] :=
    ⟨⟨_, hdet⟩, rfl⟩
  refine ⟨γ, Subgroup.mem_inf.2 ⟨?_, ?_⟩, ?_⟩
  · rw [CongruenceSubgroup.Gamma0_mem, hγ]
    simp
  · rw [CongruenceSubgroup.Gamma0_mem, hγ]
    simp
  · have hcast : (((u : ZMod (N * l)).val : ℕ) : ZMod N) = d := by
      rw [ZMod.natCast_val, ← ZMod.unitsMap_val hNl, hu, ZMod.coe_unitOfCoprime]
    simpa [en, hγ] using hcast

theorem isDiam_sgD {N l d : ℕ} (hN : N ≠ 0) (hl : l ≠ 0) (hd : Nat.Coprime d N) : IsDiam N l d (sgD N l d) := by
  exact Classical.epsilon_spec (exists_isDiam hN hl hd)

theorem isDiam_sgD_of_adm {N l q : ℕ} (h : admitted N l (Letter.T q)) : IsDiam N l q (sgD N l q) := by
  have h' : q.Prime ∧ ¬ q ∣ N * l := h
  obtain ⟨hq, hqN⟩ := h'
  have hN : N ≠ 0 := by
    rintro rfl
    exact hqN (by simp)
  have hl : l ≠ 0 := by
    rintro rfl
    exact hqN (by simp)
  exact isDiam_sgD hN hl ((Nat.Prime.coprime_iff_not_dvd hq).2 fun h'' => hqN (h''.mul_right l))

section Slash

variable {R : Type} [CommRing R]

theorem slP_X (m : Matrix (Fin 2) (Fin 2) ℤ) (i : Fin 2) :
    slP (R := R) m (MvPolynomial.X i) = (m i 0 : R) • MvPolynomial.X 0 + (m i 1 : R) • MvPolynomial.X 1 := by
  simp only [slP, MvPolynomial.aeval_X]

theorem polySlash_one (p : MvPolynomial (Fin 2) R) : slP 1 p = p := by
  have h1 : slP (R := R) 1 = AlgHom.id R _ := by
    apply MvPolynomial.algHom_ext
    intro i
    rw [slP_X]
    fin_cases i <;> simp [Matrix.one_apply]
  rw [h1, AlgHom.id_apply]

theorem polySlash_polySlash (m m' : Matrix (Fin 2) (Fin 2) ℤ) (p : MvPolynomial (Fin 2) R) :
    slP m' (slP m p) = slP (m * m') p := by
  have h1 : (slP m').comp (slP m) = slP (R := R) (m * m') := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, slP_X, map_add (f := _), map_smul, Matrix.mul_apply, Fin.sum_univ_two,
      Int.cast_add, Int.cast_mul]
    module
  exact DFunLike.congr_fun h1 p

theorem polySlash_isHomogeneous (m : Matrix (Fin 2) (Fin 2) ℤ) {p : MvPolynomial (Fin 2) R} {w : ℕ} (hp : p.IsHomogeneous w) :
    (slP m p).IsHomogeneous w := by
  have h1 := hp.aeval (fun i => (m i 0 : R) • MvPolynomial.X 0 + (m i 1 : R) • MvPolynomial.X 1)
    (n := 1) fun i => (MvPolynomial.homogeneousSubmodule (Fin 2) R 1).add_mem
      ((MvPolynomial.homogeneousSubmodule (Fin 2) R 1).smul_mem _ (MvPolynomial.isHomogeneous_X R 0))
      ((MvPolynomial.homogeneousSubmodule (Fin 2) R 1).smul_mem _ (MvPolynomial.isHomogeneous_X R 1))
  rw [one_mul] at h1
  exact h1

theorem eval_slP (m : Matrix (Fin 2) (Fin 2) ℤ) (u : Fin 2 → R) (p : MvPolynomial (Fin 2) R) :
    MvPolynomial.eval u (slP m p) = MvPolynomial.eval (m.map (Int.castRingHom R) *ᵥ u) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [slP]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, hp, slP_X, MvPolynomial.eval_X, map_add (f := _), MvPolynomial.smul_eval]
    congr 1
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem toGQ_sl (γ : SL(2, ℤ)) : toGQ (γ : Matrix (Fin 2) (Fin 2) ℤ) = ofSL γ := by
  have h : 0 < (γ : Matrix (Fin 2) (Fin 2) ℤ).det := by
    rw [Matrix.SpecialLinearGroup.det_coe]
    exact one_pos
  unfold toGQ
  rw [dite_eq_left h]
  apply Subtype.ext
  apply Units.ext
  rfl

variable {w : ℕ} {Γ : Subgroup SL(2, ℤ)}

def potSub (R : Type) [CommRing R] (w : ℕ) (Γ : Subgroup SL(2, ℤ)) : Submodule R (ℂ → MvPolynomial (Fin 2) R) where
  carrier := Pot R w Γ
  zero_mem' := ⟨fun _ => MvPolynomial.isHomogeneous_zero _ _ _, fun _ _ => ⟨0, fun _ _ => by simp⟩⟩
  add_mem' := by
    rintro F G ⟨hF, hF'⟩ ⟨hG, hG'⟩
    refine ⟨fun z => (hF z).add (hG z), fun γ hγ => ?_⟩
    obtain ⟨p, hp⟩ := hF' γ hγ
    obtain ⟨q, hq⟩ := hG' γ hγ
    refine ⟨p + q, fun z hz => ?_⟩
    rw [← hp z hz, ← hq z hz]; simp only [Pi.add_apply, map_add (f := _)]; ring
  smul_mem' := by
    rintro c F ⟨hF, hF'⟩
    refine ⟨fun z => (MvPolynomial.homogeneousSubmodule (Fin 2) R w).smul_mem c (hF z), fun γ hγ => ?_⟩
    obtain ⟨p, hp⟩ := hF' γ hγ
    refine ⟨c • p, fun z hz => ?_⟩
    rw [← hp z hz]; simp only [Pi.smul_apply, map_smul, smul_sub]

end Slash

end Betti

end GlobalTheory.KZ
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Foundations.SgC
section
noncomputable section

open scoped UpperHalfPlane MatrixGroups

namespace GlobalTheory.KZ

def sgC (c : ℕ) (x : Fin 2 → ℚ) (z : ℂ) : ℂ := GlobalTheory.Sieg.sg c x (UpperHalfPlane.ofComplex z)


open scoped Classical in
open Classical in
def siegel {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (T : Tower Ω ε) (c : ℕ) (x : Fin 2 → ℚ) : T.K :=
  if h : ∃ f : T.K, T.an f = ((sgC c x : ℂ → ℂ) : Mero) then h.choose else 0

end GlobalTheory.KZ
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSumRowCol
section
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal

noncomputable section
namespace GlobalTheory.RootEx.Model
open GlobalTheory.SplitWeil GlobalTheory.RootEx

variable {k : Type*} [Field k] {n : Type*} [Fintype n] [DecidableEq n] {c : ℕ}

theorem inN_tri {p : ℕ} {g : GL (n ⊕ Fin c) k} (hg : InN p g) : g.val.BlockTriangular (lev p) := by
  intro r s h
  rw [hg r s h.le, Matrix.one_apply_ne]
  rintro rfl; exact lt_irrefl _ h

theorem mul_entry {p : ℕ} {g : GL (n ⊕ Fin c) k} (hg : InN p g) {h : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k}
    (hh : h.BlockTriangular (lev p)) (r s) (hrs : lev p s ≤ lev p r) : (g.val * h) r s = h r s := by
  have : (g.val * h) r s = ((1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) * h) r s := by
    simp only [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun t _ => ?_
    by_cases ht : lev p t ≤ lev p r
    · rw [hg r t ht]
    · rw [hh (show lev p s < lev p t by omega)]; simp
  rw [this, Matrix.one_mul]

def Nsub (k : Type*) [Field k] (n : Type*) [Fintype n] [DecidableEq n] (c p : ℕ) : Subgroup (GL (n ⊕ Fin c) k) where
  carrier := {g | InN p g}
  one_mem' := fun _ _ _ => rfl
  mul_mem' := fun {a b} ha hb r s hrs => by
    rw [Units.val_mul, mul_entry ha (inN_tri hb) r s hrs, hb r s hrs]
  inv_mem' := fun {a} ha r s hrs => by
    have h1 : (a⁻¹).val.BlockTriangular (lev p) := by
      rw [Matrix.coe_units_inv]
      haveI := a.invertible
      exact Matrix.blockTriangular_inv_of_blockTriangular (inN_tri ha)
    rw [← mul_entry ha h1 r s hrs, Units.mul_inv]

theorem mem_N_iff {p : ℕ} {g : GL (n ⊕ Fin c) k} : g ∈ N k n c p ↔ InN p g := by
  have : N k n c p = Nsub k n c p := Subgroup.closure_eq (Nsub k n c p)
  rw [this]; rfl

theorem conj_mem {p : ℕ} {u : GL (n ⊕ Fin c) k} (hu : u ∈ N k n c p) (g : GL n k) :
    (embX c g)⁻¹ * u * embX c g ∈ N k n c p := by
  rw [mem_N_iff] at hu ⊢
  rw [← map_inv]
  have h11 : u.val.toBlocks₁₁ = 1 := by
    ext r s
    have := hu (Sum.inl r) (Sum.inl s) le_rfl
    simpa [Matrix.one_apply, toBlocks₁₁] using this
  have hv : ((embX c g⁻¹) * u * embX c g).val = fromBlocks 1 ((g⁻¹).val * u.val.toBlocks₁₂)
      (u.val.toBlocks₂₁ * g.val) u.val.toBlocks₂₂ := by
    rw [Units.val_mul, Units.val_mul, ← fromBlocks_toBlocks u.val, h11]
    simp [embX, fromBlocks_multiply]
  rintro (r | r) (s | s) h <;> rw [hv]
  · simp [Matrix.one_apply]
  · have : ∀ t, u.val (Sum.inl t) (Sum.inr s) = 0 := fun t => by
      simpa using hu (Sum.inl t) (Sum.inr s) h
    simp [Matrix.mul_apply, toBlocks₁₂, this]
  · have : ∀ t, u.val (Sum.inr r) (Sum.inl t) = 0 := fun t => by
      simpa using hu (Sum.inr r) (Sum.inl t) h
    simp [Matrix.mul_apply, toBlocks₂₁, this]
  · simpa [toBlocks₂₂] using hu (Sum.inr r) (Sum.inr s) h

def mkN (p : ℕ) (e : {rs : (n ⊕ Fin c) × (n ⊕ Fin c) // lev p rs.1 < lev p rs.2} → k) :
    Matrix (n ⊕ Fin c) (n ⊕ Fin c) k :=
  Matrix.of fun r s => if h : lev p r < lev p s then e ⟨(r, s), h⟩ else (1 : Matrix _ _ k) r s

theorem det_mkN (p : ℕ) (e : {rs : (n ⊕ Fin c) × (n ⊕ Fin c) // lev p rs.1 < lev p rs.2} → k) :
    (mkN p e).det = 1 := by
  have ht : (mkN p e).BlockTriangular (lev p) := by
    intro r s h
    have : r ≠ s := by rintro rfl; exact lt_irrefl _ h
    simp [mkN, not_lt.2 h.le, this]
  rw [ht.det]
  refine Finset.prod_eq_one fun a _ => ?_
  have : (mkN p e).toSquareBlock (lev p) a = 1 := by
    ext ⟨r, hr⟩ ⟨s, hs⟩
    simp [toSquareBlock_def, mkN, hr, hs, Matrix.one_apply]
  rw [this, det_one]

def mkNel (p : ℕ) (e : {rs : (n ⊕ Fin c) × (n ⊕ Fin c) // lev p rs.1 < lev p rs.2} → k) : N k n c p :=
  ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (mkN p e) (by rw [det_mkN]; exact one_ne_zero), by
    rw [mem_N_iff]
    intro r s h
    show mkN p e r s = _
    simp [mkN, not_lt.2 h]⟩

section meas
variable [MeasurableSpace k]

theorem coord_embedding (p : ℕ) : MeasurableEmbedding
    (fun (g : N k n c p) (rs : {rs : (n ⊕ Fin c) × (n ⊕ Fin c) // lev p rs.1 < lev p rs.2}) =>
      (g : GL (n ⊕ Fin c) k).val rs.1.1 rs.1.2) ∧ Function.Surjective
    (fun (g : N k n c p) (rs : {rs : (n ⊕ Fin c) × (n ⊕ Fin c) // lev p rs.1 < lev p rs.2}) =>
      (g : GL (n ⊕ Fin c) k).val rs.1.1 rs.1.2) := by
  have hs : Function.Surjective
      (fun (g : N k n c p) (rs : {rs : (n ⊕ Fin c) × (n ⊕ Fin c) // lev p rs.1 < lev p rs.2}) =>
      (g : GL (n ⊕ Fin c) k).val rs.1.1 rs.1.2) := by
    intro e
    refine ⟨mkNel p e, ?_⟩
    funext rs
    show mkN p e _ _ = _
    simp [mkN, rs.2]
  refine ⟨MeasurableEmbedding.of_measurable_inverse (g := mkNel (k := k) p) ?_ ?_ ?_ ?_, hs⟩
  · refine Measurable.of_eval fun rs => ?_
    have h1 : Measurable (fun g : GL (n ⊕ Fin c) k => g.val) := comap_measurable _
    have h2 : Measurable (fun m : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k => m rs.1.1 rs.1.2) :=
      (measurable_pi_apply rs.1.2).comp (measurable_pi_apply rs.1.1)
    exact h2.comp (h1.comp measurable_subtype_coe)
  · rw [hs.range_eq]; exact MeasurableSet.univ
  · refine Measurable.subtype_mk ?_
    refine measurable_comap_iff.2 ?_
    refine Measurable.of_eval fun r => Measurable.of_eval fun s => ?_
    show Measurable fun e : {rs : (n ⊕ Fin c) × (n ⊕ Fin c) // lev p rs.1 < lev p rs.2} → k => mkN (k := k) p e r s
    by_cases h : lev p r < lev p s
    · simp only [mkN, Matrix.of_apply, dif_pos h]; exact measurable_pi_apply _
    · simp only [mkN, Matrix.of_apply, dif_neg h]; exact measurable_const
  · intro g
    ext r s
    show mkN (k := k) p (fun rs => (g : GL (n ⊕ Fin c) k).val rs.1.1 rs.1.2) r s = _
    by_cases h : lev p r < lev p s
    · simp [mkN, h]
    · simp only [mkN, Matrix.of_apply, dif_neg h]
      exact (mem_N_iff.1 g.2 r s (not_lt.1 h)).symm

end meas

variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]


end GlobalTheory.RootEx.Model
end
end

