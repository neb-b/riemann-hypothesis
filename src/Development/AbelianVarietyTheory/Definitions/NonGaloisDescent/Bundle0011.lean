module

public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.PadicIntGLSmulMemPrincipalCongruenceFixed
section
noncomputable section

namespace GlobalTheory.GLp.Model

open Polynomial GlobalTheory.GLq GlobalTheory.GLp
open scoped Classical

variable {g : ℕ} [Fact g.Prime]

theorem red_surjective (n : ℕ) : Function.Surjective (red g n) := by
  intro x
  have hs : Function.Surjective (PadicInt.toZMod (p := g)) := ZMod.ringHom_surjective _
  let M : Matrix (Fin n) (Fin n) ℤ_[g] := fun i j => Function.surjInv hs ((x : Mt g n) i j)
  have hM : (PadicInt.toZMod (p := g)).mapMatrix M = (x : Mt g n) := by
    ext i j; exact Function.surjInv_eq hs _
  have hd : IsUnit M.det := by
    by_contra h
    have h1 : M.det ∈ RingHom.ker (PadicInt.toZMod (p := g)) := by
      rw [PadicInt.ker_toZMod]; exact h
    rw [RingHom.mem_ker, RingHom.map_det, hM] at h1
    exact (Matrix.isUnit_iff_isUnit_det _ |>.1 x.isUnit).ne_zero h1
  refine ⟨((Matrix.isUnit_iff_isUnit_det M).2 hd).unit, ?_⟩
  ext i j
  exact congrFun (congrFun hM i) j

variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

theorem mem_principalCongruenceFixedVectors_iff (π : Representation ℂ (GL (Fin n) ℚ_[g]) V) (v : V) :
    v ∈ fixK1 π ↔ ∀ k, red g n k = 1 → π (inc g n k) v = v := by
  simp [fixK1, Submodule.mem_iInf, sub_eq_zero, MonoidHom.mem_ker]

theorem lift_red (π : Representation ℂ (GL (Fin n) ℚ_[g]) V) {v : V} (hv : v ∈ fixK1 π)
    (k : GL (Fin n) ℤ_[g]) : π (lift g n (red g n k)) v = π (inc g n k) v := by
  have h := Function.invFun_eq (f := red g n) ⟨k, rfl⟩
  have h2 := (mem_principalCongruenceFixedVectors_iff π v).1 hv (k⁻¹ * Function.invFun (red g n) (red g n k)) (by simp [h])
  have : lift g n (red g n k) = inc g n k * inc g n (k⁻¹ * Function.invFun (red g n) (red g n k)) := by
    simp [lift]
  rw [this, map_mul, Module.End.mul_apply, h2]

theorem isIrrRep_iff {G : Type} [Group G] (π : Representation ℂ G V) : IsIrrRep π ↔ π.IsIrreducible := by
  constructor
  · rintro ⟨hn, h⟩
    haveI : Nontrivial (Subrepresentation π) := ⟨⊥, ⊤, fun e => by
      have : (⊥ : Submodule ℂ V) = ⊤ := congrArg Subrepresentation.toSubmodule e
      exact bot_ne_top this⟩
    refine ⟨fun W => ?_⟩
    rcases h W.toSubmodule (fun x v hv => W.apply_mem_toSubmodule x hv) with e | e
    · left; exact Subrepresentation.toSubmodule_injective e
    · right; exact Subrepresentation.toSubmodule_injective e
  · intro h
    refine ⟨?_, fun W hW => ?_⟩
    · by_contra hn
      rw [not_nontrivial_iff_subsingleton] at hn
      have : (⊥ : Subrepresentation π) = ⊤ := Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _)
      exact bot_ne_top this
    · rcases eq_bot_or_eq_top (⟨W, fun x v hv => hW x v hv⟩ : Subrepresentation π) with e | e
      · left; exact congrArg Subrepresentation.toSubmodule e
      · right; exact congrArg Subrepresentation.toSubmodule e

def chRep {G : Type} [Group G] (φ : G →* ℂˣ) : Representation ℂ G ℂ where
  toFun x := (φ x : ℂ) • LinearMap.id
  map_one' := by ext; simp
  map_mul' x y := by ext; simp [mul_comm]

@[simp] theorem chRep_apply {G : Type} [Group G] (φ : G →* ℂˣ) (x : G) (v : ℂ) : chRep φ x v = φ x * v := by
  simp [chRep]

theorem isIrrRep_chRep {G : Type} [Group G] (φ : G →* ℂˣ) : IsIrrRep (chRep φ) :=
  ⟨inferInstance, fun W _ => eq_bot_or_eq_top W⟩

def detRep (n : ℕ) (μ : ℚ_[g]ˣ →* ℂˣ) : Representation ℂ (GL (Fin n) ℚ_[g]) ℂ :=
  chRep (μ.comp Matrix.GeneralLinearGroup.det)

theorem exists_gen (L : LabelDatum g) : ∃ u : (ZMod g)ˣ, algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) u = L.gen 1 ∧
    orderOf u = g - 1 := by
  have hp : g.Prime := Fact.out
  have ho := L.gen_order 1 one_pos
  rw [pow_one] at ho
  have h1 : L.gen 1 ^ (g - 1) = 1 := by rw [← ho]; exact pow_orderOf_eq_one _
  have hpos : 0 < g - 1 := by have := hp.two_le; omega
  have h2 : L.gen 1 ^ g = L.gen 1 := by
    have : L.gen 1 ^ g = L.gen 1 ^ (g - 1 + 1) := by congr 1; omega
    rw [this, pow_succ, h1, one_mul]
  obtain ⟨c, hc⟩ : ∃ c : ZMod g, algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) c = L.gen 1 := by
    obtain ⟨m, hm⟩ := (mem_bot_iff_intCast g (Formalism.CyclotomicNorms.Fbar g)).1
      ((Subfield.mem_bot_iff_pow_eq_self (Formalism.CyclotomicNorms.Fbar g) g).2 h2)
    exact ⟨m, by simpa using hm⟩
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [← hc] at h1; simp [hpos.ne'] at h1
  refine ⟨Units.mk0 c hc0, hc, ?_⟩
  rw [← ho, ← hc, ← orderOf_units, Units.val_mk0]
  exact (orderOf_injective (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g)).toMonoidHom (algebraMap (ZMod g) _).injective c).symm

theorem isCharLab_exists (L : LabelDatum g) (χ : (ZMod g)ˣ →* ℂˣ) : ∃ c, IsCharLab L χ c := by
  obtain ⟨u, hu, ho⟩ := exists_gen L
  have hpos : 0 < g - 1 := by have := (Fact.out : g.Prime).two_le; omega
  haveI : NeZero (g - 1) := ⟨hpos.ne'⟩
  let T : (ZMod g)ˣ →* ℂ := L.teich.comp ((algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g)).toMonoidHom.comp (Units.coeHom _))
  have hT : Function.Injective T := fun a b e => Units.ext <| (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g)).injective
    (L.teich_inj _ _ (by simp) (by simp) e)
  have hprim : IsPrimitiveRoot (T u) (g - 1) := by
    rw [← ho, ← orderOf_injective T hT u]; exact IsPrimitiveRoot.orderOf _
  obtain ⟨m, -, hm⟩ := hprim.eq_pow_of_pow_eq_one (ξ := (χ u : ℂ)) (by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, ← ho, pow_orderOf_eq_one]; simp)
  refine ⟨(u ^ m : (ZMod g)ˣ), Units.ne_zero _, fun w hw => ?_⟩
  have : w = u := Units.ext ((algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g)).injective (hw.trans hu.symm))
  rw [this, ← hm, ← map_pow]; rfl

end GlobalTheory.GLp.Model
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon

def MatThm : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (_ : LocTied l P AI) (n : Type) [Fintype n] [DecidableEq n]
    (K : FinExt l) (r : ℕ) (ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)), IsRat r ρ → AdmDR P ρ → AdmSt P ρ

def FrameEx : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (_ : LocTied l P AI) (n : Type) [Fintype n] [DecidableEq n]
    (K : FinExt l) (r : ℕ) (ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)), IsRat r ρ →
    (AdmDR P ρ ↔ ∃ w : Fin r → n → ℤ, Framed P ρ w)

def TwistStep : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (_ : LocTied l P AI) (n : Type) [Fintype n] [DecidableEq n]
    (K : FinExt l) (r : ℕ) (ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)) (w : Fin r → n → ℤ), IsRat r ρ → Framed P ρ w →
    ∃ (K' : FinExt l) (r' : ℕ) (ρ' : ↥(GK K') →* GL n ↥(MaximalUnramifiedExtension l)) (w' : Fin r' → n → ℤ),
      IsRat r' ρ' ∧ Framed P ρ' w' ∧ ∑ m, ∑ j, w' m j = 0 ∧ (AdmSt P ρ' → AdmSt P ρ)

def SenFinite : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (n : Type) [Fintype n] [DecidableEq n] (K : FinExt l) (ρ : ↥(GK K) →* GL n ℚ_[l]),
    (∀ i j, Continuous fun g => (ρ g : Matrix n n ℚ_[l]) i j) →
    ∀ M : GL n ℂ_[l], (∀ g : ↥(GK K), (ρ g : Matrix n n ℚ_[l]).map (algebraMap ℚ_[l] ℂ_[l]) *
      (M : Matrix n n ℂ_[l]).map (Formalism.Per.σC (g : GQ l)) = M) →
    (ρ '' (IK K : Set ↥(GK K))).Finite

def UnrStep : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (_ : LocTied l P AI) (n : Type) [Fintype n] [DecidableEq n]
    (K : FinExt l) (r : ℕ) (ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)), IsRat r ρ → (ρ '' (IK K : Set ↥(GK K))).Finite → AdmSt P ρ

def SenStep : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (_ : LocTied l P AI) (n : Type) [Fintype n] [DecidableEq n]
    (K : FinExt l) (r : ℕ) (ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)), IsRat r ρ → Framed P ρ (0 : Fin r → n → ℤ) → AdmSt P ρ

def Hyodo : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (_ : LocTied l P AI)
    (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V]
    [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V),
    (∀ v : V, Continuous fun g => ρ g v) → IsSst P ρ →
    ∀ c : ↥(GK K) → V, Continuous c → (∀ g h, c (g * h) = c g + ρ g (c h)) →
    (∃ b : V ⊗[ℚ_[l]] P.R.BdR, ∀ g, c g ⊗ₜ[ℚ_[l]] (1 : P.R.BdR) = actVdR (P.PD K) ρ g b - b) →
    ∃ b : V ⊗[ℚ_[l]] Bst P, ∀ g, c g ⊗ₜ[ℚ_[l]] (1 : Bst P) = stRep P ρ g b - b

def ExtStep : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (_ : LocTied l P AI)
    (a b : Type) [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (K : FinExt l) (r : ℕ)
    (ρ : ↥(GK K) →* GL (a ⊕ b) ↥(MaximalUnramifiedExtension l)) (ρ₁ : ↥(GK K) →* GL a ↥(MaximalUnramifiedExtension l)) (ρ₂ : ↥(GK K) →* GL b ↥(MaximalUnramifiedExtension l))
    (c : ↥(GK K) → Matrix a b ↥(MaximalUnramifiedExtension l)), IsRat r ρ →
    (∀ g, (ρ g : Matrix (a ⊕ b) (a ⊕ b) ↥(MaximalUnramifiedExtension l)) = Matrix.fromBlocks (ρ₁ g : Matrix a a ↥(MaximalUnramifiedExtension l)) (c g) 0 (ρ₂ g : Matrix b b ↥(MaximalUnramifiedExtension l))) →
    AdmDR P ρ → AdmSt P ρ₁ → AdmSt P ρ₂ → AdmSt P ρ

def SubQuot : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (_ : LocTied l P AI)
    (a b : Type) [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (K : FinExt l) (r : ℕ)
    (ρ : ↥(GK K) →* GL (a ⊕ b) ↥(MaximalUnramifiedExtension l)) (ρ₁ : ↥(GK K) →* GL a ↥(MaximalUnramifiedExtension l)) (ρ₂ : ↥(GK K) →* GL b ↥(MaximalUnramifiedExtension l))
    (c : ↥(GK K) → Matrix a b ↥(MaximalUnramifiedExtension l)), IsRat r ρ →
    (∀ g, (ρ g : Matrix (a ⊕ b) (a ⊕ b) ↥(MaximalUnramifiedExtension l)) = Matrix.fromBlocks (ρ₁ g : Matrix a a ↥(MaximalUnramifiedExtension l)) (c g) 0 (ρ₂ g : Matrix b b ↥(MaximalUnramifiedExtension l))) →
    AdmDR P ρ → AdmDR P ρ₁ ∧ AdmDR P ρ₂

def RedStep : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (_ : LocTied l P AI) (n : Type) [Fintype n] [DecidableEq n]
    (K : FinExt l) (r : ℕ) (ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)), IsRat r ρ → AdmDR P ρ → Splits r ρ →
    (∀ (a : Type) [Fintype a] [DecidableEq a], Fintype.card a < Fintype.card n →
      ∀ ρ' : ↥(GK K) →* GL a ↥(MaximalUnramifiedExtension l), IsRat r ρ' → AdmDR P ρ' → AdmSt P ρ') → AdmSt P ρ

def ModStep : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (_ : LocTied l P AI) (n : Type) [Fintype n] [DecidableEq n]
    (K : FinExt l) (r : ℕ) (ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)) (w : Fin r → n → ℤ) (x y : Fin r × n), x ≠ y →
    IsRat r ρ → Framed P ρ w → ¬ Splits r ρ →
    ∃ ρ' : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l), IsRat r ρ' ∧ Framed P ρ' (fun m j => w m j + eps x y (m, j)) ∧
      (AdmSt P ρ' → AdmSt P ρ)

def FLAt (r : ℕ) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (_ : LocTied l P AI) (n : Type) [Fintype n] [DecidableEq n]
    (U : Fin r → GL n P.R.BdR) (x y : Fin r × n), x ≠ y → (∀ m, UnitM P (U m)) →
    (∀ c : n → ↥(MaximalUnramifiedExtension l), (∀ i, fr l r (c i) = c i) →
      ∑ i, kd P (c i) * (U x.1 : Matrix n n P.R.BdR) i x.2 ∈ Fil P 1 → c = 0) →
    ∃ A : GL n P.R.B, (∀ i j, P.φB^[r] ((A : Matrix n n P.R.B) i j) = (A : Matrix n n P.R.B) i j) ∧
      ∀ m : Fin r, ∃ W : GL n P.R.BdR, UnitM P W ∧ (A : Matrix n n P.R.B).map (ev P m) =
        (U m : Matrix n n P.R.BdR) * Matrix.diagonal (fun j => tz P (eps x y (m, j))) * (W : Matrix n n P.R.BdR)

def Ratio : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (h s : ℕ), s < h →
    ∀ ω ω' : P.R.B, Plus T ω → Plus T ω' → P.φB^[h] ω = (l : P.R.B) ^ s * ω → P.φB^[h] ω' = (l : P.R.B) ^ s * ω' →
    ω' ≠ 0 → P.φB ω * ω' = ω * P.φB ω' → ∃ c : ℚ_[l], ω = c • ω'

def Moore : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (h k : ℕ), k ≤ h →
    ∀ a : Fin k → P.R.B, (∀ j, Plus T (a j)) → (∀ j, P.φB^[h] (a j) = (l : P.R.B) * a j) →
    LinearIndependent ℚ_[l] a → (Matrix.of fun i j : Fin k => P.φB^[i] (a j)).det ≠ 0

def ExI : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (h : ℕ), 2 ≤ h →
    ∀ μ : Fin h → P.R.BdR, (∀ i, μ i ∈ Fil P 0) → (∃ i, μ i ∉ Fil P 1) →
    ∃ b : Fin h → P.R.B, (∀ j, Plus T (b j)) ∧ (∀ j, P.φB^[h] (b j) = (l : P.R.B) * b j) ∧
      LinearIndependent ℚ_[l] b ∧ ∀ j, ∑ i, μ i * ev P i (b j) ∈ Fil P 1

def ExII : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (h : ℕ), 2 ≤ h →
    ∀ lam : Fin h → P.R.BdR, (∀ j, lam j ∈ Fil P 0) →
    (∀ c : Fin h → ℚ_[l], ∑ j, c j • lam j ∈ Fil P 1 → c = 0) →
    ∃ a : Fin h → P.R.B, a ≠ 0 ∧ (∀ j, Plus T (a j)) ∧ (∀ j, P.φB^[h] (a j) = (l : P.R.B) * a j) ∧
      ∀ i : Fin h, ∑ j, lam j * ev P i (a j) ∈ Fil P 1

def WeilRes : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (n : Type) [Fintype n] [DecidableEq n]
    (K : FinExt l) (r : ℕ) (ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)), IsRat r ρ →
    ∃ (ρ₀ : ↥(GK K) →* GL (n × Fin r) ℚ_[l]) (p : GL (n × Fin r) ↥(MaximalUnramifiedExtension l)),
      (∀ i j, Continuous fun g => (ρ₀ g : Matrix (n × Fin r) (n × Fin r) ℚ_[l]) i j) ∧
      (∀ i j, fr l r ((p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) i j) = (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) i j) ∧
      ∀ g, (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) *
          (ρ₀ g : Matrix (n × Fin r) (n × Fin r) ℚ_[l]).map (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l)) =
        Matrix.blockDiagonal (fun m : Fin r => (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)).map (fr l m)) *
          (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l))

end GlobalTheory.PMon

end
end

