module

public import Mathlib
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.ExistsDvdQKPowSubOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027

@[expose] public section

noncomputable section

open ReciprocityTheory.DiscreteGroups.LocalClassField Matrix
open scoped TensorProduct Classical

namespace GlobalTheory.LKRes

section Generic

variable {G : Type} [Group G]

end Generic

variable (p : ℕ) [Fact p.Prime]

abbrev Q0 : IntermediateField ℚ_[p] (PadicAlgCl p) := ⊥

abbrev Qr (r : ℕ) : IntermediateField ℚ_[p] (PadicAlgCl p) := Kn p (Q0 p) r

def frobQ (r : ℕ) : Qr p r →ₐ[ℚ_[p]] Qr p r :=
  { GlobalTheory.LKLoc.frobR p (Q0 p) r with
    commutes' := fun c => Subtype.ext (((frobK p (Q0 p)).restrictScalars ℚ_[p]).commutes c) }

variable (K : IntermediateField ℚ_[p] (PadicAlgCl p))

def KQ (r : ℕ) : Type := K ⊗[ℚ_[p]] Qr p r

instance (r : ℕ) : CommRing (KQ p K r) := inferInstanceAs (CommRing (K ⊗[ℚ_[p]] Qr p r))

instance (r : ℕ) : Algebra ℚ_[p] (KQ p K r) := inferInstanceAs (Algebra ℚ_[p] (K ⊗[ℚ_[p]] Qr p r))

instance (r : ℕ) : TopologicalSpace (KQ p K r) := moduleTopology ℚ_[p] (KQ p K r)

def inclK (r : ℕ) : K →ₐ[ℚ_[p]] KQ p K r := Algebra.TensorProduct.includeLeft

def inclQ (r : ℕ) : Qr p r →ₐ[ℚ_[p]] KQ p K r := Algebra.TensorProduct.includeRight

def sigKQ (r : ℕ) : KQ p K r →ₐ[ℚ_[p]] KQ p K r :=
  Algebra.TensorProduct.map (AlgHom.id ℚ_[p] K) (frobQ p r)

def intKQ (r : ℕ) : Subring (KQ p K r) :=
  Subring.closure (Set.range (fun a : GlobalTheory.LKLoc.intK p K => inclK p K r a) ∪
    Set.range (fun b : GlobalTheory.LKLoc.intR p (Q0 p) r => inclQ p K r b))

def sigRes (n r : ℕ) : GL (Fin n) (KQ p K r) →* GL (Fin n) (KQ p K r) :=
  GeneralLinearGroup.map (sigKQ p K r).toRingHom

def Kres (n r : ℕ) : Subgroup (GL (Fin n) (KQ p K r)) :=
  (GeneralLinearGroup.map (intKQ p K r).subtype).range

def nrmRes (n r : ℕ) (δ : GL (Fin n) (KQ p K r)) : GL (Fin n) (KQ p K r) :=
  (List.map (fun i => (⇑(sigRes p K n r))^[i] δ) (List.range r)).prod

abbrev GHT (m n r : ℕ) (Kw : Fin m → IntermediateField ℚ_[p] (PadicAlgCl p)) : Type :=
  GL (Fin 1) (Qr p r) × ((i : Fin m) → GL (Fin n) (KQ p (Kw i) r))

def sigHT (m n r : ℕ) (Kw : Fin m → IntermediateField ℚ_[p] (PadicAlgCl p)) : GHT p m n r Kw →* GHT p m n r Kw :=
  (GlobalTheory.LKLoc.sig p (Q0 p) 1 r).prodMap (Pi.monoidHom fun i => (sigRes p (Kw i) n r).comp (Pi.evalMonoidHom _ i))

def KHT (m n r : ℕ) (Kw : Fin m → IntermediateField ℚ_[p] (PadicAlgCl p)) : Subgroup (GHT p m n r Kw) :=
  (GlobalTheory.LKLoc.Kint p (Q0 p) 1 r).prod (Subgroup.pi Set.univ fun i => Kres p (Kw i) n r)

theorem sigKQ_apply_inclK (r : ℕ) (a : K) : sigKQ p K r (inclK p K r a) = inclK p K r a := by
  show Algebra.TensorProduct.map (AlgHom.id ℚ_[p] K) (frobQ p r) (a ⊗ₜ[ℚ_[p]] (1 : Qr p r)) =
    a ⊗ₜ[ℚ_[p]] (1 : Qr p r)
  rw [Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply]

theorem sigKQ_apply_inclQ (r : ℕ) (b : Qr p r) : sigKQ p K r (inclQ p K r b) = inclQ p K r (frobQ p r b) := by
  show Algebra.TensorProduct.map (AlgHom.id ℚ_[p] K) (frobQ p r) ((1 : K) ⊗ₜ[ℚ_[p]] b) =
    (1 : K) ⊗ₜ[ℚ_[p]] (frobQ p r b)
  rw [Algebra.TensorProduct.map_tmul, map_one]

theorem frobQ_degree_one : frobQ p 1 = AlgHom.id ℚ_[p] (Qr p 1) := by
  have hK : FiniteDimensional ℚ_[p] (Q0 p) := by
    infer_instance
  have hle : Q0 p ≤ Qr p 1 := bot_le
  have hdeg : degLK p (Q0 p) (Kn p (Q0 p) 1) = 1 := degLK_Kn hK one_pos
  rw [degLK_eq_finrank (h := hle)] at hdeg
  have hbot := IntermediateField.finrank_eq_one_iff.1 hdeg
  refine AlgHom.ext fun x => Subtype.ext ?_
  have hx : (x : PadicAlgCl p) ∈ Q0 p := by
    have h1 : (x : PadicAlgCl p) ∈ IntermediateField.extendScalars hle := by
      exact x.2
    rw [hbot] at h1
    obtain ⟨y, hy⟩ := IntermediateField.mem_bot.1 h1
    rw [← hy]
    exact y.2
  exact (frobK p (Q0 p)).commutes ⟨_, hx⟩

theorem sigRes_degree_one (n : ℕ) : sigRes p K n 1 = MonoidHom.id _ := by
  have h1 : sigKQ p K 1 = AlgHom.id ℚ_[p] (KQ p K 1) := by
    unfold sigKQ
    rw [frobQ_degree_one]
    exact Algebra.TensorProduct.map_id
  refine MonoidHom.ext fun g => Matrix.GeneralLinearGroup.ext fun i j => ?_
  show sigKQ p K 1 ((g : Matrix (Fin n) (Fin n) (KQ p K 1)) i j) = (g : Matrix (Fin n) (Fin n) (KQ p K 1)) i j
  rw [h1]
  rfl

private lemma gl_fin_one_mul_comm {R : Type} [CommRing R] (a b : GL (Fin 1) R) : a * b = b * a := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  fin_cases i
  fin_cases j
  simp [Matrix.mul_apply, mul_comm]

theorem normal_of_gl_one {R : Type} [CommRing R] (H : Subgroup (GL (Fin 1) R)) : H.Normal :=
  ⟨fun n hn g => by
    rw [gl_fin_one_mul_comm g n, mul_inv_cancel_right]
    exact hn⟩

end GlobalTheory.LKRes
