module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0269
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DetCharacterMemPrincipalCongruenceFixedVectors
section
noncomputable section

namespace GlobalTheory.SerSys

open Polynomial GlobalTheory.GLq GlobalTheory.GLp Formalism.BasicNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders
open scoped Classical

structure Sys (g : ℕ) [Fact g.Prime] where
  e : ∀ n : ℕ, (ZMod g)[X] → MonoidAlgebra ℂ (Gn g n)
  idem : ∀ n f, e n f * e n f = e n f
  central : ∀ n f a, e n f * a = a * e n f
  orth : ∀ n f f', f ≠ f' → e n f * e n f' = 0
  label : ∀ n f, e n f ≠ 0 → f.Monic ∧ f.natDegree = n ∧ f.coeff 0 ≠ 0
  sum : ∀ n, ∃ T : Finset (ZMod g)[X], ∑ f ∈ T, e n f = 1

  mul : ∀ (a b n : ℕ), n = a + b → ∀ (f f' : (ZMod g)[X]) (V : Type) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (Gn g n) V) (v : V),
    (∀ u : Gn g n, InPar a (u : Mt g n) → tl a (u : Mt g n) = 1 → br a b (u : Mt g n) = 1 → ρ u v = v) →
    ∑ x : Gn g a, (e a f).coeff x • ρ (blk a b n x 1) v = v →
    ∑ y : Gn g b, (e b f').coeff y • ρ (blk a b n 1 y) v = v →
    ρ.asAlgebraHom (e n (f * f')) v = v

variable {g : ℕ} [Fact g.Prime]

def Has (S : Sys g) {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) ℚ_[g]) V)
    (f : (ZMod g)[X]) : Prop :=
  ∃ v ∈ fixK1 π, actK π (S.e n f) v ≠ 0

def CharIn (S : Sys g) (χ : (ZMod g)ˣ →* ℂˣ) (b : ℕ) (h : (ZMod g)[X]) : Prop :=
  ∑ y : Gn g b, (S.e b h).coeff y * ((χ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ) ≠ 0

local instance factTypePrime (D : D7) (k : Fin 2) : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩

def IneUnr (D : D7) : Prop :=
  ∀ (w : PlE D.host) (a χ : D.naut.LP w), D.naut.lpDim χ = 1 → D.naut.unr χ →
    ∀ s ∈ ReciprocityTheory.Gal.Ine (F := D.host.E) (D.nd.plOm.1 w), D.naut.inePol (D.naut.lpChar a χ) s = D.naut.inePol a s

def LocType (D : D7) (S : ∀ k, Sys (D.host.g k)) : Prop :=
  ∀ (i : D.nd.Loc) (P : D.naut.AV i) (k : Fin 2) (v : D.nd.PlG k),
    ∃ (π : Rep.{0} ℂ (GL (Fin D.R.nV) ℚ_[D.host.g k])) (χ : (ZMod (D.host.g k))ˣ →* ℂˣ) (c : ZMod (D.host.g k)),
      (∀ F ∈ D.naut.typeV i P, ∀ a ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ (Gn (D.host.g k) D.R.r)),
        D.ntypes.onMt (D.nd.mu i) (D.nd.j i) (atPlace D k v a) F ≠ 0 →
        ∃ u, IsParVec π.ρ D.R.r D.R.t χ u ∧ actTop π.ρ D.R.r D.R.t a u ≠ 0) ∧
      CharIn (S k) χ D.R.t ((X - C c) ^ D.R.t) ∧
      D.naut.inePol (D.naut.locG (D.naut.muC i) (D.naut.plGw k v)) (D.ntypes.tg k v) =
        X - C (D.ntypes.teichC k (algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k)) c)) ∧
      ∀ f, Has (S k) π.ρ f → D.naut.inePol (D.naut.locV i P (D.naut.plGw k v)) (D.ntypes.tg k v) =
        ((Formalism.CyclotomicNorms.rootsBar f).map fun x => X - C (D.ntypes.teichC k x)).prod

def Sys.IsOf (S : Sys g) (L : LabelDatum g) : Prop := ∀ n f, S.e n f = eSerC L n f

abbrev QRep (g : ℕ) [Fact g.Prime] (n : ℕ) : Type 1 := Rep.{0} ℂ (GL (Fin n) ℚ_[g])

def IrrSm {n : ℕ} (π : QRep g n) : Prop := IsIrrRep π.ρ ∧ GlobalTheory.PRep.IsSmooth π.ρ

def TamePart (μ : ℚ_[g]ˣ →* ℂˣ) (χ : (ZMod g)ˣ →* ℂˣ) : Prop :=
  ∀ u : ℤ_[g]ˣ, μ (Units.map (algebraMap ℤ_[g] ℚ_[g]).toMonoidHom u) =
    χ (Units.map (PadicInt.toZMod (p := g)).toMonoidHom u)

def ActsThrough {n : ℕ} (π : QRep g n) (r t : ℕ) (χ : (ZMod g)ˣ →* ℂˣ) {M : Type} [AddCommGroup M] [Module ℂ M]
    (W : Submodule ℂ M) (act : MonoidAlgebra ℂ (Gn g r) → Module.End ℂ M) : Prop :=
  ∃ (J : Type) (ι : W →ₗ[ℂ] (J → π)), Function.Injective ι ∧ (∀ F j, IsParVec π.ρ r t χ (ι F j)) ∧
    ∀ a ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ (Gn g r)), ∀ F : W,
      ∃ h : act a F ∈ W, ∀ j, ι ⟨act a F, h⟩ j = actTop π.ρ r t a (ι F j)

abbrev Corr (D : D7) : Type 1 :=
  ∀ (k : Fin 2) (v : D.nd.PlG k) (n : ℕ), QRep (D.host.g k) n → D.naut.LP (D.naut.plGw k v)

def SysTie (D : D7) (S : ∀ k, Sys (D.host.g k)) : Prop := ∀ k f, D.ntypes.eSer k f = (S k).e D.R.r f

def LabTie (D : D7) (L : ∀ k, LabelDatum (D.host.g k)) : Prop :=
  ∀ k, (L k).teich = D.ntypes.teichC k ∧ ∀ f, D.ntypes.eSer k f = eSerC (L k) D.R.r f

theorem eSerTie_iff (D : D7) : ESerTie D ↔ ∃ L, LabTie D L :=
  ⟨fun h => ⟨fun k => (h k).choose, fun k => (h k).choose_spec⟩, fun ⟨L, h⟩ k => ⟨L k, h k⟩⟩

theorem LabTie.sysTie {D : D7} {L : ∀ k, LabelDatum (D.host.g k)} {S : ∀ k, Sys (D.host.g k)} (h : LabTie D L)
    (hS : ∀ k, (S k).IsOf (L k)) : SysTie D S := fun k f => ((h k).2 f).trans (hS k _ f).symm

namespace Loc

open Matrix.GeneralLinearGroup

theorem alg_sum {G U : Type} [Group G] [Fintype G] [AddCommGroup U] [Module ℂ U] (ρ : Representation ℂ G U)
    (a : MonoidAlgebra ℂ G) (w : U) : ρ.asAlgebraHom a w = ∑ x, a.coeff x • ρ x w := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp [ha, hb, add_smul, Finset.sum_add_distrib]
  | single x c =>
    rw [Finset.sum_eq_single x]
    · simp
    · intro y _ hy
      simp [Finsupp.single_eq_of_ne hy]
    · simp

theorem det_blocks (a b : ℕ) (x : Gn g a) (y : Gn g b) : det (blk a b (a + b) x y) = det x * det y := by
  set M : Mt g (a + b) := fun i j : Fin (a + b) =>
    if (i : ℕ) < a ∧ (j : ℕ) < a then entN (x : Mt g a) i j
    else if a ≤ (i : ℕ) ∧ a ≤ (j : ℕ) then entN (y : Mt g b) (i - a) (j - a) else 0 with hM
  have h0 : InPar a M := fun i j hj hi => by rw [hM]; dsimp only; rw [if_neg (by omega), if_neg (by omega)]
  have h1 : tl a M = x := by
    ext i j
    have hi : (i : ℕ) < a + b := by omega
    have hj : (j : ℕ) < a + b := by omega
    simp [tl, entN, hM, hi, hj]
  have h2 : br a b M = y := by
    ext i j
    simp [br, entN, hM]
  have hd := LabelDet.det_inPar a b M h0
  rw [h1, h2] at hd
  apply Units.ext
  change ((det (toG M) : (ZMod g)ˣ) : ZMod g) = _
  rw [LabelDet.det_toG M (hd ▸ mul_ne_zero x.det_ne_zero y.det_ne_zero), hd]
  simp

theorem det_rad {a b : ℕ} {u : Gn g (a + b)} (h0 : InPar a (u : Mt g (a + b))) (h1 : tl a (u : Mt g (a + b)) = 1)
    (h2 : br a b (u : Mt g (a + b)) = 1) : det u = 1 := by
  rw [LabelDet.det_par a b u h0, h1, h2, LabelDet.toG_one, LabelDet.toG_one]; simp

def ev (χ : (ZMod g)ˣ →* ℂˣ) {n : ℕ} (a : MonoidAlgebra ℂ (Gn g n)) : ℂ := ∑ y : Gn g n, a.coeff y * ((χ (det y) : ℂˣ) : ℂ)

theorem alg_ev (χ : (ZMod g)ˣ →* ℂˣ) {n : ℕ} (a : MonoidAlgebra ℂ (Gn g n)) (v : ℂ) :
    (Model.chRep (χ.comp (det (n := Fin n)))).asAlgebraHom a v = ev χ a * v := by
  rw [alg_sum, ev, Finset.sum_mul]
  simp [mul_assoc]

theorem charIn_iff (S : Sys g) (χ : (ZMod g)ˣ →* ℂˣ) (b : ℕ) (h : (ZMod g)[X]) :
    CharIn S χ b h ↔ ev χ (S.e b h) = 1 := by
  change ev χ (S.e b h) ≠ 0 ↔ _
  refine ⟨fun h0 => ?_, fun h1 => h1 ▸ one_ne_zero⟩
  have := alg_ev χ (S.e b h * S.e b h) 1
  rw [map_mul, Module.End.mul_apply, alg_ev, alg_ev, S.idem] at this
  exact mul_left_cancel₀ h0 (by simpa using this)

theorem exists_charIn (S : Sys g) (χ : (ZMod g)ˣ →* ℂˣ) (b : ℕ) :
    ∃ h, CharIn S χ b h ∧ h.Monic ∧ h.natDegree = b ∧ h.coeff 0 ≠ 0 := by
  obtain ⟨T, hT⟩ := S.sum b
  have h1 := congrArg (fun a => (Model.chRep (χ.comp (det (n := Fin b)))).asAlgebraHom a 1) hT
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, LinearMap.sum_apply, alg_ev, map_one, Module.End.one_apply, mul_one] at h1
  obtain ⟨h, -, hh⟩ := Finset.exists_ne_zero_of_sum_ne_zero (h1 ▸ one_ne_zero)
  exact ⟨h, hh, S.label b h fun e => hh (by rw [e]; simp [ev])⟩

theorem charIn_mul (S : Sys g) (χ : (ZMod g)ˣ →* ℂˣ) {a b : ℕ} {f f' : (ZMod g)[X]} (h : CharIn S χ a f)
    (h' : CharIn S χ b f') : CharIn S χ (a + b) (f * f') := by
  rw [charIn_iff] at h h' ⊢
  have := S.mul a b _ rfl f f' ℂ (Model.chRep (χ.comp (det (n := Fin (a + b))))) 1
    (fun u h0 h1 h2 => by simp [det_rad h0 h1 h2]) (by simpa [det_blocks, ev] using h) (by simpa [det_blocks, ev] using h')
  rwa [alg_ev, mul_one] at this

theorem charIn_pow (S : Sys g) (χ : (ZMod g)ˣ →* ℂˣ) {h : (ZMod g)[X]} (h1 : CharIn S χ 1 h) (b : ℕ) :
    CharIn S χ b (h ^ b) := by
  induction b with
  | zero =>
    obtain ⟨f, hf, hm, hd, -⟩ := exists_charIn S χ 0
    rwa [hm.natDegree_eq_zero.1 hd, ← pow_zero h] at hf
  | succ b ih => exact pow_succ h b ▸ charIn_mul S χ ih h1

section Det

variable {μ : ℚ_[g]ˣ →* ℂˣ} {χ : (ZMod g)ˣ →* ℂˣ} (h : TamePart μ χ) {n : ℕ}
include h

theorem det_inc (k : GL (Fin n) ℤ_[g]) : μ (det (inc g n k)) = χ (det (red g n k)) := by
  have h1 : det (inc g n k) = Units.map (algebraMap ℤ_[g] ℚ_[g]).toMonoidHom (det k) := by
    ext; simp [inc, RingHom.map_det]
  have h2 : det (red g n k) = Units.map (PadicInt.toZMod (p := g)).toMonoidHom (det k) := by
    ext; simp [red, RingHom.map_det]
  rw [h1, h2, h]

theorem detCharacter_mem_principalCongruenceFixedVectors (v : ℂ) : v ∈ fixK1 (Model.detRep n μ) := by
  rw [Model.mem_principalCongruenceFixedVectors_iff]; intro k hk
  simp [Model.detRep, det_inc h, hk]

theorem det_lift (x : Gn g n) (v : ℂ) : Model.detRep n μ (lift g n x) v = χ (det x) * v := by
  obtain ⟨k, rfl⟩ := Model.red_surjective n x
  rw [Model.lift_red _ (detCharacter_mem_principalCongruenceFixedVectors h v)]
  simp [Model.detRep, det_inc h]

theorem actK_det (a : MonoidAlgebra ℂ (Gn g n)) (v : ℂ) : actK (Model.detRep n μ) a v = ev χ a * v := by
  simp [actK, LinearMap.sum_apply, det_lift h, ev, Finset.sum_mul, mul_assoc]

theorem has_det (S : Sys g) (f : (ZMod g)[X]) : Has S (Model.detRep n μ) f ↔ CharIn S χ n f := by
  refine ⟨fun ⟨v, _, hv⟩ => ?_, fun hf => ⟨1, detCharacter_mem_principalCongruenceFixedVectors h 1, by rwa [actK_det h, mul_one]⟩⟩
  rw [actK_det h] at hv
  exact left_ne_zero_of_mul hv

theorem irrSm_det : IrrSm (Rep.of (Model.detRep n μ)) := by
  refine ⟨Model.isIrrRep_chRep _, fun (v : ℂ) => ?_⟩
  let H : Subgroup (GL (Fin n) ℚ_[g]) :=
    { carrier := {x | Model.detRep n μ x v = v}
      one_mem' := by simp
      mul_mem' := fun {a b} ha hb => by
        change Model.detRep n μ (a * b) v = v
        rw [map_mul, Module.End.mul_apply, hb, ha]
      inv_mem' := fun {a} ha => by
        change Model.detRep n μ a⁻¹ v = v
        conv_lhs => rw [← show Model.detRep n μ a v = v from ha]
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
  have hc : Continuous fun x : GL (Fin n) ℚ_[g] => ‖x.val.det - 1‖ :=
    ((Units.continuous_val.matrix_det).sub continuous_const).norm
  refine H.isOpen_of_mem_nhds (g := 1) (Filter.mem_of_superset
    ((isOpen_lt hc continuous_const).mem_nhds (show ‖(1 : GL (Fin n) ℚ_[g]).val.det - 1‖ < 1 by simp)) fun x hx => ?_)
  have hx' : ‖x.val.det - 1‖ < 1 := hx
  have h1 : ‖x.val.det‖ = 1 := by
    have := Padic.norm_eq_of_norm_sub_lt_right (z1 := x.val.det) (z2 := 1) (by simpa using hx')
    simpa using this
  have e1 : det x = Units.map (algebraMap ℤ_[g] ℚ_[g]).toMonoidHom (PadicInt.mkUnits h1) := by
    ext; simp; rfl
  have e2 : Units.map (PadicInt.toZMod (p := g)).toMonoidHom (PadicInt.mkUnits h1) = 1 := by
    have : ((PadicInt.mkUnits h1 : ℤ_[g]ˣ) : ℤ_[g]) - 1 ∈ RingHom.ker (PadicInt.toZMod (p := g)) := by
      rw [PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits]
      exact hx'
    rw [RingHom.mem_ker, map_sub, map_one, sub_eq_zero] at this
    exact Units.ext this
  change Model.detRep n μ x v = v
  simp only [Model.detRep, Model.chRep_apply, MonoidHom.comp_apply]
  rw [e1, h, e2]; simp

end Det

theorem prod_linear (τ : Formalism.CyclotomicNorms.Fbar g →* ℂ) (c : ZMod g) :
    ((Formalism.CyclotomicNorms.rootsBar (X - C c)).map fun x => X - C (τ x)).prod =
      X - C (τ (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) c)) := by
  simp [Formalism.CyclotomicNorms.rootsBar]

end Loc

theorem ActsThrough.exists_parVec {n r t : ℕ} {π : QRep g n} {χ : (ZMod g)ˣ →* ℂˣ} {M : Type} [AddCommGroup M] [Module ℂ M]
    {W : Submodule ℂ M} {act : MonoidAlgebra ℂ (Gn g r) → Module.End ℂ M} (H : ActsThrough π r t χ W act) {F : M}
    (hF : F ∈ W) {a : MonoidAlgebra ℂ (Gn g r)} (ha : a ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ (Gn g r)))
    (h0 : act a F ≠ 0) : ∃ u, IsParVec π.ρ r t χ u ∧ actTop π.ρ r t a u ≠ 0 := by
  obtain ⟨J, ι, hi, hp, he⟩ := H
  obtain ⟨hm, hj⟩ := he a ha ⟨F, hF⟩
  obtain ⟨j, h1⟩ := Function.ne_iff.1 ((map_ne_zero_iff ι hi).2 (fun e => h0 (congrArg Subtype.val e) : (⟨_, hm⟩ : W) ≠ 0))
  exact ⟨_, hp _ j, hj j ▸ h1⟩

end GlobalTheory.SerSys
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisExportOfMatrixDetBounds
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen
open scoped ENNReal TensorProduct

namespace GlobalTheory.TwSys.Test

section Ord
variable (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

end Ord

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}



end GlobalTheory.TwSys.Test

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.H1MapSubgroup
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys

namespace GlobalTheory.SelFun

def Tors (Λ : Type) [CommRing Λ] [IsLocalRing Λ] (B : Type) [AddCommGroup B] [Module Λ B] : Prop :=
  ∀ b : B, ∃ n : ℕ, ∀ x ∈ IsLocalRing.maximalIdeal Λ ^ n, x • b = 0

section Maps

variable {Γ O Λ : Type} [Group Γ] [CommRing O] [CommRing Λ] [Algebra O Λ] {r : ℕ} (ρ : Γ →* GL (Fin r) O) (κ : Γ →* Λˣ)
  {B B' : Type} [AddCommGroup B] [Module Λ B] [AddCommGroup B'] [Module Λ B']

theorem repOn_map (f : B →ₗ[Λ] B') (g : Γ) (m : Fin r → B) :
    f.compLeft (Fin r) (repOn ρ κ B g m) = repOn ρ κ B' g (f.compLeft (Fin r) m) := by
  funext a
  set_option synthInstance.maxHeartbeats 100000 in
    simp [repOn, matAct, map_sum, Finset.smul_sum]

variable [TopologicalSpace Γ] [TopologicalSpace B] [DiscreteTopology B] [TopologicalSpace B'] [DiscreteTopology B']

def h1Map (f : B →ₗ[Λ] B') : H1 (repOn ρ κ B) →ₗ[Λ] H1 (repOn ρ κ B') :=
  mapH1 _ _ (f.compLeft (Fin r)) continuous_of_discreteTopology (repOn_map ρ κ f)

def h1MapSubgroup (U : Subgroup Γ) (f : B →ₗ[Λ] B') :
    H1 ((repOn ρ κ B).comp U.subtype) →ₗ[Λ] H1 ((repOn ρ κ B').comp U.subtype) :=
  mapH1 _ _ (f.compLeft (Fin r)) continuous_of_discreteTopology (fun g m => repOn_map ρ κ f g.1 m)

end Maps

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} (bkP : BKPh X)
  (i : X.Tw) (s : X.Sig i) {Λ : Type} [CommRing Λ] [IsLocalRing Λ] [Algebra (X.O0 i) Λ] (κ : GE N →* Λˣ)
  (Q : Finset (PlE D.host))

def Setup : Prop :=
  GalHyp bkP i s ∧ IsLocalHom (algebraMap (X.O0 i) Λ) ∧ Module.Finite (X.O0 i) Λ ∧
    IsOpen (κ.ker : Set (GE N)) ∧ (∀ g, ∃ n : ℕ, κ g ^ (X.l i ^ n) = 1) ∧ TrivAbove κ (X.l i) ∧
    (∀ v ∈ Q, v ∉ placesOver D.host.E (X.l i)) ∧
    ∀ v, v ∉ Q → ∀ A : ValuationSubring N.Om, IsPlaceOver A v → ∀ σ ∈ Ine (F := D.host.E) A, κ σ = 1

def SelMaps : Prop :=
  ∀ (B B' : Type) [AddCommGroup B] [Module Λ B] [TopologicalSpace B] [DiscreteTopology B]
    [AddCommGroup B'] [Module Λ B'] [TopologicalSpace B'] [DiscreteTopology B'] (f : B →ₗ[Λ] B'),
    (selOn bkP i (Tgl i s) κ B Q).map (h1Map (Tgl i s) κ f) ≤ selOn bkP i (Tgl i s) κ B' Q

def NoInv : Prop :=
  ∀ (B : Type) [AddCommGroup B] [Module Λ B] [TopologicalSpace B] [DiscreteTopology B], Tors Λ B →
    H0 (repOn (Tgl i s) κ B) = ⊥

def LocSat : Prop :=
  ∀ v ∈ placesOver D.host.E (X.l i),
  ∀ (B' B : Type) [AddCommGroup B'] [Module Λ B'] [TopologicalSpace B'] [DiscreteTopology B']
    [AddCommGroup B] [Module Λ B] [TopologicalSpace B] [DiscreteTopology B], Tors Λ B →
    ∀ f : B' →ₗ[Λ] B, Function.Injective f → ∀ y : H1 ((repOn (Tgl i s) κ B').comp (DecV N v).subtype),
      h1MapSubgroup (Tgl i s) κ (DecV N v) f y ∈ bkOn bkP i (Tgl i s) κ B v → y ∈ bkOn bkP i (Tgl i s) κ B' v

def SelLeft : Prop :=
  ∀ (B' B B'' : Type) [AddCommGroup B'] [Module Λ B'] [TopologicalSpace B'] [DiscreteTopology B']
    [AddCommGroup B] [Module Λ B] [TopologicalSpace B] [DiscreteTopology B]
    [AddCommGroup B''] [Module Λ B''] [TopologicalSpace B''] [DiscreteTopology B''], Tors Λ B → Tors Λ B'' →
    ∀ (f : B' →ₗ[Λ] B) (g : B →ₗ[Λ] B''), Function.Injective f → Function.Exact f g →
      Function.Injective (h1Map (Tgl i s) κ f) ∧
      ∀ y ∈ selOn bkP i (Tgl i s) κ B Q, h1Map (Tgl i s) κ g y = 0 →
        ∃ x ∈ selOn bkP i (Tgl i s) κ B' Q, h1Map (Tgl i s) κ f x = y

def SelColim : Prop :=
  ∀ (B : Type) [AddCommGroup B] [Module Λ B] [TopologicalSpace B] [DiscreteTopology B], Tors Λ B →
    ∀ y ∈ selOn bkP i (Tgl i s) κ B Q, ∃ B' : Submodule Λ B, B'.FG ∧
      ∃ x ∈ selOn bkP i (Tgl i s) κ B' Q, h1Map (Tgl i s) κ B'.subtype x = y

def LocCount : Prop :=
  ∀ (K : Type) [AddCommGroup K] [Module Λ K] [TopologicalSpace K] [DiscreteTopology K], IsSimpleModule Λ K →
    ∏ᶠ v ∈ placesOver D.host.E (X.l i), Nat.card (bkOn bkP i (Tgl i s) κ K v) =
      (∏ᶠ v ∈ placesOver D.host.E (X.l i), Nat.card (H0 ((repOn (Tgl i s) κ K).comp (DecV N v).subtype))) *
        Nat.card K ^ (D.R.f * D.R.r)

def SelObs : Prop :=
  ∀ (K B B'' : Type) [AddCommGroup K] [Module Λ K] [TopologicalSpace K] [DiscreteTopology K]
    [AddCommGroup B] [Module Λ B] [TopologicalSpace B] [DiscreteTopology B]
    [AddCommGroup B''] [Module Λ B''] [TopologicalSpace B''] [DiscreteTopology B''], IsSimpleModule Λ K → Tors Λ B →
    ∀ (f : K →ₗ[Λ] B) (g : B →ₗ[Λ] B''), Function.Injective f → Function.Exact f g → Function.Surjective g →
      Finite (selOn bkP i (Tgl i s) κ K Q) ∧
      Finite (↥(selOn bkP i (Tgl i s) κ B'' Q) ⧸ ((selOn bkP i (Tgl i s) κ B Q).map (h1Map (Tgl i s) κ g)).comap
        (selOn bkP i (Tgl i s) κ B'' Q).subtype) ∧
      Nat.card (↥(selOn bkP i (Tgl i s) κ B'' Q) ⧸ ((selOn bkP i (Tgl i s) κ B Q).map (h1Map (Tgl i s) κ g)).comap
        (selOn bkP i (Tgl i s) κ B'' Q).subtype) ≤ Nat.card (selOn bkP i (Tgl i s) κ K Q)


open CategoryTheory in
def KernelRep : Prop :=
  ∀ (Λ : Type) [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [IsAdicComplete (IsLocalRing.maximalIdeal Λ) Λ]
    [Finite (IsLocalRing.ResidueField Λ)] (F : ModuleCat.{0} Λ ⥤ ModuleCat.{0} Λ) [F.Additive] [F.Linear Λ],
    (∀ (B' B B'' : ModuleCat.{0} Λ), Tors Λ B → Tors Λ B'' → ∀ (f : B' ⟶ B) (g : B ⟶ B''), Function.Injective f.hom →
      Function.Exact f.hom g.hom → Function.Injective (F.map f).hom ∧ Function.Exact (F.map f).hom (F.map g).hom) →
    (∀ B : ModuleCat.{0} Λ, Tors Λ B → ∀ y : F.obj B, ∃ B' : Submodule Λ B, B'.FG ∧
      y ∈ LinearMap.range (F.map (ModuleCat.ofHom B'.subtype)).hom) →
    (∀ (K B B'' : ModuleCat.{0} Λ), IsSimpleModule Λ K → Tors Λ B → ∀ (f : K ⟶ B) (g : B ⟶ B''),
      Function.Injective f.hom → Function.Exact f.hom g.hom → Function.Surjective g.hom →
      Finite (F.obj K) ∧ Finite (F.obj B'' ⧸ LinearMap.range (F.map g).hom) ∧
        Nat.card (F.obj B'' ⧸ LinearMap.range (F.map g).hom) ≤ Nat.card (F.obj K)) →
    ∃ (a : ℕ) (Φ : Matrix (Fin a) (Fin a) Λ), (∀ b c, ¬ IsUnit (Φ b c)) ∧
      ∃ e : ∀ B : ModuleCat.{0} Λ, Tors Λ B → (↥(LinearMap.ker (matAct (M := B) Φ)) ≃ₗ[Λ] F.obj B),
        ∀ (B B' : ModuleCat.{0} Λ) (hB : Tors Λ B) (hB' : Tors Λ B') (f : B ⟶ B')
          (x : ↥(LinearMap.ker (matAct (M := B) Φ))) (x' : ↥(LinearMap.ker (matAct (M := B') Φ))),
          (∀ c, x'.1 c = f.hom (x.1 c)) → e B' hB' x' = (F.map f).hom (e B hB x)

end GlobalTheory.SelFun
end
end

