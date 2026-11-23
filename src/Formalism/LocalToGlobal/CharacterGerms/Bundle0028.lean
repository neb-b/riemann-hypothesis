module

public import Formalism.LocalToGlobal.CharacterGerms.Bundle0024
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0026
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0015
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0027
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0001
public import Formalism.LocalToGlobal.CharacterGerms.RowTiePOActSg

@[expose] public section

-- bundled from Formalism.LocalToGlobal.CharacterGerms.PderivSubGOff
section
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds.RF

open Formalism.IncomingBounds Formalism.L2.Pj MvPolynomial

section Chain

variable {C : Type} [Field C] {T Orb : Type} [Fintype Orb] {r : T → ℕ} {tau : Orb → ZMod 2 → T}
  {gm : Orb → ZMod 2 → Matrix (Fin 2) (Fin 2) C} {N n : ℕ} (plc : Fin N × Fin 2 ↪ Fin n)

theorem chain_aeval {σ τ : Type} [Fintype σ] (S : MvPolynomial σ C →ₐ[C] MvPolynomial τ C) (ℓ : τ) (p : MvPolynomial σ C) :
    pderiv ℓ (S p) = ∑ y, S (pderiv y p) * pderiv ℓ (S (X y)) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    simp [MvPolynomial.algHom_C, MvPolynomial.pderiv_C]
  | add p q hp hq =>
    simp only [map_add (f := _), hp, hq, add_mul, Finset.sum_add_distrib]
  | mul_X p i hp =>
    have key : ∀ y, S (pderiv y (p * X i)) = (if i = y then S p else 0) + S (X i) * S (pderiv y p) := by
      intro y
      rw [Derivation.leibniz, pderiv_X]
      by_cases h : i = y
      · subst h
        simp
      · simp [Pi.single_apply, h]
    conv_lhs => rw [map_mul S p (X i), Derivation.leibniz, hp]
    simp only [key, smul_eq_mul, add_mul, Finset.sum_add_distrib, ite_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, if_true, Finset.mul_sum, mul_assoc]
    try ring

theorem pderiv_subG_off {p : MvPolynomial (Fin N × WVO fun o (_ : Fin 2) => IIs r tau o) C} {ℓ : Letter T r n}
    (h : ∀ z, ℓ ≠ lam r tau plc z) : pderiv ℓ (subG r tau gm plc p) = 0 := by
  rw [chain_aeval]
  refine Finset.sum_eq_zero fun y _ => ?_
  have hX : pderiv ℓ (subG r tau gm plc (X y)) = 0 := by
    unfold subG
    set_option synthInstance.maxHeartbeats 100000 in
      rw [MvPolynomial.aeval_X, map_sum]
    refine Finset.sum_eq_zero fun col _ => ?_
    rw [Derivation.leibniz, MvPolynomial.pderiv_C, smul_zero, add_zero, MvPolynomial.pderiv_X]
    have hne : (⟨tau y.2.1 y.2.2.2.1, y.2.2.2.2, plc (y.1, col)⟩ : Letter T r n) ≠ ℓ := by
      intro heq
      apply h (((eW r tau N) y).1, col)
      rw [← heq]
      rfl
    simp [Pi.single_apply, hne]
  rw [hX, mul_zero]

private theorem lam_injective_of_tau_injective (inj : Function.Injective fun x : Orb × ZMod 2 => tau x.1 x.2)
    (z z' : AA r tau N × Fin 2) (h : lam r tau plc z = lam r tau plc z') : z = z' := by
  obtain ⟨⟨n1, o1, s1, i1⟩, c1⟩ := z
  obtain ⟨⟨n2, o2, s2, i2⟩, c2⟩ := z'
  injection h with h0 h3
  have h1 : tau o1 s1 = tau o2 s2 := h0
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (@inj (o1, s1) (o2, s2) h1)
  have h4 : (i1, plc (n1, c1)) = (i2, plc (n2, c2)) := eq_of_heq h3
  obtain ⟨rfl, h5⟩ := Prod.mk.inj h4
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (plc.injective h5)
  rfl

private theorem pderiv_lam_subG_X_eq_ite (inj : Function.Injective fun x : Orb × ZMod 2 => tau x.1 x.2)
    (α0 : AA r tau N) (col0 : Fin 2) (y : Fin N × WVO fun o (_ : Fin 2) => IIs r tau o) :
    pderiv (lam r tau plc (α0, col0)) (subG r tau gm plc (X y)) =
      if (eW r tau N y).1 = α0 then MvPolynomial.C (gm y.2.1 y.2.2.2.1 col0 y.2.2.1) else 0 := by
  unfold subG
  set_option synthInstance.maxHeartbeats 100000 in
    rw [MvPolynomial.aeval_X, map_sum]
  have key : ∀ col : Fin 2, pderiv (lam r tau plc (α0, col0))
      (MvPolynomial.C (gm y.2.1 y.2.2.2.1 col y.2.2.1) *
        MvPolynomial.X (⟨tau y.2.1 y.2.2.2.1, y.2.2.2.2, plc (y.1, col)⟩ : Letter T r n)) =
      if ((eW r tau N y).1, col) = (α0, col0) then MvPolynomial.C (gm y.2.1 y.2.2.2.1 col y.2.2.1) else 0 := by
    intro col
    rw [Derivation.leibniz, MvPolynomial.pderiv_C, smul_zero, add_zero, MvPolynomial.pderiv_X]
    have e1 : (⟨tau y.2.1 y.2.2.2.1, y.2.2.2.2, plc (y.1, col)⟩ : Letter T r n) =
        lam r tau plc ((eW r tau N y).1, col) := rfl
    rw [e1, Pi.single_apply]
    by_cases hz : ((eW r tau N y).1, col) = (α0, col0)
    · rw [if_pos (congrArg (lam r tau plc) hz), if_pos hz, smul_eq_mul, mul_one]
    · rw [if_neg (fun h' => hz (lam_injective_of_tau_injective plc inj _ _ h')), if_neg hz, smul_zero]
  simp only [key]
  by_cases ha : (eW r tau N y).1 = α0
  · simp [ha]
  · simp [ha]

theorem pderiv_subG_lam (inj : Function.Injective fun x : Orb × ZMod 2 => tau x.1 x.2) (α0 : AA r tau N) (col0 : Fin 2)
    (p : MvPolynomial (Fin N × WVO fun o (_ : Fin 2) => IIs r tau o) C) :
    pderiv (lam r tau plc (α0, col0)) (subG r tau gm plc p) =
      ∑ g, MvPolynomial.C (Gm r tau gm α0 col0 g) * subG r tau gm plc (pderiv ((eW r tau N).symm (α0, g)) p) := by
  rw [chain_aeval, ← (eW r tau N).symm.sum_comp, Fintype.sum_prod_type, Finset.sum_eq_single α0]
  · refine Finset.sum_congr rfl fun g _ => ?_
    rw [pderiv_lam_subG_X_eq_ite plc inj]
    simp only [Equiv.apply_symm_apply]
    first | rw [if_pos rfl] | skip
    exact mul_comm _ _
  · intro α _ hα
    refine Finset.sum_eq_zero fun g _ => ?_
    rw [pderiv_lam_subG_X_eq_ite plc inj]
    simp only [Equiv.apply_symm_apply]
    first | rw [if_neg hα] | simp [hα]
    first | exact mul_zero _ | simp
  · intro h
    exact absurd (Finset.mem_univ _) h

end Chain

end Formalism.L2.FormalSeriesBounds.RF
end
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.RowTiePAllSet
section
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds

variable {C : Type} [Field C]

namespace RawChart

variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ] (X : RawChart C d I κ)

def AllSet (V : VF C) (g : Fin 2) : Set (ℕ → I g ⊕ JJ I g → C) :=
  {L | ∃ (γ : κ → PowerSeries C) (lam : JJ I g → PowerSeries C), IsCv V γ ∧ IsCv V lam ∧
    (∀ i : κ, alongCv γ (X.lg i) = ∑ c : I g, X.u g c i • PowerSeries.mk (fun n => L n (Sum.inl c))) ∧
    ∀ q : JJ I g, PowerSeries.mk (fun n => L n (Sum.inr q)) =
      lam q - alongCv γ (X.sg (X.u (1 - g) q)) +
        ∑ c : I g, if X.ty g c = X.ty (1 - g) q then
          X.sg1 (X.u g c) (X.u (1 - g) q) • PowerSeries.mk (fun n => L n (Sum.inl c)) else 0}

end RawChart

end Formalism.L2.FormalSeriesBounds
end
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.RowTiePCEqDer
section
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds PartialDerivEval RowTiePCEq ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

variable {C : Type} [Field C]

section Defs

variable [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}

def FBChart.dF (Y : FBChart C V O dd) (v : Fin dd → C) (j : Fin dd) : PS C 1 dd :=
  ∑ i, MvPowerSeries.C (v i) * ev (n := 1) ![pt C dd 0, 0] (MvPowerSeries.pderiv (R := C) ((1 : Fin 2), i) (Y.B.G.F j))

def ExDerSt (Y : FBChart C V O dd) : Prop :=
  ∀ (v : Fin dd → C) (j : Fin dd),
    ∑ i, MvPowerSeries.C (v i) * MvPowerSeries.pderiv (R := C) ((0 : Fin 1), i) (Y.ex j) = ev (n := 1) ![Y.ex] (Y.dF v j)

def GermIIMSt (Y : FBChart C V O dd) : Prop :=
  ∀ v : Fin dd → C, (∀ i, V.Ge 0 (v i)) →
    IntS V ((∑ j : Fin dd, (∑ i : Fin dd, MvPowerSeries.C (v i) *
        ev (n := 2) ![pt C dd 0, 0] (MvPowerSeries.pderiv (R := C) ((1 : Fin 2), i) (Y.B.G.F j))) *
          MvPowerSeries.pderiv (R := C) ((0 : Fin 2), j) Y.h) + ev (n := 2) ![pt C dd 1] (Y.sgP v))

end Defs

namespace RowTiePCEqDer

variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)]

theorem dVar_eq {σ : Type} (w : σ) (F : MvPowerSeries σ C) : dVar w F = MvPowerSeries.pderiv (R := C) w F := by
  ext μ
  rw [MvPowerSeries.coeff_pderiv]
  show ((μ w + 1 : ℕ) : C) * MvPowerSeries.coeff (μ + Finsupp.single w 1) F = _
  push_cast
  ring

theorem pderiv_upG_same (g : Fin 2) (k : I g) (F : MvPowerSeries (I g) C) :
    MvPowerSeries.pderiv (R := C) (⟨g, k⟩ : WV I) (upG g F) = upG g (MvPowerSeries.pderiv (R := C) k F) := by
  unfold upG
  rw [Formalism.G.LogCR.pderiv_subst (fun _ => MvPowerSeries.constantCoeff_X _), Finset.sum_eq_single k]
  · rw [MvPowerSeries.pderiv_X_self, mul_one]
  · intro c _ hc
    rw [MvPowerSeries.pderiv_X_of_ne, mul_zero]
    intro h
    exact hc (eq_of_heq (Sigma.mk.inj h).2)
  · intro h
    exact absurd (Finset.mem_univ k) h

theorem pderiv_upG_ne (g g' : Fin 2) (h : g' ≠ g) (k : I g) (F : MvPowerSeries (I g') C) :
    MvPowerSeries.pderiv (R := C) (⟨g, k⟩ : WV I) (upG g' F) = 0 := by
  unfold upG
  rw [Formalism.G.LogCR.pderiv_subst (fun _ => MvPowerSeries.constantCoeff_X _)]
  refine Finset.sum_eq_zero fun c _ => ?_
  rw [MvPowerSeries.pderiv_X_of_ne, mul_zero]
  intro he
  exact h (Sigma.mk.inj he).1

end RowTiePCEqDer

namespace RowTiePCEqDer

variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)]
variable [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}

theorem pderiv_uncurry (f : PS C 1 dd) (i : Fin dd) :
    MvPowerSeries.pderiv (R := C) i (un1 f) = un1 (MvPowerSeries.pderiv (R := C) ((0 : Fin 1), i) f) := by
  rw [uncurry_eq_subst, Formalism.G.LogCR.pderiv_subst (fun _ => MvPowerSeries.constantCoeff_X _),
    Finset.sum_eq_single ((0 : Fin 1), i), uncurry_eq_subst]
  · rw [show (((0 : Fin 1), i) : Fin 1 × Fin dd).2 = i from rfl, MvPowerSeries.pderiv_X_self, mul_one]
  · intro q _ hq
    rw [MvPowerSeries.pderiv_X_of_ne, mul_zero]
    intro h
    exact hq (Prod.ext (Subsingleton.elim _ _) h)
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem uncurry_linear_combination (r : Fin dd → C) (f : Fin dd → PS C 1 dd) :
    un1 (∑ i, MvPowerSeries.C (r i) * f i) = ∑ i, MvPowerSeries.C (r i) * un1 (f i) := by
  simp only [uncurry_eq_subst]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← MvPowerSeries.coe_substAlgHom hasSubst_snd, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, MvPowerSeries.coe_substAlgHom, MvPowerSeries.subst_C]

theorem ev_pt_dF (Y : FBChart C V O dd) (v : Fin dd → C) (g' : Fin 2) (j : Fin dd) :
    ev (n := 2) ![pt C dd g'] (Y.dF v j) =
      ∑ i, MvPowerSeries.C (v i) * ev (n := 2) ![pt C dd g', 0] (MvPowerSeries.pderiv (R := C) ((1 : Fin 2), i) (Y.B.G.F j)) := by
  have hZ := z0_1 (pt C (n := 2) dd g') (z0_pt g')
  have hZ' : Z0 (![pt C dd 0, 0] : Fin 2 → Pt C 1 dd) := z0_p0 _ (z0_pt 0)
  unfold FBChart.dF
  rw [ev_sum hZ]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ev_mul hZ, Formalism.L2.FormalSeriesBounds.PartialDerivEval.ev_C, ev_ev hZ' hZ]
  congr 2
  funext k j'
  fin_cases k
  · exact ev_X hZ 0 j'
  · exact ev_zero hZ

theorem pderiv_lin {κ : Type} [Fintype κ] (X : RawChart C d I κ) (g : Fin 2) (k : I g) (i : κ) :
    MvPowerSeries.pderiv (R := C) k (∑ c : I g, X.u g c i • (MvPowerSeries.X c : MvPowerSeries (I g) C)) =
      MvPowerSeries.C (X.u g k i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.sum_eq_single k]
  · rw [Derivation.map_smul, MvPowerSeries.pderiv_X_self, MvPowerSeries.smul_eq_C_mul, mul_one]
  · intro c _ hc
    rw [Derivation.map_smul, MvPowerSeries.pderiv_X_of_ne hc, smul_zero]
  · intro h
    exact absurd (Finset.mem_univ k) h

end RowTiePCEqDer

namespace RowTiePCEqDer

variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)]

theorem subst_exp_eval_two {dd : ℕ} (X : RawChart C d I (Fin dd))
    (hE0 : ∀ q : Fin 2 × Fin dd, MvPowerSeries.constantCoeff (X.expPt q.1 q.2) = 0) (g' : Fin 2) (f : PS C 1 dd) :
    MvPowerSeries.subst (fun q : Fin 2 × Fin dd => X.expPt q.1 q.2) (ev (n := 2) ![pt C dd g'] f) =
      MvPowerSeries.subst (X.expPt g') (un1 f) := by
  have hS := MvPowerSeries.hasSubst_of_constantCoeff_zero hE0
  rw [eval_single_eq_subst, MvPowerSeries.subst_comp_subst_apply
    (MvPowerSeries.hasSubst_of_constantCoeff_zero (a := fun q : Fin 1 × Fin dd => pt C (n := 2) dd g' q.2)
      fun q => MvPowerSeries.constantCoeff_X _) hS,
    subst_singlePointUncurry (fun j => hE0 (g', j))]
  congr 1
  funext q
  rw [show (pt C (n := 2) dd g' q.2) = MvPowerSeries.X (g', q.2) from rfl, MvPowerSeries.subst_X hS]

end RowTiePCEqDer


end Formalism.L2.FormalSeriesBounds
end
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.RowTiePKeyEigB
section
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

namespace RowTiePKeyEig

open RowTiePE0 RowTiePKey RowTiePProj GmExArith

variable {C : Type} [Field C] {V : VF C} {O : Type} [CommRing O] {n d : ℕ} (K : KeyData C V O n d)

theorem em_iter (x : O) (a : ZMod d) (k : ℕ) : V.MM (K.em (a + k) x - K.em a x ^ V.l ^ k) := by
  induction k with
  | zero => simp [mm_zero]
  | succ k ih =>
    have h1 := K.em_frob (a + k) x
    have h2 := mm_pow_sub (K.em_int _ x) ((K.em_int a x).pow _) ih V.l
    have e : K.em (a + ((k + 1 : ℕ) : ZMod d)) x - K.em a x ^ V.l ^ (k + 1) =
        (K.em (a + k + 1) x - K.em (a + k) x ^ V.l) + (K.em (a + k) x ^ V.l - (K.em a x ^ V.l ^ k) ^ V.l) := by
      rw [← pow_mul, ← pow_succ, Nat.cast_succ, ← add_assoc]; ring
    rw [e]
    exact mm_add h1 h2

theorem em_cong (x : O) (a : ZMod d) : V.MM (K.em a (x ^ V.l ^ d - x)) := by
  have h := em_iter K x a d
  rw [ZMod.natCast_self, add_zero] at h
  rw [map_sub, map_pow]
  have := mm_neg h
  rwa [neg_sub] at this

theorem star_S (x : O) : (V.l : C)⁻¹ • ((K.P * K.ρ x) ^ V.l ^ d - K.P * K.ρ x) ∈ Acl K := by
  obtain ⟨y, hy⟩ := K.ε_ann (x ^ V.l ^ d - x) fun a => em_cong K x a
  have hl0 : (V.l : C) ≠ 0 := V.l_ne_zero
  have hq : V.l ^ d = (V.l ^ d - 1) + 1 := (Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr
    (pow_ne_zero _ V.l_prime.ne_zero))).symm
  have eM : (K.P * K.ρ x) ^ V.l ^ d - K.P * K.ρ x = K.P * (K.P * K.ρ (x ^ V.l ^ d - x)) := by
    rw [← Matrix.mul_assoc, P_idem, map_sub, Matrix.mul_sub, hq, S_pow, ← hq]
  rw [eM]
  refine ⟨fun k => K.ε ^ (V.l ^ k - 1) * y, ?_⟩
  have key : ∀ k : ℕ, K.P * K.ρ (K.ε ^ (V.l ^ k - 1) * y) =
      (V.l : C)⁻¹ • (K.ρ (K.ε ^ V.l ^ k) * (K.P * K.ρ (x ^ V.l ^ d - x))) := by
    intro k
    have hk : V.l ^ k ≠ 0 := pow_ne_zero _ V.l_prime.ne_zero
    have e1 : K.ε ^ V.l ^ k * (x ^ V.l ^ d - x) = (V.l : O) * (K.ε ^ (V.l ^ k - 1) * y) := by
      rw [← pow_sub_one_mul hk, mul_assoc, hy]; ring
    rw [← Matrix.mul_assoc, ← P_comm, Matrix.mul_assoc, ← map_mul, e1, ρ_natmul, Matrix.mul_smul, smul_smul,
      inv_mul_cancel₀ hl0, one_smul]
  have hseq : (fun k => K.P * K.ρ (K.ε ^ (V.l ^ k - 1) * y)) =
      fun k => (V.l : C)⁻¹ • (K.ρ (K.ε ^ V.l ^ k) * (K.P * K.ρ (x ^ V.l ^ d - x))) := funext key
  rw [hseq]
  exact MT.smul _ ((hPT K).mul (MT.const _))

theorem star_mem {B : Matrix (Fin n) (Fin n) C} (hB : B ∈ Acl K) : (V.l : C)⁻¹ • (B ^ V.l ^ d - B) ∈ Acl K := by
  obtain ⟨s, hs⟩ := hB
  exact closed_mem K (fun k => star_S K (s k)) (MT.smul _ ((hs.pow _).sub hs))

end RowTiePKeyEig

end Formalism.L2.FormalSeriesBounds
end
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.RowTiePOAct
section
noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace Formalism.L2.FormalSeriesBounds

namespace OAct

open PartialDerivEval LogEx OActLog OActSg

variable {C : Type} [Field C]

theorem tyS_smul (l : ℕ) (c : C) (a : ℕ → C) : tyS l (fun s => c * a s) = c • tyS l a := by
  ext n
  rw [PowerSeries.coeff_smul]
  simp only [tyS, PowerSeries.coeff_mk, smul_eq_mul, Finset.mul_sum, mul_ite, mul_zero]

variable {dd : ℕ}

theorem uncurry_sub (f g : PS C 1 dd) : un1 (f - g) = un1 f - un1 g := by
  funext μ
  show MvPowerSeries.coeff _ (f - g) = MvPowerSeries.coeff _ f - MvPowerSeries.coeff _ g
  exact map_sub _ _ _

theorem uncurry_C_mul (c : C) (f : PS C 1 dd) : un1 (MvPowerSeries.C c * f) = MvPowerSeries.C c * un1 f := by
  funext μ
  show MvPowerSeries.coeff _ (MvPowerSeries.C c * f) = MvPowerSeries.coeff μ (MvPowerSeries.C c * un1 f)
  rw [MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_C_mul]
  rfl

theorem uncurry_linear_combination (c : Fin dd → C) (f : Fin dd → PS C 1 dd) :
    un1 (∑ j, MvPowerSeries.C (c j) * f j) = ∑ j, MvPowerSeries.C (c j) * un1 (f j) := by
  funext μ
  show MvPowerSeries.coeff _ (∑ j, MvPowerSeries.C (c j) * f j) =
    MvPowerSeries.coeff μ (∑ j, MvPowerSeries.C (c j) * un1 (f j))
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_C_mul]
  rfl

theorem integralSeries_uncurry_one {V : VF C} {f : PS C 1 dd} (hf : IntS V f) : IntS V (un1 f) := fun _ => hf _

variable [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O]

theorem sgP_smul (Y : FBChart C V O dd) (c : C) (v : Fin dd → C) :
    Y.sgP (c • v) = MvPowerSeries.C c * Y.sgP v := by
  unfold FBChart.sgP
  rw [mul_neg, Finset.mul_sum]
  simp only [Pi.smul_apply, smul_eq_mul, map_mul, mul_assoc]

end OAct

end Formalism.L2.FormalSeriesBounds
end
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.ValuationEqPairOfLogUnitGerm
section
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj

namespace VP

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb] {I : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)]

theorem cc_smul {σ : Type} (c : C) {F : MvPowerSeries σ C} (hF : MvPowerSeries.constantCoeff F = 0) :
    MvPowerSeries.constantCoeff (c • F) = 0 := by
  rw [MvPowerSeries.smul_eq_C_mul, map_mul, hF, mul_zero]

theorem expS_copies (Y : FBChart C V O dd) (n : ℕ) :
    FB.expS C ((Y.k : C) • ∑ b : Fin n, ev (n := n) ![pt C dd b] (Y.B.hL C Y.h Y.w0)) =
      ∏ b : Fin n, ev (n := n) ![pt C dd b] (FB.expS C ((Y.k : C) • Y.B.hL C Y.h Y.w0)) := by
  have ha : ∀ b : Fin n, ∀ s : Fin 1 × Fin dd, MvPowerSeries.constantCoeff (![pt C dd b] s.1 s.2) = 0 := by
    intro b s
    simp [pt]
  have hc : ∀ b : Fin n, MvPowerSeries.constantCoeff (ev (n := n) ![pt C dd b] (Y.B.hL C Y.h Y.w0)) = 0 := fun b =>
    (ordGE_one_iff _).1 (ordGE_subst (VP.og (a := fun s : Fin 1 × Fin dd => ![pt C dd b] s.1 s.2) (ha b))
      ((ordGE_one_iff _).2 (VP.cc_hL Y)))
  have hs : ∀ b : Fin n, ev (n := n) ![pt C dd b] ((Y.k : C) • Y.B.hL C Y.h Y.w0) =
      (Y.k : C) • ev (n := n) ![pt C dd b] (Y.B.hL C Y.h Y.w0) := fun b =>
    MvPowerSeries.subst_smul (hasSubst_of_ordGE (VP.og (a := fun s : Fin 1 × Fin dd => ![pt C dd b] s.1 s.2) (ha b))) _ _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [VP.expS_eq _ (cc_smul _ (by rw [map_sum]; exact Finset.sum_eq_zero fun b _ => hc b)), Finset.smul_sum,
    Formalism.UnitaryBoundIntegral.ubint_mvExp_sum _ _ (fun b _ => cc_smul _ (hc b))]
  refine Finset.prod_congr rfl fun b _ => ?_
  rw [VP.expS_eq _ (cc_smul _ (VP.cc_hL Y))]
  show _ = MvPowerSeries.subst (fun s : Fin 1 × Fin dd => ![pt C dd b] s.1 s.2) (mvExp _)
  rw [VP.subst_exp (ha b) (cc_smul _ (VP.cc_hL Y))]
  exact congrArg mvExp (hs b).symm

theorem rowCopy_mul_exp {J : Fin 2 → Type} {n : ℕ} (b : Fin n) (F L : MvPowerSeries (WV J) C) :
    rowCopy b (F * mvExp L) = rowCopy b F * mvExp (rowCopy b L) := by
  rw [rtj_rowCopy_eq, rtj_rowCopy_eq, rtj_rowCopy_eq, map_mul]
  congr 1
  ext x
  rw [MvPowerSeries.coeff_rename]
  show _ = ∑ k ∈ Finset.range (x.degree + 1),
    MvPowerSeries.coeff x ((MvPowerSeries.rename (rtjR b) L) ^ k) / (k.factorial : C)
  simp_rw [← map_pow, MvPowerSeries.coeff_rename, Finset.sum_div]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y hy => ?_
  have hdeg : y.degree = x.degree := by
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, Set.mem_preimage] at hy
    rw [← hy, Finsupp.degree_mapDomain]
  show ∑ k ∈ Finset.range (y.degree + 1), _ = _
  rw [hdeg]

end VP

end Formalism.L2.FormalSeriesBounds
end
end

