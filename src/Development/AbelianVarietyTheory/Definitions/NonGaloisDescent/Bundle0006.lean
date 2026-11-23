module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TameDescentExtendedActionExtraVector
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0088
public import Formalism.LocalRingCardinality.AdicCompletionLocal.InstIsAdicCompleteOCSpanSingletonSetCast
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsOfLayers
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0150

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsEqMulAddOfIsAdicComplete
section
noncomputable section

namespace GlobalTheory.BK

open PowerSeries Filter Topology Matrix

theorem exists_eq_mul_add_of_isAdicComplete {R : Type} [CommRing R] (t : R)
    [IsAdicComplete (Ideal.span {t}) R] (T : R →+ R) (hT : ∀ x, T (t * x) = t * T x) (w : R) :
    ∃ x, x = t * T x + w := by
  have hS (n : ℕ) (x y : R) : x ≡ y [SMOD (Ideal.span {t} ^ n • ⊤ : Ideal R)] ↔ t ^ n ∣ x - y := by
    simp [SModEq.sub_mem, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  have hd (n : ℕ) (x : R) (h : t ^ n ∣ x) : t ^ (n + 1) ∣ t * T x := by
    obtain ⟨y, rfl⟩ := h
    have : T (t ^ n * y) = t ^ n * T y := by
      induction n with
      | zero => simp
      | succ n ih => rw [pow_succ', mul_assoc, hT, ih, mul_assoc]
    exact ⟨T y, by rw [this]; ring⟩
  let f : ℕ → R := fun n => (fun x => t * T x + w)^[n] 0
  have hf (n : ℕ) : f (n + 1) = t * T (f n) + w := Function.iterate_succ_apply' _ _ _
  have h1 (n : ℕ) : t ^ n ∣ f (n + 1) - f n := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [hf (n + 1), hf n, add_sub_add_right_eq_sub, ← mul_sub, ← map_sub, ← hf]
      exact hd _ _ ih
  obtain ⟨x, hx⟩ := IsPrecomplete.prec' (I := Ideal.span {t}) f (fun {m n} hmn => by
    rw [hS]
    induction hmn with
    | refl => simp
    | step h ih =>
      have := dvd_sub ih ((pow_dvd_pow t h).trans (h1 _))
      convert this using 1
      simp)
  refine ⟨x, sub_eq_zero.1 (IsHausdorff.haus' (I := Ideal.span {t}) _ fun n => ?_)⟩
  rw [hS, sub_zero]
  have := dvd_sub (hd n _ ((hS _ _ _).1 (hx n))) ((hS _ _ _).1 (hx (n + 1)))
  refine (pow_dvd_pow t n.le_succ).trans ?_
  convert this using 1
  rw [hf, map_sub]
  ring

theorem pow_mul_factorial_dvd (l k : ℕ) (hl : 0 < l) : l ^ k * k.factorial ∣ (l * k).factorial := by
  induction k with
  | zero => simp
  | succ k ih =>
    obtain ⟨m, hm⟩ : ∃ m, l * (k + 1) = m + 1 := ⟨l * (k + 1) - 1, by
      have : 0 < l * (k + 1) := by positivity
      omega⟩
    have h : (l * k).factorial ∣ m.factorial := Nat.factorial_dvd_factorial (by nlinarith)
    rw [hm, Nat.factorial_succ m, ← hm, Nat.factorial_succ, pow_succ]
    refine Dvd.dvd.trans (dvd_of_eq ?_) (mul_dvd_mul_left (l * (k + 1)) (ih.trans h))
    ring

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] (l e : ℕ) {a : ℕ} [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e]

theorem exists_mul_frob_E : ∃ c ∈ S O K e, c * frob K l (E K l e) = l := by
  have hl := (Fact.out : l.Prime).pos
  have : NeZero (e * l) := ⟨(Nat.mul_pos (NeZero.pos e) hl).ne'⟩
  have hl0 := l_ne_zero (K := K) l
  let c : K⟦X⟧ := expand (e * l) (NeZero.ne _) (rescale (-(l : K)⁻¹) (PowerSeries.mk 1))
  have hc (n : ℕ) : ‖coeff n c‖ * wS K e n ≤ wS K (e * l) n := by
    rw [coeff_expand]
    split_ifs with h
    · obtain ⟨k, rfl⟩ := h
      rw [wS, wS, Nat.mul_div_cancel_left _ (NeZero.pos (e * l)), mul_assoc e l,
        Nat.mul_div_cancel_left _ (NeZero.pos e), coeff_rescale, coeff_mk, Pi.one_apply, mul_one,
        norm_pow, norm_neg, norm_inv, inv_pow, inv_mul_le_iff₀ (pow_pos (norm_pos_iff.2 hl0) k),
        ← norm_pow, ← norm_mul]
      exact_mod_cast norm_natCast_le_of_dvd (K := K) (pow_mul_factorial_dvd l k hl)
    · simpa using wS_nonneg _ _
  refine ⟨c, ⟨fun n => (hc n).trans (wS_le_one _ _), squeeze_zero
    (fun n => mul_nonneg (norm_nonneg _) (wS_nonneg e n)) hc (tendsto_wS l (e * l))⟩, ?_⟩
  have h := congrArg (fun f => expand (e * l) (NeZero.ne _) (rescale (-(l : K)⁻¹) f))
    (mk_one_mul_one_sub_eq_one K)
  simp only [map_mul, map_sub, map_one, rescale_X, expand_X, expand_C, map_neg] at h
  have h2 : (C (l : K)⁻¹ : K⟦X⟧) * l = 1 := by
    rw [← map_natCast (C : K →+* K⟦X⟧), ← map_mul, inv_mul_cancel₀ hl0, map_one]
  rw [E, map_add (f := _), map_pow, frob_X, map_natCast, ← pow_mul, mul_comm l e]
  linear_combination (l : K⟦X⟧) * h - c * X ^ (e * l) * h2

omit [IsUltrametricDist K] in
theorem E_mul_N_Ezpow (j : ℤ) :
    E K l e * N K (Ezpow (K := K) l e j) =
      (j : K⟦X⟧) * N K (E K l e) * Ezpow (K := K) l e j := by
  have h1 (i : ℤ) : Ezpow (K := K) l e (i + 1) = Ezpow (K := K) l e i * E K l e := by
    simp [Ezpow, _root_.zpow_add]
  have key (i : ℤ) : N K (Ezpow (K := K) l e (i + 1)) =
      Ezpow (K := K) l e i * N K (E K l e) + E K l e * N K (Ezpow (K := K) l e i) := by
    rw [h1, Derivation.leibniz]
    rfl
  induction j using Int.induction_on with
  | zero => simp [Ezpow]
  | succ i ih =>
    rw [key, ih, h1]
    push_cast
    ring
  | pred i ih =>
    have h := key (-i - 1)
    have h' := h1 (-i - 1)
    rw [sub_add_cancel] at h h'
    rw [h, h'] at ih
    refine (isUnit_E (K := K) l e).mul_left_cancel ?_
    push_cast at ih ⊢
    linear_combination ih

omit [IsUltrametricDist K] in
theorem map_Ezpow (f : K⟦X⟧ →+* K⟦X⟧) (hf : f (E K l e) = E K l e) (j : ℤ) :
    f (Ezpow (K := K) l e j) = Ezpow (K := K) l e j := by
  have h : Units.map (f : K⟦X⟧ →* K⟦X⟧) (isUnit_E (K := K) l e).unit = (isUnit_E l e).unit :=
    Units.ext hf
  conv_rhs => rw [Ezpow, ← h, ← map_zpow]
  rfl

omit [IsUltrametricDist K] in
theorem Ezpow_neg_mul (j : ℤ) : Ezpow (K := K) l e (-j) * Ezpow (K := K) l e j = 1 := by
  rw [Ezpow, Ezpow, ← Units.val_mul, ← _root_.zpow_add]
  simp

variable {l e}

theorem mx_rankOne_eq (j : ZMod a → ℤ) (τ : ZMod a) (i k : Unit) :
    (rankOne O K l e j).mx τ i k = Ezpow (K := K) l e (j τ) := by
  have h : Units.map ((invE l e (A O K)).val : invE l e (A O K) →* K⟦X⟧) (Eunit O K l e) =
      (isUnit_E l e).unit := Units.ext rfl
  rw [Ezpow, ← h, ← map_zpow]
  rw [PhiMod.mx, rankOne]
  dsimp only
  generalize Eunit O K l e ^ j τ = u
  simp

theorem mxInv_rankOne_eq (j : ZMod a → ℤ) (τ : ZMod a) (i k : Unit) :
    (rankOne O K l e j).mxInv τ i k = Ezpow (K := K) l e (-j τ) := by
  have h := congrFun (congrFun ((rankOne O K l e j).mxInv_mul_mx τ) ()) ()
  rw [Matrix.mul_apply, Fintype.sum_unique, mx_rankOne_eq, Matrix.one_apply_eq,
    ← Ezpow_neg_mul l e (j τ)] at h
  exact mul_right_cancel₀ (Units.ne_zero _) h

theorem phi_bas_rankOne (j : ℤ) : (rankOne O K l e fun _ : ZMod a => j).phi (bas ()) =
    Ezpow (K := K) l e j • bas () := by
  ext τ i : 2
  simp [PhiMod.phi_bas, mx_rankOne_eq, bas]

theorem mem_ext_rankOne (j : ℤ) {B : Subalgebra O K⟦X⟧} {v : Vec K a Unit} :
    v ∈ (rankOne O K l e fun _ : ZMod a => j).ext B ↔ ∀ τ, Ezpow (K := K) l e (-j) * v τ () ∈ B := by
  rw [PhiMod.ext, mem_tot]
  refine forall_congr' fun τ => ?_
  rw [PhiMod.extc, Set.range_unique, Submodule.mem_span_singleton]
  have h (c : B) : c • ((rankOne O K l e fun _ : ZMod a => j).mx τ).col () = v τ ↔
      (c : K⟦X⟧) = Ezpow (K := K) l e (-j) * v τ () := by
    simp only [funext_iff, Unique.forall_iff, Pi.smul_apply, Subalgebra.smul_def, smul_eq_mul,
      Matrix.col_apply, mx_rankOne_eq]
    constructor <;> intro hc
    · rw [← hc, mul_left_comm, Ezpow_neg_mul, mul_one]
    · rw [hc, mul_right_comm, Ezpow_neg_mul, one_mul]
  exact ⟨fun ⟨c, hc⟩ => (h c).1 hc ▸ c.2, fun hv => ⟨⟨_, hv⟩, (h ⟨_, hv⟩).2 rfl⟩⟩

variable [CompleteSpace K]

theorem exists_nabla_rankOne (j : ℤ) : ∃ γ ∈ S O K e,
    (rankOne O K l e fun _ : ZMod a => j).nabla (Ezpow (K := K) l e j • bas ()) =
      γ • Ezpow (K := K) l e j • bas () := by
  set P := rankOne O K l e fun _ : ZMod a => j
  obtain ⟨c, hc, hcE⟩ := exists_mul_frob_E (O := O) (K := K) l e
  obtain ⟨m, hm⟩ : ∃ m, l = m + 1 := Nat.exists_eq_succ_of_ne_zero (Fact.out : l.Prime).ne_zero
  obtain ⟨n, hn⟩ : ∃ n, l * e = n + 1 :=
    Nat.exists_eq_succ_of_ne_zero (mul_ne_zero (Fact.out : l.Prime).ne_zero (NeZero.ne e))
  have := isAdicComplete_S O K l e
  obtain ⟨γ, hγ⟩ := exists_eq_mul_add_of_isAdicComplete (l : S O K e)
    { toFun := fun x => uIn _ ^ m * ⟨_, frob_mem_S l x.2⟩
      map_zero' := Subtype.ext (by simp)
      map_add' := fun x y => Subtype.ext (by simp [mul_add]) }
    (fun x => Subtype.ext (by simp [mul_left_comm])) (-((j : S O K e) * (e : S O K e) * uIn (S O K e) ^ n * (⟨c, hc⟩ : S O K e)))
  have hγ' : (γ : K⟦X⟧) = (l : K⟦X⟧) * (X ^ m * frob K l γ) +
      -((j : K⟦X⟧) * (e : K⟦X⟧) * (X : K⟦X⟧) ^ n * c) := by
    simpa using congrArg Subtype.val hγ
  refine ⟨γ, γ.2, smul_right_injective _ (X_ne_zero (R := K)) ?_⟩
  have hq : (l : K⟦X⟧) * frob K l (N K (Ezpow (K := K) l e (-j)) * Ezpow (K := K) l e j) =
      -((j : K⟦X⟧) * (e : K⟦X⟧) * (X : K⟦X⟧) ^ (n + 1) * c) := by
    have h1 : E K l e * (N K (Ezpow (K := K) l e (-j)) * Ezpow (K := K) l e j) =
        -((j : K⟦X⟧) * (e : K⟦X⟧) * (X : K⟦X⟧) ^ e) := by
      rw [← mul_assoc, E_mul_N_Ezpow, mul_assoc, Ezpow_neg_mul, N_E]
      push_cast
      ring
    have h2 := congrArg (frob K l) h1
    simp only [map_mul, map_neg, map_pow, frob_X, map_natCast, map_intCast, ← pow_mul, hn] at h2 ⊢
    rw [← hcE]
    linear_combination c * h2
  have hb : (bas () : Vec K a Unit) = Ezpow (K := K) l e (-j) • Ezpow (K := K) l e j • bas () := by
    rw [smul_smul, Ezpow_neg_mul, one_smul]
  have hl (v : Vec K a Unit) : (l : K) • v = (l : K⟦X⟧) • v := by
    rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
  have hR : Raises (P.lphi * mulV K a Unit (Ezpow (K := K) l e (-j))) := fun k v hv =>
    P.raises_lphi k _ ((uPow K a Unit _).smul_mem _ hv)
  change P.conn _ = (X : K⟦X⟧) • (γ : K⟦X⟧) • Ezpow (K := K) l e j • bas ()
  rw [← sub_eq_zero, smul_smul X]
  refine hR.eq_zero (σ := (id : Unit → Unit)) Function.surjective_id
    (δ := fun _ =>
      P.conn (Ezpow (K := K) l e j • bas ()) -
        (X * (γ : K⟦X⟧)) • Ezpow (K := K) l e j • bas ())
    (fun _ => sub_mem (P.conn_mem_uPow _) (by rw [mul_smul]; exact X_smul_mem_uPow _))
    (fun _ => ?_) ()
  have h3 : Ezpow (K := K) l e (-j) • P.conn (Ezpow (K := K) l e j • bas ()) =
      P.conn (bas ()) - (N K (Ezpow (K := K) l e (-j)) * Ezpow (K := K) l e j) • bas () := by
    conv_rhs => rw [hb, P.conn_smul, ← hb, mul_smul, add_sub_cancel_left]
  have hmulV (v : Vec K a Unit) :
      mulV K a Unit (Ezpow (K := K) l e (-j)) v = Ezpow (K := K) l e (-j) • v := rfl
  rw [mul_apply_eq_comp, hmulV, smul_sub, h3, smul_comm _ (X * (γ : K⟦X⟧)), ← hb, map_sub,
    map_sub, P.lphi_apply, ← P.conn_phi, P.lphi_apply, P.lphi_apply, P.phi_smul, P.phi_smul,
    phi_bas_rankOne, hl, hl, smul_smul (l : K⟦X⟧), smul_smul (l : K⟦X⟧), hq, sub_sub, ← add_smul,
    map_mul, frob_X]
  congr 2
  have hX : (X : K⟦X⟧) ^ l = X ^ (m + 1) := by rw [← hm]
  linear_combination X * hγ' - l * frob K l γ * hX

end GlobalTheory.BK
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ImportsAlt
section
noncomputable section

open Formalism.Per
open scoped Formalism.Per

namespace GlobalTheory.PSer

variable {l : ℕ} [Fact l.Prime]

def sh (x : Fl l) : ℂ_[l] := ((x.untilt : OC l) : ℂ_[l])

def pw (k : ℤ) (x : Fl l) : Fl l := ((frobeniusEquiv (Fl l) l : RingAut (Fl l)) ^ k : RingAut (Fl l)) x

def lam (h j : ℕ) (x : Fl l) : ℂ_[l] := ∑' n : ℤ, (l : ℂ_[l]) ^ (-n) * sh (pw (n * h + j) x)

def abelian₂ (h j : ℕ) (y : ℕ → Fl l) : ℂ_[l] := ∑' k : ℕ, (l : ℂ_[l]) ^ k * lam h j (y k)

def gam (l : ℕ) [Fact l.Prime] (h j : ℕ) (r : ℝ) : ℝ :=
  ⨆ n : ℤ, ‖(l : ℂ_[l])‖ ^ (-n) * r ^ ((l : ℝ) ^ (n * h + j : ℤ))

end GlobalTheory.PSer

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LayersOfExists
section
noncomputable section

namespace GlobalTheory.HWL.Back

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct
open scoped Classical

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

variable {Zl Ai : Type} [CommRing Zl] [CommRing Ai] [Algebra Zl O] [Algebra Zl Ai]
    {RW : Type} [CommRing RW] [Algebra O RW]
    {inclR : (O ⊗[Zl] Ai) →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : O ⊗[Zl] Ai}
    {W : LocWach PD LL O v n} {E : EtTie W (O ⊗[Zl] Ai) RW inclR φR gR πA}
    {ιdR : Ai →+* BdR} {p1 : Ai} {tS zS : BdR}


theorem tmul_cancel (hO : Function.Injective (algebraMap O LL)) (W : LocWach PD LL O v n)
    (e₀ : ↥W.one.L.T) (h₀ : Submodule.span O {e₀} = ⊤) {r r' : RW}
    (h : (r ⊗ₜ[O] e₀ : TW RW W.one) = r' ⊗ₜ[O] e₀) : r = r' := by
  obtain ⟨e, he, hT⟩ := W.one_line
  have hne : (e₀ : W.one.V) ≠ 0 := by
    intro h0
    have heT : e ∈ W.one.L.T := hT ▸ Submodule.mem_span_singleton_self e
    have : (⟨e, heT⟩ : ↥W.one.L.T) ∈ Submodule.span O {e₀} := h₀ ▸ Submodule.mem_top
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp this
    apply he
    have := congrArg Subtype.val ha
    simp only [Submodule.coe_smul, h0, smul_zero] at this
    exact this.symm
  have hbij : Function.Bijective (LinearMap.toSpanSingleton O ↥W.one.L.T e₀) := by
    constructor
    · rw [injective_iff_map_eq_zero]
      intro a ha
      have := congrArg Subtype.val ha
      simp only [LinearMap.toSpanSingleton_apply, Submodule.coe_smul, Submodule.coe_zero] at this
      rw [← algebraMap_smul LL a, smul_eq_zero] at this
      exact hO (by rw [this.resolve_right hne, map_zero])
    · rw [← LinearMap.range_eq_top, LinearMap.range_toSpanSingleton, h₀]
  let ψ := (LinearEquiv.ofBijective _ hbij).symm
  have hψ : ψ e₀ = 1 := by
    rw [LinearEquiv.symm_apply_eq]
    simp
  have := congrArg (fun x => TensorProduct.rid O RW (LinearMap.lTensor RW ψ.toLinearMap x)) h
  simpa [hψ] using this

theorem ioE_φ (hO : Function.Injective (algebraMap O LL))
    (E : EtTie W (O ⊗[Zl] Ai) RW inclR φR gR πA) (a : W.EE) : E.ioE (W.φE a) = φR (E.ioE a) := by
  obtain ⟨e, e₀, h₀, he, -⟩ := E.one_e
  have h1 := E.jD_φ W.one (a • e)
  rw [W.φD_smul, E.jD_smul, E.jD_smul, E.jD_φ, he] at h1
  simp only [TWmap, smul_tmul', smul_eq_mul, mul_one, map_tmul, AlgHom.toLinearMap_apply, map_one,
    LinearMap.id_apply] at h1
  exact tmul_cancel hO W e₀ h₀ h1

theorem ioE_γ (hO : Function.Injective (algebraMap O LL))
    (E : EtTie W (O ⊗[Zl] Ai) RW inclR φR gR πA) (g : G) (a : W.EE) :
    E.ioE (W.γE (W.resΓ g) a) = gR g (E.ioE a) := by
  obtain ⟨e, e₀, h₀, he, -⟩ := E.one_e
  have h1 := E.jD_act W.one g (a • e)
  have h2 : W.one.actT g e₀ = e₀ := Subtype.ext (W.one_triv g _)
  rw [W.γD_smul, E.jD_smul, E.jD_smul, E.jD_act, he] at h1
  simp only [TWact, smul_tmul', smul_eq_mul, mul_one, map_tmul, AlgHom.toLinearMap_apply, map_one,
    h2] at h1
  exact tmul_cancel hO W e₀ h₀ h1





end Generic

section Concrete

variable {l : ℕ} [Fact l.Prime]


end Concrete

end GlobalTheory.HWL.Back
end
end

