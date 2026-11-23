module

public import Formalism.LocalToGlobal.CharacterGerms.Bundle0016
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0034
public import Formalism.LocalToGlobal.CharacterGerms.MfactMulCoeffMvExpLinF
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0033
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0028
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0030
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0010
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0020
public import Formalism.LocalToGlobal.CharacterGerms.RowTiePOActSelf
public import Formalism.LocalToGlobal.CharacterGerms.RowTiePHStab
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0021

@[expose] public section

-- bundled from Formalism.LocalToGlobal.CharacterGerms.ConstantCoeffPderivUncurry
section
set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace ChG

section Uniq

variable {K : Type} [Field K] [CharZero K] {τ : Type} [Fintype τ]

theorem exp_unique (y : τ → K) (Ψ : MvPowerSeries τ K) (h0 : MvPowerSeries.constantCoeff Ψ = 1)
    (hd : ∀ w, MvPowerSeries.pderiv (R := K) w Ψ = Ψ * MvPowerSeries.C (y w)) : Ψ = mvExp (linF y) := by
  have step : ∀ (w : τ) (m : τ →₀ ℕ), MvPowerSeries.coeff (m + Finsupp.single w 1) Ψ * ((m w : K) + 1) =
      y w * MvPowerSeries.coeff m Ψ := by
    intro w m
    have h := congrArg (MvPowerSeries.coeff m) (hd w)
    rw [MvPowerSeries.coeff_pderiv, mul_comm Ψ, MvPowerSeries.coeff_C_mul] at h
    exact h
  have key : ∀ (n : ℕ) (m : τ →₀ ℕ), m.degree = n →
      MvPowerSeries.coeff m Ψ = MvPowerSeries.coeff m (mvExp (linF y)) := by
    intro n
    induction n with
    | zero =>
      intro m hm
      have hm0 : m = 0 := (Finsupp.degree_eq_zero_iff m).1 hm
      subst hm0
      rw [coeff_zero_mvExp, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, h0]
    | succ n ih =>
      intro m hm
      obtain ⟨w, hw⟩ : ∃ w, m w ≠ 0 := by
        by_contra hcon
        simp only [not_exists, not_not] at hcon
        have : m = 0 := Finsupp.ext hcon
        rw [this] at hm
        simp at hm
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + Finsupp.single w 1 := by
        refine ⟨m - Finsupp.single w 1, ?_⟩
        ext x
        by_cases hx : x = w
        · subst hx
          simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply, Finsupp.single_eq_same]
          omega
        · simp [Ne.symm hx]
      have hdeg : m'.degree = n := by
        rw [map_add (f := _), Finsupp.degree_single] at hm
        omega
      have hne : ((m' w : K) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (m' w)
      have e1 := step w m'
      have e2 := coeff_mvExp_linF_step y w m'
      rw [ih m' hdeg, ← e2] at e1
      exact mul_right_cancel₀ hne e1
  ext m
  exact key _ m rfl

end Uniq

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}
  (Y : FBChart C V O dd)

open VP

theorem chi_mul {χ : PS C 1 dd} (hχ : Y.IsChar χ) :
    MvPowerSeries.subst (fun k => Y.B.G.F k) (un1 χ) =
      MvPowerSeries.subst (fun k : Fin dd => (MvPowerSeries.X ((0 : Fin 2), k) : PS C 2 dd)) (un1 χ) *
        MvPowerSeries.subst (fun k : Fin dd => (MvPowerSeries.X ((1 : Fin 2), k) : PS C 2 dd)) (un1 χ) := by
  have h := hχ.2.2
  rw [eval_single_eq_subst, eval_single_eq_subst, eval_single_eq_subst] at h
  rw [subst_singlePointUncurry (cc_F Y), subst_singlePointUncurry (fun _ => cc_X _), subst_singlePointUncurry (fun _ => cc_X _)]
  have h2 : (fun p : Fin 1 × Fin dd => addOf Y.B.G.F (pt C dd 0) (pt C dd 1) p.2) =
      fun p : Fin 1 × Fin dd => Y.B.G.F p.2 := by
    funext p
    exact ev_id _
  rw [h2] at h
  exact h

theorem constantCoeff_pderiv_uncurry (χ : PS C 1 dd) (i : Fin dd) :
    MvPowerSeries.constantCoeff (MvPowerSeries.pderiv (R := C) i (un1 χ)) = dlogC χ i := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_pderiv]
  have h1 : MvPowerSeries.coeff (Finsupp.single i 1) (un1 χ) = dlogC χ i := by
    show MvPowerSeries.coeff ((Finsupp.single i 1).mapDomain fun x : Fin dd => ((0 : Fin 1), x)) χ = _
    rw [Finsupp.mapDomain_single]
    rfl
  simp [h1]

def Psi (χ : PS C 1 dd) : MvPowerSeries (Fin dd) C := MvPowerSeries.subst (e Y) (un1 χ)

theorem chi_ode {χ : PS C 1 dd} (hχ : Y.IsChar χ) (i : Fin dd) :
    MvPowerSeries.pderiv (R := C) i (Psi Y χ) = Psi Y χ * MvPowerSeries.C (dlogC χ i) := by
  have hFK : ∀ k, Y.B.FK C k = Y.B.G.F k := by
    intro k
    show MvPowerSeries.map (algebraMap C C) (Y.B.G.F k) = _
    rw [Algebra.algebraMap_self, MvPowerSeries.map_id]
    rfl

  have hL : MvPowerSeries.pderiv (R := C) i (Psi Y χ) =
      ∑ k, MvPowerSeries.subst (exZero Y) (MvPowerSeries.pderiv (R := C) ((1 : Fin 2), i) (Y.B.G.F k)) *
        MvPowerSeries.subst (e Y) (MvPowerSeries.pderiv (R := C) k (un1 χ)) := by
    unfold Psi
    rw [pderiv_subst (og (cc_e Y))]
    refine Finset.sum_congr rfl fun k _ => ?_
    have := expODE Y i k
    rw [hFK] at this
    show MvPowerSeries.pderiv (R := C) i (un1 (Y.ex k)) * _ = _
    rw [this]

  have h := congrArg (fun G => MvPowerSeries.subst (exZero Y) (MvPowerSeries.pderiv (R := C) ((1 : Fin 2), i) G)) (chi_mul Y hχ)
  beta_reduce at h
  rw [Derivation.leibniz, pderiv_subst (og (cc_F Y)), pderiv_subst (og fun _ => cc_X _), pderiv_subst (og fun _ => cc_X _),
    MvPowerSeries.subst_add (hs (cc_exZero Y)), subst_sum (cc_exZero Y), smul_eq_mul, smul_eq_mul,
    subst_mul (cc_exZero Y), subst_mul (cc_exZero Y), subst_sum (cc_exZero Y), subst_sum (cc_exZero Y)] at h
  have h1 : ∀ k, MvPowerSeries.subst (exZero Y) (MvPowerSeries.pderiv (R := C) ((1 : Fin 2), i) (Y.B.G.F k) *
      MvPowerSeries.subst (fun k => Y.B.G.F k) (MvPowerSeries.pderiv (R := C) k (un1 χ))) =
      MvPowerSeries.subst (exZero Y) (MvPowerSeries.pderiv (R := C) ((1 : Fin 2), i) (Y.B.G.F k)) *
        MvPowerSeries.subst (e Y) (MvPowerSeries.pderiv (R := C) k (un1 χ)) := by
    intro k
    rw [subst_mul (cc_exZero Y), subst_subst (cc_F Y) (cc_exZero Y)]
    congr 2
    funext k'
    exact F_exZero Y k'
  have h2 : ∀ k, MvPowerSeries.subst (exZero Y)
      (MvPowerSeries.pderiv (R := C) ((1 : Fin 2), i) (MvPowerSeries.X ((0 : Fin 2), k) : PS C 2 dd) *
      MvPowerSeries.subst (fun k : Fin dd => (MvPowerSeries.X ((0 : Fin 2), k) : PS C 2 dd))
        (MvPowerSeries.pderiv (R := C) k (un1 χ))) = 0 := by
    intro k
    rw [MvPowerSeries.pderiv_X_of_ne (fun hh => by simpa using (Prod.ext_iff.1 hh).1), zero_mul,
      subst_zero' (cc_exZero Y)]
  have h3 : ∀ k, MvPowerSeries.subst (exZero Y)
      (MvPowerSeries.pderiv (R := C) ((1 : Fin 2), i) (MvPowerSeries.X ((1 : Fin 2), k) : PS C 2 dd) *
      MvPowerSeries.subst (fun k : Fin dd => (MvPowerSeries.X ((1 : Fin 2), k) : PS C 2 dd))
        (MvPowerSeries.pderiv (R := C) k (un1 χ))) = if k = i then MvPowerSeries.C (dlogC χ i) else 0 := by
    intro k
    by_cases hk : k = i
    · subst hk
      rw [MvPowerSeries.pderiv_X_self, one_mul, subst_subst (fun _ => cc_X _) (cc_exZero Y), if_pos rfl]
      have : (fun s : Fin dd => MvPowerSeries.subst (exZero Y) (MvPowerSeries.X ((1 : Fin 2), s) : PS C 2 dd)) =
          fun _ => 0 := by
        funext s
        rw [subst_X (cc_exZero Y)]
        rfl
      rw [this, subst_zeroPt, constantCoeff_pderiv_uncurry]
    · rw [MvPowerSeries.pderiv_X_of_ne (fun hh => hk (Prod.ext_iff.1 hh).2), zero_mul, subst_zero' (cc_exZero Y),
        if_neg hk]
  have h4 : MvPowerSeries.subst (exZero Y)
      (MvPowerSeries.subst (fun k : Fin dd => (MvPowerSeries.X ((0 : Fin 2), k) : PS C 2 dd)) (un1 χ)) = Psi Y χ := by
    rw [subst_subst (fun _ => cc_X _) (cc_exZero Y)]
    unfold Psi
    congr 1
    funext s
    rw [subst_X (cc_exZero Y)]
    rfl
  rw [Finset.sum_congr rfl fun k _ => h1 k, Finset.sum_congr rfl fun k _ => h2 k,
    Finset.sum_congr rfl fun k _ => h3 k, Finset.sum_const_zero, mul_zero, add_zero, Finset.sum_ite_eq', h4] at h
  rw [hL, h]
  simp

theorem cc_Psi {χ : PS C 1 dd} (hχ : Y.IsChar χ) : MvPowerSeries.constantCoeff (Psi Y χ) = 1 := by
  obtain ⟨-, hχ1, -⟩ := hχ
  have hu : ∀ f : PS C 1 dd, MvPowerSeries.constantCoeff (un1 f) = MvPowerSeries.constantCoeff f := by
    intro f
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    show MvPowerSeries.coeff ((0 : Fin dd →₀ ℕ).mapDomain fun x : Fin dd => ((0 : Fin 1), x)) f = _
    rw [Finsupp.mapDomain_zero]
  have he0 : ∀ k, MvPowerSeries.constantCoeff (e Y k) = 0 := fun k => (hu _).trans (Y.ex_const k)
  have hA : MvPowerSeries.HasSubst (e Y) := MvPowerSeries.hasSubst_of_constantCoeff_zero he0
  unfold Psi
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_subst hA, finsum_eq_single _ 0]
  · simp [hu, hχ1]
  · intro d hd
    obtain ⟨s, hs⟩ : ∃ s, d s ≠ 0 := by
      by_contra h
      push_neg at h
      exact hd (Finsupp.ext h)
    rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, Finsupp.prod, map_prod,
      Finset.prod_eq_zero (Finsupp.mem_support_iff.2 hs), smul_zero]
    rw [map_pow, he0, zero_pow hs]

theorem chi_exp {χ : PS C 1 dd} (hχ : Y.IsChar χ) : Psi Y χ = mvExp (linF (dlogC χ)) := exp_unique (dlogC χ) (Psi Y χ) (cc_Psi Y hχ) (chi_ode Y hχ)

end ChG

end Formalism.L2.FormalSeriesBounds
end
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.RowTiePPTClose
section
namespace Formalism.L2.FormalSeriesBounds

theorem ptSelf_of_start2 (hS : AllStartSelfSt) : PTSelfSt :=
  ptSelf_of_start hS OActSelf.oActSelf_holds hStabSelf_holds

end Formalism.L2.FormalSeriesBounds
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.RowTieValG
section
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj

namespace VP

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}
  {Var : Type} [Fintype Var] {n : ℕ}

def colLin (M : Var → Fin n × Fin dd → C) (b : Fin n) : Var → Fin dd → C := fun x i => M x (b, i)

variable (Y : FBChart C V O dd) (M : Var → Fin n × Fin dd → C)

def linPt (q : Fin n × Fin dd) : MvPowerSeries Var C := MvPowerSeries.subst (linS (colLin M q.1)) (e Y q.2)

def linPull (F : PS C n dd) : MvPowerSeries Var C := MvPowerSeries.subst (linPt Y M) F

theorem cc_linPt (q : Fin n × Fin dd) : MvPowerSeries.constantCoeff (linPt Y M q) = 0 := by
  unfold linPt
  exact VP.cc_subst (fun s => by simp [linS, MvPowerSeries.smul_eq_C_mul]) (cc_e Y q.2)

theorem linPull_mul (F G : PS C n dd) : linPull Y M (F * G) = linPull Y M F * linPull Y M G := by
  unfold linPull
  exact VP.subst_mul (cc_linPt Y M) F G

theorem linPull_prod {ι : Type} (s : Finset ι) (F : ι → PS C n dd) :
    linPull Y M (∏ i ∈ s, F i) = ∏ i ∈ s, linPull Y M (F i) := by
  unfold linPull
  exact VP.subst_prod (cc_linPt Y M) s F

theorem linear_pullback_eval_point_zero (b : Fin n) (G : PS C 2 dd) :
    linPull Y M (ev (n := n) ![pt C dd b, 0] G) =
      MvPowerSeries.subst (linS (colLin M b)) (MvPowerSeries.subst (exZero Y) G) := by
  have hL : ∀ s, MvPowerSeries.constantCoeff (linS (colLin M b) s : MvPowerSeries Var C) = 0 := fun s => by
    simp [linS, MvPowerSeries.smul_eq_C_mul]
  unfold linPull ev
  rw [VP.subst_subst (fun q => VP.constantCoeff_two_points_zero b q) (cc_linPt Y M), VP.subst_subst (cc_exZero Y) hL]
  congr 1
  funext q
  rcases q with ⟨i, k⟩
  fin_cases i
  · simp [pt, exZero, linPt, e, VP.subst_X (cc_linPt Y M)]
  · simp [exZero, VP.subst_zero' (cc_linPt Y M), VP.subst_zero' hL]

def RR (b : Fin n) (i j : Fin dd) : MvPowerSeries Var C :=
  linPull Y M (ev (n := n) ![pt C dd b, 0] (MvPowerSeries.pderiv (R := C) ((1 : Fin 2), i) (Y.B.FK C j)))

theorem linPull_DofN (b : Fin n) (u : Fin dd → C) (F : PS C n dd) :
    linPull Y M (DofN (Y.B.FK C) b u F) =
      ∑ j, (∑ i, MvPowerSeries.C (u i) * RR Y M b i j) * linPull Y M (MvPowerSeries.pderiv (R := C) (b, j) F) := by
  unfold DofN
  simp only [← MvPowerSeries.smul_eq_C_mul]
  simp only [linPull, RR, VP.subst_sum (cc_linPt Y M), VP.subst_mul (cc_linPt Y M), VP.subst_smul (cc_linPt Y M)]

theorem pderiv_linPull (x : Var) (F : PS C n dd) :
    MvPowerSeries.pderiv (R := C) x (linPull Y M F) =
      ∑ b, ∑ j, (∑ i, MvPowerSeries.C (M x (b, i)) * RR Y M b i j) *
        linPull Y M (MvPowerSeries.pderiv (R := C) (b, j) F) := by
  have hE := expODE Y
  unfold ExpODESt at hE
  have hJ : ∀ b j, MvPowerSeries.pderiv (R := C) x (linPt Y M (b, j)) =
      ∑ i, MvPowerSeries.C (M x (b, i)) * RR Y M b i j := by
    intro b j
    simp only [linPt, e, hE, pderiv_subst_linS, colLin, RR, linear_pullback_eval_point_zero, MvPowerSeries.smul_eq_C_mul]
  unfold linPull
  rw [pderiv_subst (VP.og (cc_linPt Y M)), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun j _ => ?_))
  rw [hJ b j]

theorem dpullG (b0 : Fin n) (u : Fin dd → C) (c : Var → C)
    (hc : ∀ b i, ∑ x, c x * M x (b, i) = if b = b0 then u i else 0) (F : PS C n dd) :
    linPull Y M (DofN (Y.B.FK C) b0 u F) = ∑ x, c x • MvPowerSeries.pderiv (R := C) x (linPull Y M F) := by
  have key : ∀ b j, ∑ x, c x • ((∑ i, MvPowerSeries.C (M x (b, i)) * RR Y M b i j) *
      linPull Y M (MvPowerSeries.pderiv (R := C) (b, j) F)) =
      (∑ i, MvPowerSeries.C (if b = b0 then u i else 0) * RR Y M b i j) *
        linPull Y M (MvPowerSeries.pderiv (R := C) (b, j) F) := by
    intro b j
    simp_rw [← hc b]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, Finset.sum_mul, Finset.mul_sum, MvPowerSeries.smul_eq_C_mul, mul_assoc]
    exact Finset.sum_comm
  rw [linPull_DofN]
  simp only [pderiv_linPull, Finset.smul_sum]
  conv_rhs => rw [Finset.sum_comm]; arg 2; ext b; rw [Finset.sum_comm]
  simp only [key]
  rw [Finset.sum_eq_single b0 (fun b _ hb => by simp [hb]) (by simp)]
  simp

theorem jet_iterG (b0 : Fin n) (u : Fin dd → C) (c : Var → C)
    (hc : ∀ b i, ∑ x, c x * M x (b, i) = if b = b0 then u i else 0) (k : ℕ) :
    ∀ (q : MvPolynomial Var C) (g : PS C n dd),
      jetAt0 q (linPull Y M ((DofN (Y.B.FK C) b0 u)^[k] g)) =
        jetAt0 (q * (∑ x, MvPolynomial.C (c x) * MvPolynomial.X x) ^ k) (linPull Y M g) := by
  induction k with
  | zero => intro q g; simp
  | succ k ih =>
    intro q g
    rw [Function.iterate_succ_apply, ih, dpullG Y M b0 u c hc]
    have h := jet_lin (fun x : Var => x) (q * (∑ x, MvPolynomial.C (c x) * MvPolynomial.X x) ^ k) c (linPull Y M g)
    rw [← h]
    congr 1
    ring

theorem jet_listG {ι : Type} (cp : ι → Fin n) (uv : ι → Fin dd → C) (co : ι → Var → C) (m : ι →₀ ℕ) (f : PS C n dd) :
    ∀ (ls : List ι), (∀ ℓ ∈ ls, m ℓ ≠ 0 → ∀ b i, ∑ x, co ℓ x * M x (b, i) = if b = cp ℓ then uv ℓ i else 0) →
    ∀ q : MvPolynomial Var C,
      jetAt0 q (linPull Y M (ls.foldr (fun l g => (DofN (Y.B.FK C) (cp l) (uv l))^[m l] g) f)) =
        jetAt0 (q * (ls.map fun l => (∑ x, MvPolynomial.C (co l x) * MvPolynomial.X x) ^ m l).prod)
          (linPull Y M f) := by
  intro ls
  induction ls with
  | nil => intro _ q; simp
  | cons l ls ih =>
    intro h q
    simp only [List.foldr_cons, List.map_cons, List.prod_cons]
    have h' : ∀ ℓ ∈ ls, m ℓ ≠ 0 → ∀ b i, ∑ x, co ℓ x * M x (b, i) = if b = cp ℓ then uv ℓ i else 0 :=
      fun ℓ hℓ => h ℓ (by simp [hℓ])
    by_cases hm : m l = 0
    · rw [hm]
      simp only [Function.iterate_zero, id, pow_zero, one_mul]
      exact ih h' q
    · rw [jet_iterG Y M (cp l) (uv l) (co l) (h l (by simp) hm) (m l), ih h']
      congr 1
      ring

theorem logCoordG {ι : Type} [Fintype ι] (cp : ι → Fin n) (uv : ι → Fin dd → C) (P : MvPolynomial ι C)
    (co : ι → Var → C)
    (hco : ∀ ℓ ∈ P.vars, ∀ b i, ∑ x, co ℓ x * M x (b, i) = if b = cp ℓ then uv ℓ i else 0) (F : PS C n dd) :
    MvPowerSeries.constantCoeff (DpolyN (Y.B.FK C) cp uv P F) =
      jetAt0 (MvPolynomial.aeval (fun ℓ => ∑ x, MvPolynomial.C (co ℓ x) * MvPolynomial.X x) P) (linPull Y M F) := by
  have hj1 : ∀ G : MvPowerSeries Var C, jetAt0 (1 : MvPolynomial Var C) G = MvPowerSeries.constantCoeff G :=
    fun G => by simpa using jet_C (σ := Var) (1 : C) G
  have hD : ∀ m ∈ P.support, MvPowerSeries.constantCoeff (DmonN (Y.B.FK C) cp uv m F) =
      jetAt0 (∏ ℓ, (∑ x, MvPolynomial.C (co ℓ x) * MvPolynomial.X x) ^ m ℓ) (linPull Y M F) := by
    intro m hm
    have h1 := jet_listG Y M cp uv co m F (Finset.univ : Finset ι).toList
      (fun ℓ _ hmℓ => hco ℓ ((MvPolynomial.mem_vars_iff_mem_support ℓ).2 ⟨m, hm, Finsupp.mem_support_iff.2 hmℓ⟩)) 1
    rw [one_mul, Finset.prod_map_toList, hj1, linPull, VP.cc_subst_eq (cc_linPt Y M)] at h1
    exact h1
  unfold DpolyN
  conv_rhs => rw [MvPolynomial.as_sum P]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum]
  rw [tpjet_jetAt0_sum]
  refine Finset.sum_congr rfl (fun m hm => ?_)
  rw [MvPolynomial.aeval_monomial, map_mul, MvPowerSeries.constantCoeff_C, hD m hm, MvPolynomial.algebraMap_eq,
    mul_comm (MvPolynomial.C (AddMonoidAlgebra.coeff P m)), jet_mul_C, Finsupp.prod_fintype _ _ (fun ℓ => pow_zero _)]

end VP

end Formalism.L2.FormalSeriesBounds
end
end

