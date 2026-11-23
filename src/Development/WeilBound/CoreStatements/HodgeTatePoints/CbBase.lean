module

public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.LogClosed

@[expose] public section

noncomputable section

namespace PositivityTheory.HtPt.Cb

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Conj
open ReciprocityTheory.ChartRestriction.G.TB

variable {R : Type} [CommRing R] {d : ℕ} {l m n : ℕ}

def Z (x : Pt R n d) : Prop := ∀ i, constantCoeff (x i) = 0

def ZZ (b : Fin m → Pt R n d) : Prop := ∀ j i, constantCoeff (b j i) = 0

def ep (b : Fin m → Pt R n d) (x : Pt R m d) : Pt R n d := fun i => ev b (x i)

theorem Z_pt (j : Fin n) : Z (pt R d j) := fun i => by simp [pt]
theorem Z_zero : Z (0 : Pt R n d) := fun i => by simp
theorem ZZ_nil : ZZ (![] : Fin 0 → Pt R n d) := fun j => j.elim0
theorem ZZ_cons {x : Pt R n d} {b : Fin m → Pt R n d} (hx : Z x) (hb : ZZ b) : ZZ (Matrix.vecCons x b) :=
  LogPf.CZ.cons hx hb
theorem Z_add (G : FGLaw R d) {x y : Pt R n d} (hx : Z x) (hy : Z y) : Z (G.add x y) :=
  fun i => LogPf.constantCoeff_ev (ZZ_cons hx (ZZ_cons hy ZZ_nil)) (G.const i)
theorem Z_comp1 {φ : Pt R 1 d} {x : Pt R n d} (hφ : Z φ) (hx : Z x) : Z (comp1 φ x) :=
  fun i => LogPf.constantCoeff_ev (ZZ_cons hx ZZ_nil) (hφ i)
theorem Z_act {O : Type} [CommRing O] {G : FGLaw R d} (A : OAct O G) (a : O) : Z (A.act a) := A.const a
theorem Z_ptPow (p : ℕ) [hp : Fact p.Prime] (j : Fin n) : Z (ptPow R d p j) := fun i => by
  simp [ptPow, hp.out.ne_zero]

theorem evm {b : Fin m → Pt R n d} (hb : ZZ b) (f g : PS R m d) : ev b (f * g) = ev b f * ev b g :=
  LogPf.ev_mul hb f g
theorem eva {b : Fin m → Pt R n d} (hb : ZZ b) (f g : PS R m d) : ev b (f + g) = ev b f + ev b g :=
  LogPf.ev_add hb f g
theorem evz {b : Fin m → Pt R n d} (hb : ZZ b) : ev b (0 : PS R m d) = 0 := LogPf.ev_zero' hb
theorem evsum {b : Fin m → Pt R n d} (hb : ZZ b) {ι : Type} (s : Finset ι) (f : ι → PS R m d) :
    ev b (∑ x ∈ s, f x) = ∑ x ∈ s, ev b (f x) := LogPf.ev_sum hb s f
theorem evprod {b : Fin m → Pt R n d} (hb : ZZ b) {ι : Type} (s : Finset ι) (f : ι → PS R m d) :
    ev b (∏ x ∈ s, f x) = ∏ x ∈ s, ev b (f x) := by
  simp only [← LogPf.evHom_apply hb, map_prod]
theorem evpow {b : Fin m → Pt R n d} (hb : ZZ b) (f : PS R m d) (k : ℕ) : ev b (f ^ k) = ev b f ^ k := by
  simp only [← LogPf.evHom_apply hb, map_pow]
theorem ccev {b : Fin m → Pt R n d} (hb : ZZ b) (f : PS R m d) : constantCoeff (ev b f) = constantCoeff f :=
  LogPf.cc_ev hb f

theorem ev1 {b : Fin m → Pt R n d} {x : Pt R m d} (hb : ZZ b) (hx : Z x) (f : PS R 1 d) :
    ev b (ev ![x] f) = ev ![ep b x] f := by
  rw [LogPf.ev_ev hb (ZZ_cons hx ZZ_nil)]
  congr 1; funext j; fin_cases j; rfl

theorem ev2 {b : Fin m → Pt R n d} {x y : Pt R m d} (hb : ZZ b) (hx : Z x) (hy : Z y) (f : PS R 2 d) :
    ev b (ev ![x, y] f) = ev ![ep b x, ep b y] f := by
  rw [LogPf.ev_ev hb (ZZ_cons hx (ZZ_cons hy ZZ_nil))]
  congr 1; funext j; fin_cases j <;> rfl

theorem ev3 {b : Fin m → Pt R n d} {x y z : Pt R m d} (hb : ZZ b) (hx : Z x) (hy : Z y) (hz : Z z)
    (f : PS R 3 d) : ev b (ev ![x, y, z] f) = ev ![ep b x, ep b y, ep b z] f := by
  rw [LogPf.ev_ev hb (ZZ_cons hx (ZZ_cons hy (ZZ_cons hz ZZ_nil)))]
  congr 1; funext j; fin_cases j <;> rfl

theorem ep_pt {b : Fin m → Pt R n d} (hb : ZZ b) (j : Fin m) : ep b (pt R d j) = b j :=
  funext fun i => LogPf.ev_X hb j i
theorem ep_zero {b : Fin m → Pt R n d} (hb : ZZ b) : ep b (0 : Pt R m d) = 0 :=
  funext fun _ => evz hb
theorem ep_add (G : FGLaw R d) {b : Fin m → Pt R n d} {x y : Pt R m d} (hb : ZZ b) (hx : Z x) (hy : Z y) :
    ep b (G.add x y) = G.add (ep b x) (ep b y) := funext fun _ => ev2 hb hx hy _
theorem ep_comp1 (φ : Pt R 1 d) {b : Fin m → Pt R n d} {x : Pt R m d} (hb : ZZ b) (hx : Z x) :
    ep b (comp1 φ x) = comp1 φ (ep b x) := funext fun _ => ev1 hb hx _
theorem ep_one (φ : Pt R 1 d) (x : Pt R n d) : ep ![x] φ = comp1 φ x := rfl
theorem ep_ptPow (p : ℕ) {b : Fin m → Pt R n d} (hb : ZZ b) (j : Fin m) :
    ep b (ptPow R d p j) = fun i => b j i ^ p :=
  funext fun i => by rw [ep, ptPow, evpow hb, LogPf.ev_X hb]

theorem germComp1_zero_of_noConstantCoeff {φ : Pt R 1 d} (hφ : Z φ) : comp1 φ (0 : Pt R n d) = 0 := by
  funext i
  have : (![(0 : Pt R n d)] : Fin 1 → Pt R n d) = fun _ _ => 0 := by funext j; fin_cases j; rfl
  rw [comp1, this, LogPf.ev_zeroFam, hφ i, map_zero]; rfl

theorem germCompOne_identityPoint_left (φ : Pt R 1 d) : comp1 φ (pt R (n := 1) d 0) = φ :=
  funext fun _ => ev_pt_self _ (fun j => by fin_cases j; rfl) _

theorem germComp1_germComp1_eq_substitute (φ : Pt R 1 d) {ψ : Pt R 1 d} {x : Pt R n d} (hψ : Z ψ) (hx : Z x) :
    comp1 (comp1 φ ψ) x = comp1 φ (comp1 ψ x) := ep_comp1 φ (ZZ_cons hx ZZ_nil) hψ

theorem eval_points_two (f : PS R 2 d) : ev (n := 2) ![pt R d 0, pt R d 1] f = f :=
  ev_pt_self _ (fun j => by fin_cases j <;> rfl) _

theorem eval_points_three (f : PS R 3 d) : ev (n := 3) ![pt R d 0, pt R d 1, pt R d 2] f = f :=
  ev_pt_self _ (fun j => by fin_cases j <;> rfl) _

section Law

variable (G : FGLaw R d) {x y z : Pt R n d}

theorem p_zero_add (hx : Z x) : G.add 0 x = x := by
  have h : G.add 0 (pt R (n := 1) d 0) = pt R d 0 := funext G.unit
  have hb := ZZ_cons hx ZZ_nil
  have he := congrArg (ep ![x]) h
  rw [ep_add G hb Z_zero (Z_pt 0), ep_zero hb, ep_pt hb] at he
  exact he

theorem p_add_comm (hx : Z x) (hy : Z y) : G.add x y = G.add y x := by
  funext i
  have hb := ZZ_cons hx (ZZ_cons hy ZZ_nil)
  have he := congrArg (ev ![x, y]) (G.comm i)
  rw [ev2 hb (Z_pt 1) (Z_pt 0), ep_pt hb, ep_pt hb] at he
  exact he.symm

theorem p_add_zero (hx : Z x) : G.add x 0 = x := by
  rw [p_add_comm G hx Z_zero, p_zero_add G hx]

variable {G} {O : Type} [CommRing O] (A : OAct O G)

theorem act_add (a : O) (hx : Z x) (hy : Z y) :
    comp1 (A.act a) (G.add x y) = G.add (comp1 (A.act a) x) (comp1 (A.act a) y) := by
  have hb := ZZ_cons hx (ZZ_cons hy ZZ_nil)
  have he := congrArg (ep ![x, y]) (A.hom a)
  rw [ep_comp1 _ hb (Z_add G (Z_pt 0) (Z_pt 1)), ep_add G hb (Z_pt 0) (Z_pt 1),
    ep_add G hb (Z_comp1 (Z_act A a) (Z_pt 0)) (Z_comp1 (Z_act A a) (Z_pt 1)),
    ep_comp1 _ hb (Z_pt 0), ep_comp1 _ hb (Z_pt 1), ep_pt hb, ep_pt hb] at he
  exact he

theorem add_act (a b : O) (hx : Z x) :
    comp1 (A.act (a + b)) x = G.add (comp1 (A.act a) x) (comp1 (A.act b) x) := by
  rw [A.add_act]
  exact ep_add G (ZZ_cons hx ZZ_nil) (Z_act A a) (Z_act A b)

theorem mul_act (a b : O) (hx : Z x) : comp1 (A.act (a * b)) x = comp1 (A.act a) (comp1 (A.act b) x) := by
  rw [A.mul_act, germComp1_germComp1_eq_substitute _ (Z_act A b) hx]

theorem act_comm (a b : O) (hx : Z x) :
    comp1 (A.act a) (comp1 (A.act b) x) = comp1 (A.act b) (comp1 (A.act a) x) := by
  rw [← mul_act A a b hx, ← mul_act A b a hx, mul_comm]

end Law

theorem dpt (v : Fin n × Fin d) (j : Fin n) (i : Fin d) :
    pderiv (R := R) v (pt R (n := n) d j i) = if (j, i) = v then 1 else 0 := by
  rw [pt, MvPowerSeries.pderiv_X, Pi.single_apply]

section ChainRule

open scoped MvPowerSeries.WithPiTopology

local macro "prove_cb_ev_chain_rule " R:ident b:ident hb:ident f:ident v:ident : term =>
  `(by
    classical
    let : UniformSpace $R := ⊥
    let family := fun p : _ × _ => $b p.1 p.2
    change pderiv $v (subst family $f) = ∑ p, subst family (pderiv p $f) * pderiv $v (family p)
    have hsubst := continuous_subst (R := $R) (LogPf.CZ.hasSubst (show LogPf.CZ $b from $hb))
    have hderiv {σ : Type} (i : σ) : Continuous (pderiv (R := $R) i) := by
      apply continuous_pi
      intro e
      change Continuous (fun g => coeff e (pderiv i g))
      simp only [coeff_pderiv]
      exact (WithPiTopology.continuous_coeff $R _).mul continuous_const
    refine congrFun (WithPiTopology.denseRange_toMvPowerSeries.equalizer
      ((hderiv $v).comp hsubst) (continuous_finsetSum _ fun p _ =>
        (hsubst.comp (hderiv p)).mul continuous_const) ?_) $f
    funext q
    change pderiv $v (subst family (q : MvPowerSeries _ $R)) =
      ∑ p, subst family (pderiv p (q : MvPowerSeries _ $R)) * pderiv $v (family p)
    simp only [pderiv_coe, subst_coe]
    induction q using MvPolynomial.induction_on with
    | C c => simp
    | add q r hq hr => simp only [map_add, hq, hr, add_mul, Finset.sum_add_distrib]
    | mul_X q p hq =>
      rw [map_mul, MvPolynomial.aeval_X, Derivation.leibniz, hq, smul_eq_mul, smul_eq_mul,
        Finset.mul_sum]
      simp [Pi.single_apply, apply_ite (MvPolynomial.aeval family), add_mul,
        Finset.sum_add_distrib, mul_assoc])

theorem d1 {x : Pt R n d} (hx : Z x) (f : PS R 1 d) (v : Fin n × Fin d) :
    pderiv v (ev ![x] f) = ∑ c, ev ![x] (pderiv ((0 : Fin 1), c) f) * pderiv v (x c) := by
  let b : Fin 1 → Pt R n d := ![x]
  have hb : ZZ b := ZZ_cons hx ZZ_nil
  have hchain : pderiv v (ev b f) =
      ∑ p : Fin 1 × Fin d, ev b (pderiv p f) * pderiv v (b p.1 p.2) :=
    prove_cb_ev_chain_rule R b hb f v
  change pderiv v (ev b f) = _
  rw [hchain, Fintype.sum_prod_type, Fin.sum_univ_one]
  rfl

theorem d2 {x y : Pt R n d} (hx : Z x) (hy : Z y) (f : PS R 2 d) (v : Fin n × Fin d) :
    pderiv v (ev ![x, y] f) = ∑ c, ev ![x, y] (pderiv ((0 : Fin 2), c) f) * pderiv v (x c) +
      ∑ c, ev ![x, y] (pderiv ((1 : Fin 2), c) f) * pderiv v (y c) := by
  let b : Fin 2 → Pt R n d := ![x, y]
  have hb : ZZ b := ZZ_cons hx (ZZ_cons hy ZZ_nil)
  have hchain : pderiv v (ev b f) =
      ∑ p : Fin 2 × Fin d, ev b (pderiv p f) * pderiv v (b p.1 p.2) :=
    prove_cb_ev_chain_rule R b hb f v
  change pderiv v (ev b f) = _
  rw [hchain, Fintype.sum_prod_type, Fin.sum_univ_two]
  rfl

theorem d3 {x y z : Pt R n d} (hx : Z x) (hy : Z y) (hz : Z z) (f : PS R 3 d) (v : Fin n × Fin d) :
    pderiv v (ev ![x, y, z] f) = ∑ c, ev ![x, y, z] (pderiv ((0 : Fin 3), c) f) * pderiv v (x c) +
      ∑ c, ev ![x, y, z] (pderiv ((1 : Fin 3), c) f) * pderiv v (y c) +
      ∑ c, ev ![x, y, z] (pderiv ((2 : Fin 3), c) f) * pderiv v (z c) := by
  let b : Fin 3 → Pt R n d := ![x, y, z]
  have hb : ZZ b := ZZ_cons hx (ZZ_cons hy (ZZ_cons hz ZZ_nil))
  have hchain : pderiv v (ev b f) =
      ∑ p : Fin 3 × Fin d, ev b (pderiv p f) * pderiv v (b p.1 p.2) :=
    prove_cb_ev_chain_rule R b hb f v
  change pderiv v (ev b f) = _
  rw [hchain, Fintype.sum_prod_type, Fin.sum_univ_three]
  rfl

end ChainRule

theorem dmul (v : Fin n × Fin d) (f g : PS R n d) :
    pderiv (R := R) v (f * g) = pderiv (R := R) v f * g + f * pderiv (R := R) v g := by
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]; ring

theorem cc_pderiv (f : PS R n d) (v : Fin n × Fin d) :
    constantCoeff (pderiv (R := R) v f) = coeff (Finsupp.single v 1) f := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_pderiv, zero_add]
  simp

theorem coeff_lin_ev {φ : Pt R 1 d} (hφ : Z φ) (f : PS R 1 d) (j : Fin d) :
    coeff (Finsupp.single ((0 : Fin 1), j) 1) (ev ![φ] f) =
      ∑ c, coeff (Finsupp.single ((0 : Fin 1), c) 1) f * lin φ 1 c j := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← cc_pderiv, d1 hφ, map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_mul, ccev (ZZ_cons hφ ZZ_nil), cc_pderiv, cc_pderiv, lin]

theorem lin_add (G : FGLaw R d) {φ ψ : Pt R 1 d} (hφ : Z φ) (hψ : Z ψ) :
    lin (G.add φ ψ) 1 = lin φ 1 + lin ψ 1 := by
  ext i j
  have h0 : ∀ c, constantCoeff (pderiv (R := R) ((0 : Fin 2), c) (G.F i)) = if i = c then 1 else 0 := fun c => by
    have he := congrFun (p_add_zero G (Z_pt (R := R) (d := d) (0 : Fin 1))) i
    change ev ![pt R d (0 : Fin 1), 0] (G.F i) = pt R d (0 : Fin 1) i at he
    have hd := congrArg (pderiv (R := R) ((0 : Fin 1), c)) he
    rw [d2 (Z_pt 0) Z_zero, dpt] at hd
    simp [dpt, Prod.mk.injEq] at hd
    have hc := congrArg constantCoeff hd
    rw [ccev (ZZ_cons (Z_pt 0) (ZZ_cons Z_zero ZZ_nil))] at hc
    rw [hc]
    split_ifs <;> simp
  have h1 : ∀ c, constantCoeff (pderiv (R := R) ((1 : Fin 2), c) (G.F i)) = if i = c then 1 else 0 := fun c => by
    have he : ev ![0, pt R d (0 : Fin 1)] (G.F i) = pt R d (0 : Fin 1) i := G.unit i
    have hd := congrArg (pderiv (R := R) ((0 : Fin 1), c)) he
    rw [d2 Z_zero (Z_pt 0), dpt] at hd
    simp [dpt, Prod.mk.injEq] at hd
    have hc := congrArg constantCoeff hd
    rw [ccev (ZZ_cons Z_zero (ZZ_cons (Z_pt 0) ZZ_nil))] at hc
    rw [hc]
    split_ifs <;> simp
  change coeff _ (ev ![φ, ψ] (G.F i)) = _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← cc_pderiv, d2 hφ hψ, map_add (f := _), map_sum, map_sum]
  simp only [map_mul, ccev (ZZ_cons hφ (ZZ_cons hψ ZZ_nil)), h0, h1]
  simp [cc_pderiv, lin]

section Act

variable {G : FGLaw R d} {O : Type} [CommRing O] (A : OAct O G)

theorem lin_act_zero : lin (A.act 0) 1 = 0 := by
  have h := congrArg (fun φ => lin φ 1) (A.add_act 0 0)
  simp only [add_zero, lin_add G (Z_act A 0) (Z_act A 0)] at h
  simpa using h

theorem lin_act_nat (k : ℕ) : lin (A.act (k : O)) 1 = k • (1 : Matrix (Fin d) (Fin d) R) := by
  induction k with
  | zero => simpa using lin_act_zero A
  | succ k ih =>
    rw [Nat.cast_succ, A.add_act, lin_add G (Z_act A _) (Z_act A _), ih, A.one_act,
      lin_pt_eq_one, succ_nsmul]

theorem act_zero : A.act 0 = 0 := by
  have h2 : ∀ i, (2 : ℕ) ≤ (A.act 0 i).order := fun i => nat_le_order fun e he => by
    have : e.degree = 0 ∨ e.degree = 1 := by omega
    rcases this with h | h
    · rw [Finsupp.degree_eq_zero_iff] at h
      rw [h, coeff_zero_eq_constantCoeff_apply, A.const]
    · obtain ⟨⟨s, c⟩, rfl⟩ : ∃ s, e = Finsupp.single s 1 := by
        have := (Finsupp.sum_eq_one_iff e).1 (by exact h)
        exact this
      obtain rfl : s = 0 := Subsingleton.elim _ _
      exact congrFun (congrFun (lin_act_zero A) i) c
  funext i
  have h : A.act 0 i = ev ![A.act 0] (A.act 0 i) := by
    have := A.mul_act 0 0
    rw [mul_zero] at this
    exact congrFun this i
  have h3 := le_order_subst (LogPf.CZ.hasSubst (ZZ_cons (Z_act A 0) ZZ_nil)) (A.act 0 i)
  change _ ≤ (ev ![A.act 0] (A.act 0 i)).order at h3
  rw [← h] at h3
  have h4 : ((2 : ℕ) : ℕ∞) ≤ ⨅ s : Fin 1 × Fin d, ((![A.act 0] : Fin 1 → Pt R 1 d) s.1 s.2).order :=
    le_iInf fun ⟨s, c⟩ => by fin_cases s; exact h2 c
  have h5 := (mul_le_mul_left h4 _).trans h3
  have h6 := h2 i
  rw [Pi.zero_apply, ← order_eq_top_iff]
  by_contra hne
  obtain ⟨N, hN⟩ := ENat.ne_top_iff_exists.1 hne
  rw [← hN] at h5 h6
  norm_cast at h5 h6
  omega

end Act

end PositivityTheory.HtPt.Cb
