module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.Bundle0016
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle0017
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0015
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0033
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Taylor
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0034
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0033

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.AnFrameC
section
set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.AnFrameC

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
  Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj

section Form

variable {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ)

theorem hermForm_add_left (z z' w : Fin g → ℂ) :
    hermForm Hm (z + z') w = hermForm Hm z w + hermForm Hm z' w := by
  unfold hermForm
  rw [add_dotProduct]

theorem hermForm_add_right (z w w' : Fin g → ℂ) :
    hermForm Hm z (w + w') = hermForm Hm z w + hermForm Hm z w' := by
  unfold hermForm
  rw [star_add, Matrix.mulVec_add, dotProduct_add]

theorem hermForm_zero_left (w : Fin g → ℂ) : hermForm Hm 0 w = 0 := by
  unfold hermForm
  rw [zero_dotProduct]

theorem hermForm_zero_right (z : Fin g → ℂ) : hermForm Hm z 0 = 0 := by
  unfold hermForm
  rw [star_zero, Matrix.mulVec_zero, dotProduct_zero]

end Form

section Compat

variable {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ)

theorem hermForm_smul_left (c : ℂ) (z w : Fin g → ℂ) : hermForm Hm (c • z) w = c * hermForm Hm z w := by
  unfold hermForm
  rw [smul_dotProduct, smul_eq_mul]

theorem hermForm_smul_right (c : ℂ) (z w : Fin g → ℂ) :
    hermForm Hm z (c • w) = star c * hermForm Hm z w := by
  unfold hermForm
  rw [star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem real_smul_eq (r : ℝ) (z : Fin g → ℂ) : r • z = (r : ℂ) • z := by
  funext i
  simp [Complex.real_smul]

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def tyAct (ty : Fin g → (E →+* ℂ)) (a : 𝓞 E) (z : Fin g → ℂ) : Fin g → ℂ := fun i => ty i (a : E) * z i

theorem tyAct_add (ty : Fin g → (E →+* ℂ)) (a : 𝓞 E) (u v : Fin g → ℂ) :
    tyAct ty a (u + v) = tyAct ty a u + tyAct ty a v := by
  funext i
  simp only [tyAct, Pi.add_apply, mul_add]

theorem tyAct_smul (ty : Fin g → (E →+* ℂ)) (a : 𝓞 E) (c : ℂ) (u : Fin g → ℂ) :
    tyAct ty a (c • u) = c • tyAct ty a u := by
  funext i
  simp only [tyAct, Pi.smul_apply, smul_eq_mul]
  ring

theorem tyAct_zero (ty : Fin g → (E →+* ℂ)) (a : 𝓞 E) : tyAct ty a 0 = 0 := by
  funext i
  simp [tyAct]

variable {H : Host E} (D : Datum H) (ty : Fin g → (E →+* ℂ)) (P : D.La →+ (Fin g → ℂ))

theorem im_hermForm_act (hP : IsPeriod D ty P) (hc1 : ∀ x y, (hermForm Hm (P x) (P y)).im = D.EF x y)
    (a : 𝓞 E) (u v : Fin g → ℂ) :
    (hermForm Hm (tyAct ty a u) v).im = (hermForm Hm u (tyAct ty (H.bar a) v)).im := by
  have hTP : ∀ (b : 𝓞 E) x, tyAct ty b (P x) = P (b • x) := fun b x => funext fun i => (hP.1 b x i).symm
  have hspan : ∀ w : Fin g → ℂ, w ∈ Submodule.span ℝ (Set.range P) := fun w => by
    rw [hP.2.2.2.1]; trivial
  have base : ∀ x y, (hermForm Hm (tyAct ty a (P x)) (P y)).im =
      (hermForm Hm (P x) (tyAct ty (H.bar a) (P y))).im := by
    intro x y
    rw [hTP, hTP, hc1, hc1, D.adj]
  have step1 : ∀ x (w : Fin g → ℂ), (hermForm Hm (tyAct ty a (P x)) w).im =
      (hermForm Hm (P x) (tyAct ty (H.bar a) w)).im := by
    intro x w
    induction hspan w using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨y, rfl⟩ := hw
      exact base x y
    | zero => simp [tyAct_zero, hermForm_zero_right]
    | add w w' _ _ h1 h2 =>
      rw [hermForm_add_right, tyAct_add, hermForm_add_right, Complex.add_im, Complex.add_im, h1, h2]
    | smul r w _ h =>
      rw [real_smul_eq, hermForm_smul_right, tyAct_smul, hermForm_smul_right, Complex.mul_im, Complex.mul_im, h]
      simp
  induction hspan u using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨x, rfl⟩ := hu
    exact step1 x v
  | zero => simp [tyAct_zero, hermForm_zero_left]
  | add u u' _ _ h1 h2 =>
    rw [tyAct_add, hermForm_add_left, hermForm_add_left, Complex.add_im, Complex.add_im, h1, h2]
  | smul r u _ h =>
    rw [real_smul_eq, tyAct_smul, hermForm_smul_left, hermForm_smul_left, Complex.mul_im, Complex.mul_im, h]
    simp

theorem hermForm_act (hP : IsPeriod D ty P) (hc1 : ∀ x y, (hermForm Hm (P x) (P y)).im = D.EF x y)
    (a : 𝓞 E) (u v : Fin g → ℂ) :
    hermForm Hm (tyAct ty a u) v = hermForm Hm u (tyAct ty (H.bar a) v) := by
  apply Complex.ext
  · have h := im_hermForm_act Hm D ty P hP hc1 a (Complex.I • u) v
    rw [tyAct_smul, hermForm_smul_left, hermForm_smul_left, Complex.mul_im, Complex.mul_im] at h
    simpa using h
  · exact im_hermForm_act Hm D ty P hP hc1 a u v

end Compat

section Frame

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

end Frame

end ReciprocityTheory.ChartRestriction.G.PullbackSections.AnFrameC
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ChartValJ
section
noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf

section Letters

variable {T : Type} [Fintype T] (rr : T → ℕ) (n : ℕ)

def colL (m : Formalism.L2.Pj.Letter T rr n →₀ ℕ) (b : Fin n) : (Σ τ : T, Fin (rr τ)) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun ℓ => m ⟨ℓ.1, ℓ.2, b⟩

theorem colM_lEq_colL (m : Formalism.L2.Pj.Letter T rr n →₀ ℕ) (b : Fin n) :
    colM (m.mapDomain (CVA.lEq (T := T) (r := rr) (n := n))) b = colL rr n m b := by
  ext ℓ
  show Finsupp.mapDomain CVA.lEq m (CVA.lEq ⟨ℓ.1, ℓ.2, b⟩) = m ⟨ℓ.1, ℓ.2, b⟩
  rw [Finsupp.mapDomain_apply_of_injective CVA.lEq.injective]

end Letters

section Main

variable {R k : Type} [CommRing R] [Field k] [Algebra ℚ k] [Algebra R k]

set_option maxHeartbeats 1000000 in
theorem chartValJ (hRQ : IsRQ (R := R) k) (J : Submodule R k) (hJ1 : (1 : k) ∈ J)
    {d : ℕ} {O : Type} [CommRing O] [StarRing O] (B : FB R d O) (h : PS k 2 d) (hg : B.IsCanonGauge k h)
    (w0 : O) (hw0 : w0 + star w0 = 1) (m : ℕ)
    {T : Type} [Fintype T] (rr : T → ℕ) (cc : T → T) (hcc : ∀ τ, cc (cc τ) = τ) (isX : T → Prop)
    (hX : ∀ τ, isX τ ∨ isX (cc τ))
    {π : Type} [Fintype π] [DecidableEq π] (c : T → π) (s : T → Bool)
    (hcs : ∀ τ, c (cc τ) = c τ ∧ s (cc τ) ≠ s τ)
    (u φ : (Σ τ : T, Fin (rr τ)) → Fin d → R) (ψ : (Σ τ : T, Fin (rr τ)) → Fin d → k) (hψ : ∀ ℓ i, ψ ℓ i ∈ J)
    (heig : ∀ ℓ ℓ' : (Σ τ : T, Fin (rr τ)), ℓ'.1 ≠ cc ℓ.1 →
      ∑ i, (algebraMap R k (φ ℓ' i) + ψ ℓ' i - (sg1 k h).mulVec (fun j => algebraMap R k (u ℓ' j)) i) *
        algebraMap R k (u ℓ i) = 0)
    (h21a : OppositePairVanishing k (fun ℓ : (Σ τ : T, Fin (rr τ)) => c ℓ.1) (fun ℓ => s ℓ.1)
      (fun ℓ => ((fun j => algebraMap R k (u ℓ j)),
        fun i => algebraMap R k (φ ℓ i) - (sg1 k h).mulVec (fun j => algebraMap R k (u ℓ j)) i))
      (fun ℓ => ((fun j => algebraMap R k (u ℓ j)),
        fun i => algebraMap R k (φ ℓ i) - (sg1 k h).mulVec (fun j => algebraMap R k (u ℓ j)) i)))
    (h21b : OppositePairVanishing k (fun ℓ : (Σ τ : T, Fin (rr τ)) => c ℓ.1) (fun ℓ => s ℓ.1) (fun ℓ => (0, ψ ℓ))
      (fun ℓ => ((fun j => algebraMap R k (u ℓ j)),
        fun i => algebraMap R k (φ ℓ i) - (sg1 k h).mulVec (fun j => algebraMap R k (u ℓ j)) i)))
    (h21c : OppositePairVanishing k (fun ℓ : (Σ τ : T, Fin (rr τ)) => c ℓ.1) (fun ℓ => s ℓ.1)
      (fun ℓ => ((fun j => algebraMap R k (u ℓ j)),
        fun i => algebraMap R k (φ ℓ i) - (sg1 k h).mulVec (fun j => algebraMap R k (u ℓ j)) i))
      (fun ℓ => (0, ψ ℓ)))
    (n : ℕ) (a : T → ℕ → ℕ) (P : MvPolynomial (Formalism.L2.Pj.Letter T rr n) k)
    (hP : P ∈ Formalism.L2.Pj.HaO rr n k (algebraMap R k).range cc isX a)
    (e : ℕ) (he : ∀ mo ∈ P.support, ∑ b, pairMin (fun ℓ : (Σ τ : T, Fin (rr τ)) => c ℓ.1) (fun ℓ => s ℓ.1)
      (colL rr n mo b) ≤ e)
    (f : Fin n → PS k 1 d) (hf : ∀ b, IntAA (R := R) k (f b)) :
    ∑ mo ∈ P.support, P.coeff mo * ∏ b, B.nabVal k h w0 m (f b) (fun ℓ j => algebraMap R k (u ℓ j))
      (MvPolynomial.monomial (colL rr n mo b) 1) ∈ J ^ e := by
  classical
  set uK : (Σ τ : T, Fin (rr τ)) → Fin d → k := fun ℓ j => algebraMap R k (u ℓ j) with huK
  set φK : (Σ τ : T, Fin (rr τ)) → Fin d → k :=
    fun ℓ i => algebraMap R k (φ ℓ i) + ψ ℓ i - (sg1 k h).mulVec (uK ℓ) i with hφK
  set g : Fin n → PS k 1 d := fun b => FB.expS k ((m : k) • B.hL k h w0) * f b with hgdef
  set P2 := MvPolynomial.rename (CVA.lEq (T := T) (r := rr) (n := n)) P with hP2

  have hvan : ∀ ℓ ℓ' : (Σ τ : T, Fin (rr τ)), ℓ'.1 ≠ cc ℓ.1 → ∑ i, φK ℓ' i * uK ℓ i = 0 := fun ℓ ℓ' hne => heig ℓ ℓ' hne
  have hpair : ∀ ℓ ℓ' : (Σ τ : T, Fin (rr τ)), ℓ'.1 = cc ℓ.1 → (c ℓ.1 = c ℓ'.1 ∧ s ℓ.1 ≠ s ℓ'.1) := by
    intro ℓ ℓ' he'
    rw [he']
    exact ⟨(hcs ℓ.1).1.symm, (hcs ℓ.1).2.symm⟩
  have hL1 : OppositePairVanishing k (fun ℓ : (Σ τ : T, Fin (rr τ)) => c ℓ.1) (fun ℓ => s ℓ.1) (fun ℓ => (uK ℓ, 0))
      (fun ℓ => (uK ℓ, 0)) := by
    intro l l' _
    simp [betaH]
  have hL2 : OppositePairVanishing k (fun ℓ : (Σ τ : T, Fin (rr τ)) => c ℓ.1) (fun ℓ => s ℓ.1) (fun ℓ => (uK ℓ, 0))
      (fun ℓ => (0, φK ℓ)) := by
    intro l l' hnot
    by_cases hl : l'.1 = cc l.1
    · exact absurd (hpair l l' hl) hnot
    · simp only [betaH, Pi.zero_apply, zero_mul, sub_zero]
      exact hvan l l' hl
  have hL3 : OppositePairVanishing k (fun ℓ : (Σ τ : T, Fin (rr τ)) => c ℓ.1) (fun ℓ => s ℓ.1) (fun ℓ => (0, φK ℓ))
      (fun ℓ => (uK ℓ, 0)) := by
    intro l l' hnot
    by_cases hl : l.1 = cc l'.1
    · exfalso
      apply hnot
      have := hpair l' l hl
      exact ⟨this.1.symm, this.2.symm⟩
    · simp only [betaH, Pi.zero_apply, mul_zero, zero_sub, Finset.sum_neg_distrib, neg_eq_zero]
      exact hvan l' l hl

  have hharm := CVA.harm_rename (r := rr) (n := n) cc isX P hP.1.1

  set cfun : (Σ τ : T, Fin (rr τ)) → (Σ τ : T, Fin (rr τ)) → k := fun l l' =>
    if c l.1 = c l'.1 ∧ s l.1 = true ∧ s l'.1 = false then (m : k) * betaH k (0, φK l) (uK l', 0) else 0
    with hcfun
  have hcvan : ∀ l l' : (Σ τ : T, Fin (rr τ)), l'.1 ≠ cc l.1 → cfun l l' = 0 := by
    intro l l' hne
    have hne' : l.1 ≠ cc l'.1 := fun h' => hne (by rw [h', hcc])
    have hz : betaH k (0, φK l) (uK l', 0) = 0 := by
      simp only [betaH, Pi.zero_apply, mul_zero, zero_sub, Finset.sum_neg_distrib, neg_eq_zero]
      exact hvan l' l hne'
    simp only [hcfun, hz, mul_zero, ite_self]
  have hso := harmSecond_holds k T rr cc isX hcc hX n cfun hcvan P2 hharm
  have hfun : (fun p q : (Σ τ : T, Fin (rr τ)) × Fin n =>
      if p.2 = q.2 ∧ c p.1.1 = c q.1.1 ∧ s p.1.1 = true ∧ s q.1.1 = false then
        (m : k) * betaH k (0, φK p.1) (uK q.1, 0) else 0) =
      (fun p q : (Σ τ : T, Fin (rr τ)) × Fin n => if p.2 = q.2 then cfun p.1 q.1 else 0) := by
    funext p q
    by_cases h1 : p.2 = q.2 <;> simp [h1, hcfun]
  have hso' : secondOrder k (fun p q : (Σ τ : T, Fin (rr τ)) × Fin n =>
      if p.2 = q.2 ∧ c p.1.1 = c q.1.1 ∧ s p.1.1 = true ∧ s q.1.1 = false then
        (m : k) * betaH k (0, φK p.1) (uK q.1, 0) else 0) P2 = 0 := by
    rw [hfun]
    exact hso

  have hLH := TB.WickVanishing.Closed.lemma_H_columns R d O k B h hg.ax0 m (Σ τ : T, Fin (rr τ)) π (fun ℓ => c ℓ.1) (fun ℓ => s ℓ.1)
    uK φK hL1 hL2 hL3 n P2 hso' g

  set ξh : (Σ τ : T, Fin (rr τ)) → (Fin d → k) × (Fin d → k) := fun ℓ => ((fun j => algebraMap R k (u ℓ j)),
      fun i => algebraMap R k (φ ℓ i) - (sg1 k h).mulVec (fun j => algebraMap R k (u ℓ j)) i) with hξh
  have hxi : (fun ℓ => ξh ℓ + ((0 : Fin d → k), ψ ℓ)) = fun ℓ => (uK ℓ, φK ℓ) := by
    funext ℓ
    refine Prod.ext ?_ ?_
    · funext j
      simp [hξh, huK]
    · funext i
      simp only [hξh, Prod.snd_add, Pi.add_apply, hφK, huK]
      ring
  have he2 : ∀ mo ∈ P2.support, ∑ b, pairMin (fun ℓ : (Σ τ : T, Fin (rr τ)) => c ℓ.1) (fun ℓ => s ℓ.1)
      (colM mo b) ≤ e := by
    intro mo hmo
    rw [hP2, MvPolynomial.support_rename_of_injective CVA.lEq.injective] at hmo
    obtain ⟨mo0, hmo0, rfl⟩ := Finset.mem_image.1 hmo
    simp only [colM_lEq_colL]
    exact he mo0 hmo0
  have hSC := TB.WickVanishing.Closed.scaled_connection_columns R d O k hRQ J hJ1 B h hg w0 hw0 m (Σ τ : T, Fin (rr τ)) π (fun ℓ => c ℓ.1)
    (fun ℓ => s ℓ.1) ξh ψ (fun ℓ => ⟨u ℓ, φ ℓ, rfl⟩) hψ h21a h21b h21c n P2
    (CVA.coeff_rename_mem _ P hP.2) e he2 f hf
  rw [hxi] at hSC
  have hchain : ∑ mo ∈ P.support, P.coeff mo * ∏ b, B.nabVal k h w0 m (f b) uK
      (MvPolynomial.monomial (colL rr n mo b) 1) =
      ∑ mo ∈ P2.support, P2.coeff mo * ∏ b, constantCoeff (ordNabla k B h m (fun ℓ => s ℓ.1)
        (fun ℓ => (uK ℓ, φK ℓ)) (MvPolynomial.monomial (colM mo b) 1) (liftX k (g b))) := by
    rw [hLH, hP2, CVA.sum_rename]
    refine Finset.sum_congr rfl fun mo _ => ?_
    congr 1
    refine Finset.prod_congr rfl fun b _ => ?_
    rw [colM_lEq_colL]
    simp only [FB.nabVal, hgdef]
    rw [mul_comm]
  rw [hchain]
  have hg' : g = fun b => FB.expS k ((m : k) • B.hL k h w0) * f b := hgdef
  rw [hg']
  exact hSC

end Main

end ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ExistsBorelOrthonormalMove
section
set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField Complex ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

section Frames

variable {r : ℕ} (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r)

theorem diagonal_minor_orthonormal {x : Frame X.Ψ r} (hx : X.IsOrtho x) (τ : X.Ψ) (i : Fin (r + 1)) :
    dmin X.Gm x τ i = ((psgn X.p0 i : ℝ) : ℂ) := by
  unfold dmin
  rw [hx τ, ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.lminor_diagonal]
  simp [psgn, Finset.prod_range]

theorem norm_diagonal_minor_one {x : Frame X.Ψ r} (hx : X.IsOrtho x) (τ : X.Ψ) (i : Fin (r + 1)) :
    ‖dmin X.Gm x τ i‖ = 1 := by
  rw [diagonal_minor_orthonormal X hx, Complex.norm_real, Real.norm_eq_abs]
  unfold psgn
  rw [Finset.abs_prod]
  apply Finset.prod_eq_one
  intro a _
  unfold sgn
  split_ifs <;> simp

theorem exists_borel_orthonormal_move {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    ∃ b ∈ Bor X.Ψ r, rmul x b ∈ X.dom ∧ X.IsOrtho (rmul x b) := by
  refine ⟨ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x, ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf_mem X hx, fun τ => ⟨?_, fun i => ?_⟩,
    ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.ortho_bOf X hx⟩
  · show (mat x τ * mat (ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x) τ).det ≠ 0
    rw [Matrix.det_mul]
    exact mul_ne_zero (hx τ).1 ((ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf_mem X hx) τ).1
  · rw [diagonal_minor_orthonormal X (ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.ortho_bOf X hx) τ i, Complex.ofReal_re]
    have h : psgn X.p0 i ≠ 0 := by
      unfold psgn
      rw [Finset.prod_ne_zero_iff]
      intro a _
      unfold sgn
      split_ifs <;> norm_num
    exact mul_self_pos.2 h

end Frames

section Act

variable {dim : (E →+* ℂ) → ℕ}

end Act

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.TaylorPSEqTay
section
set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open scoped ContDiff

theorem expS_zero' (k : Type) [CommRing k] [Algebra ℚ k] {n d : ℕ} : FB.expS k (0 : PS k n d) = 1 := by
  unfold FB.expS
  have ha : PowerSeries.HasSubst (0 : PS k n d) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (by simp)
  have h0 : PowerSeries.constantCoeff (PowerSeries.exp k - 1) = 0 := by
    rw [map_sub, PowerSeries.constantCoeff_exp, map_one, sub_self]
  have e : PowerSeries.exp k = 1 + (PowerSeries.exp k - 1) := by ring
  rw [e, ← PowerSeries.coe_substAlgHom ha, map_add (f := _), map_one, PowerSeries.coe_substAlgHom ha,
    PowerSeries.subst_zero_of_constantCoeff_zero h0, add_zero]

private theorem hL0_lemma {d : ℕ} {O : Type} [CommRing O] [StarRing O] (B : FB ℂ d O) (w0 : O) :
    B.hL ℂ 0 w0 = 0 := by
  unfold FB.hL
  unfold ev
  simp [MvPowerSeries.subst, MvPowerSeries.eval₂]

theorem nabVal_additive {d : ℕ} {O : Type} [CommRing O] [StarRing O] (B : FB ℂ d O)
    (hF : ∀ i, B.G.F i = addF ℂ d i) (w0 : O) (m : ℕ) {θ : (Fin d → ℂ) → ℂ} (hθ : ContDiffAt ℂ ω θ 0)
    {ι : Type} [Fintype ι] (u : ι → Fin d → ℂ) (P : MvPolynomial ι ℂ) :
    B.nabVal ℂ 0 w0 m (tay θ 0) u P = ReciprocityTheory.ChartRestriction.G.I2.polyDeriv P u θ 0 := by
  have hL0 : B.hL ℂ 0 w0 = 0 := hL0_lemma B w0
  have hK : B.FK ℂ = addF ℂ d := by
    funext i
    unfold FB.FK
    unfold FGLaw.mapF
    simp [hF]
  rw [FB.nabVal, hL0, smul_zero, expS_zero', mul_one, hK]
  exact constantCoeff_dpolyOf_tay hθ u P

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ThcAssembly
section
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj

theorem Thc_le_Mlat {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : WeightAlgebra.PJ D B P j) (s : 𝓞 B.KO)
    (w : WeightFamilies.Wt D j)
    (hb : ∀ G ∈ X.shortTh w, ∀ la (y : X.Pt la),
      (((-(((vAdd la ((s * ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 B.KO) ^ (D.R.f * D.R.r * w.n) : 𝓞 B.KO) :
        B.KO) : ℤ) : ℝ))) : ℝ) : EReal) ≤ X.vAt la y (X.inc w G)) :
    X.Thc s w ≤ B.Mlat j w := by
  intro x hx
  simp only [Formalism.MainNotions.WeightAlgebra.PJ.Thc, Formalism.MainNotions.WeightAlgebra.PJ.scaled, Submodule.mem_map] at hx
  obtain ⟨x', ⟨G, hG, rfl⟩, rfl⟩ := hx
  rw [X.Mlat_eq]
  intro la y
  have hne := X.vAt_ne_bot la y (X.inc w G)
  have key : ∀ t : 𝓞 B.KO, ((-(((vAdd la (t : B.KO) : ℤ) : ℝ)) : ℝ) : EReal) ≤ X.vAt la y (X.inc w G) →
      0 ≤ X.vAt la y (X.inc w (t • G)) := by
    intro t hb'
    have e : algebraMap (𝓞 B.KO) B.KO t = (t : B.KO) := rfl
    rw [← algebraMap_smul B.KO t G, map_smul, e]
    by_cases h0 : (t : B.KO) = 0
    · rw [h0, zero_smul, X.vAt_zero]
      exact le_top
    rw [X.vAt_smul la y _ _ h0]
    generalize X.vAt la y (X.inc w G) = V at hb' hne ⊢
    induction V using EReal.rec with
    | bot => exact absurd rfl hne
    | coe v =>
      rw [← EReal.coe_add]
      have h1 := EReal.coe_le_coe_iff.mp hb'
      exact EReal.coe_nonneg.mpr (by linarith)
    | top => simp
  have hb' := hb G hG la y
  simp only [LinearMap.smul_apply, LinearMap.id_apply, smul_smul]
  exact key _ hb'

end ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf
end
end

