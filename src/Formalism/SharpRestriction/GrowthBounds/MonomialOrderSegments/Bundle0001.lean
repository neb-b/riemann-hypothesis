module

public import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.MemPolKIff

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.CollapseExponent
section
noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.PlaneGram

namespace TwistData

variable {K : Type} [Field K] (D : TwistData K)

abbrev EA := D.OL × Fin D.r →₀ ℕ

abbrev EM := D.ML × Fin D.r →₀ ℕ

def collapseExponent (p : ℕ) (ζ : D.EM) : D.EA :=
  Finsupp.equivFunOnFinite.symm fun x => Sum.elim (fun b => ζ (D.mb b, x.2))
    (fun t => ζ (D.mlab t, x.2) + D.P p t * ζ (D.mw t, x.2)) x.1

def tpE (ζ : D.EM) : D.EA :=
  Finsupp.equivFunOnFinite.symm fun x => Sum.elim (fun _ => 0) (fun t => ζ (D.mtp t, x.2)) x.1

def phE (p : ℕ) (ζ : D.EM) : D.EA := D.collapseExponent p ζ + D.tpE ζ

def GoodE (p : ℕ) (ζ : D.EM) : Prop :=
  (∀ t a, ζ (D.mlab t, a) < D.P p t) ∧
  (∀ (j : Fin D.J) (m : Fin D.r), m.val = 0 → ∀ a, ζ (D.mtp (j, m), a) = 0) ∧
  (∀ b, ldeg ζ (D.mb b) = D.dB b) ∧
  (∀ t, ldeg ζ (D.mlab t) + D.P p t * ldeg ζ (D.mw t) + ldeg ζ (D.mtp t) = D.dT t) ∧
  (∀ t : D.Tau, ldeg ζ (D.mtp t) ≤ D.dLL t.1)

def Good (p : ℕ) (Z : MvPolynomial (D.ML × Fin D.r) K) : Prop := ∀ ζ ∈ Z.support, D.GoodE p ζ

def abelian₂ (p : ℕ) (F : MvPolynomial (D.OL × Fin D.r) K) (Z : MvPolynomial (D.ML × Fin D.r) K) : K :=
  fock F (D.gaAct (D.ph p Z))

def labF (ζ : D.EM) (t : D.Tau) : Fin D.r → ℕ := fun a => ζ (D.mlab t, a)

def wF (ζ : D.EM) (t : D.Tau) : Fin D.r → ℕ := fun a => ζ (D.mw t, a)

def LabLowE (p : ℕ) (ζ : D.EM) : Prop := ∀ t a, ζ (D.mlab t, a) < D.P p t

def DigOK (v : AddValuation K (WithTop ℚ)) (p : ℕ) (cst : D.Tau → (Fin D.r → ℕ) → ℕ → K)
    (gam : D.Tau → (Fin D.r → ℕ) → (Fin D.r → ℕ) → K) : Prop :=
  (∀ (t : D.Tau) (ρ : Fin D.r → ℕ), (∀ a, ρ a < D.P p t) →
    (∀ n, cst t ρ n ≠ 0) ∧
    (∀ β : Fin D.r → ℕ, v (gam t ρ β) = 0 ∧
      ((∏ a, (ρ a + D.P p t * β a).factorial : ℕ) : K) =
        cst t ρ (∑ a, β a) * ((∏ a, (β a).factorial : ℕ) : K) * gam t ρ β)) ∧
  ∀ ρ : D.Tau → Fin D.r → ℕ, (∀ t a, ρ t a < D.P p t) → ∀ ε : ℤ, (ε = 1 ∨ ε = -1) →
    ∃ (T : Finset (D.Tau × Fin D.r → ℕ)) (lam : (D.Tau × Fin D.r → ℕ) → K),
      (∀ m ∈ T, 0 ≤ v (lam m) ∧ ∑ x, m x ≤ 6 * D.c) ∧
      ∀ β : D.Tau × Fin D.r → ℕ, ((D.c : ℕ) : WithTop ℚ) ≤
        v ((∏ t, gam t (ρ t) (fun a => β (t, a))) ^ ε - binomComb T lam β)

def gaP (p : ℕ) (gam : D.Tau → (Fin D.r → ℕ) → (Fin D.r → ℕ) → K) (ζ : D.EM) : K :=
  D.ga (D.collapseExponent p ζ) * ∏ t, gam t (D.labF ζ t) (D.wF ζ t)

end TwistData

section Steps

variable (K : Type) [Field K] [CharZero K] (v : AddValuation K (WithTop ℚ)) (p : ℕ) (C0 : ℝ)

def StepB : Prop :=
  DVRHyp v p → ∀ D : TwistData K, D.Valid v p → D.Hc p C0 →
    ∀ F : MvPolynomial (D.OL × Fin D.r) K, D.InXX p F → vBB v F = 0 →
      ∃ Gt : MvPolynomial (D.OL × Fin D.r) K, Gt ∈ PolO v D.r D.dO ∧
        (∀ (j : Fin D.J) (m : Fin D.r), m.val + 2 ≤ D.r →
          vala D.osg (D.Tset j m) (D.thl j m - 6 * D.c) Gt) ∧
        vle v (D.n0 v + D.Dl p C0 + 1) (fock F (D.gaAct Gt))

def StepC : Prop :=
  DVRHyp v p → ∀ D : TwistData K, 0 < D.r → 0 < D.J → ∀ (θ : Fin D.J → Fin D.r → ℝ)
    (Gt : MvPolynomial (D.OL × Fin D.r) K), Gt ∈ PolO v D.r D.dO →
      (∀ (j : Fin D.J) (m : Fin D.r), m.val + 2 ≤ D.r → vala D.osg (D.Tset j m) (θ j m) Gt) →
      ∃ Z : MvPolynomial (D.ML × Fin D.r) K, Integral v Z ∧ D.Good p Z ∧ D.ph p Z = Gt ∧
        ∀ (j : Fin D.J) (m : Fin D.r), m.val + 2 ≤ D.r → vala D.msg (D.Yset j m) (θ j m) Z

def StepBC : Prop :=
  DVRHyp v p → ∀ D : TwistData K, D.Valid v p → D.Hc p C0 →
    ∀ F : MvPolynomial (D.OL × Fin D.r) K, D.InXX p F → vBB v F = 0 →
      ∃ Z : MvPolynomial (D.ML × Fin D.r) K, Integral v Z ∧ D.Good p Z ∧
        (∀ (j : Fin D.J) (m : Fin D.r), m.val + 2 ≤ D.r →
          vala D.msg (D.Yset j m) (D.thl j m - 6 * D.c) Z) ∧
        vle v (D.n0 v + D.Dl p C0 + 1) (D.abelian₂ p F Z)

def StepDEF : Prop :=
  DVRHyp v p → ∀ D : TwistData K, D.Valid v p → D.HypH p 13 → D.Hc p C0 →
    ∀ F : MvPolynomial (D.OL × Fin D.r) K, D.InXX p F → vBB v F = 0 →
      ∃ (Ω : MvPolynomial (D.ML × Fin D.r) K →ₗ[K] MvPolynomial (D.ML × Fin D.r) K) (N2 : ℕ),
        (N2 : ℝ) ≤ D.Dm p C0 + D.kapD p / 2 + 1 ∧
        (∀ Z, Integral v Z → D.Good p Z → Integral v (((p : K) ^ N2) • Ω Z)) ∧
        (∀ Z, D.Good p Z → D.Good p (Ω Z)) ∧
        (∀ Z, D.Good p Z → ∀ (j : Fin D.J) (i : Fin (D.nch j)),
          vala D.msg (D.chainSet j i) (D.th j i - D.sl j i - 12 * D.c) (Ω Z)) ∧
        (∀ Z, D.Good p Z → ∀ (j : Fin D.J) (m : Fin D.r) (θ : ℝ), m.val + 2 ≤ D.r →
          vala D.msg (D.Yset j m) θ Z → vala D.msg (D.Yset j m) (θ - 24 * D.c) (Ω Z)) ∧
        (∀ Z, Integral v Z → D.Good p Z →
          vge v (D.c + D.n0 v - 2 * D.kapD p - D.Dm p C0) (D.abelian₂ p F (Ω Z) - D.abelian₂ p F Z))

def StepG : Prop :=
  DVRHyp v p → ∀ D : TwistData K, D.Valid v p → ∀ cst gam, D.DigOK v p cst gam →
    ∃ gp gm : D.EM → K, (∀ ζ, 0 ≤ v (gp ζ)) ∧ (∀ ζ, 0 ≤ v (gm ζ)) ∧
      (∀ ζ, D.LabLowE p ζ → ((D.c : ℕ) : WithTop ℚ) ≤ v (gp ζ - D.gaP p gam ζ) ∧
        ((D.c : ℕ) : WithTop ℚ) ≤ v (gm ζ - (D.gaP p gam ζ)⁻¹)) ∧
      ∀ S : Finset D.ML, (∀ t, D.mlab t ∉ S) → ∀ (θ : ℝ) (Z : MvPolynomial (D.ML × Fin D.r) K),
        vala D.msg S θ Z → vala D.msg S (θ - 12 * D.c) (dg gp Z) ∧ vala D.msg S (θ - 12 * D.c) (dg gm Z)

def StepP : Prop :=
  DVRHyp v p → ∀ D : TwistData K, D.Valid v p →
    ∃ Pj : MvPolynomial (D.ML × Fin D.r) K →ₗ[K] MvPolynomial (D.ML × Fin D.r) K,
      (∀ ζ ζ' : D.EM, ζ' ∈ (Pj (monomial ζ 1)).support → (∀ i, ldeg ζ' i = ldeg ζ i) ∧
        (∀ t a, ζ' (D.mlab t, a) = ζ (D.mlab t, a)) ∧ (∀ t a, ζ' (D.mtp t, a) = ζ (D.mtp t, a))) ∧
      (∀ ζ : D.EM, D.GoodE p ζ → bge v (vN v (fact ζ) / 2 - D.Dm p C0) (Pj (monomial ζ 1))) ∧
      (∀ Z (j : Fin D.J) (i : Fin (D.nch j)), vala D.msg (D.chainSet j i) (D.th j i - D.sl j i) (Pj Z)) ∧
      (∀ (A : MvPolynomial (D.ML × Fin D.r) K) (ζ : D.EM), A ∈ PolK K D.r (fun i => ldeg ζ i) →
        (∀ (j : Fin D.J) (i : Fin (D.nch j)), vala D.msg (D.chainSet j i) (D.th j i - D.sl j i) A) →
        fock A (Pj (monomial ζ 1)) = fock A (monomial ζ 1)) ∧
      (∀ (j : Fin D.J) (m : Fin D.r) (θ : ℝ) Z, vala D.msg (D.Yset j m) θ Z → vala D.msg (D.Yset j m) θ (Pj Z))

def StepE : Prop :=
  DVRHyp v p → ∀ D : TwistData K, D.Valid v p → D.HypH p 13 →
    ∀ F : MvPolynomial (D.OL × Fin D.r) K, D.InXX p F → bge v 0 F →
      ∀ M : D.EA, (∀ b a, M (Sum.inl b, a) = 0) → (∀ t : D.Tau, ldeg M (Sum.inr t) ≤ D.dLL t.1) →
        ∀ ρ : D.Tau → Fin D.r → ℕ, ∃ Q0 E : MvPolynomial (D.ML × Fin D.r) K,
          D.digitPart p ρ (dg (fun α => (D.ga α)⁻¹) (ddiv M (D.gaAct F))) = Q0 + E ∧
          (∀ (j : Fin D.J) (i : Fin (D.nch j)), vala D.msg (D.chainSet j i) (D.th j i - D.sl j i) Q0) ∧
          cge v (D.c - D.n0 v) E

end Steps

end Formalism.MainNotions.PlaneGram
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.ExistsMonomialOrder
section
noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.PlaneGram

variable {K : Type} [Field K] (v : AddValuation K (WithTop ℚ))

def vG {σ : Type} (F : MvPolynomial σ K) : WithTop ℚ := F.support.inf fun α => v (F.coeff α)

variable {v}
variable {σ τ : Type}

theorem le_vG_iff (F : MvPolynomial σ K) (n : WithTop ℚ) :
    n ≤ vG v F ↔ ∀ α, n ≤ v (F.coeff α) := by
  unfold vG
  rw [Finset.le_inf_iff]
  constructor
  · intro h α
    by_cases hα : α ∈ F.support
    · exact h α hα
    · rw [notMem_support_iff.mp hα, AddValuation.map_zero]; exact le_top
  · intro h α _; exact h α

theorem vG_le_coeff (F : MvPolynomial σ K) (α : σ →₀ ℕ) : vG v F ≤ v (F.coeff α) :=
  (le_vG_iff F _).mp le_rfl α

theorem integral_iff (F : MvPolynomial σ K) : Integral v F ↔ 0 ≤ vG v F :=
  (le_vG_iff F 0).symm

theorem vG_zero : vG v (0 : MvPolynomial σ K) = ⊤ := by
  simp [vG]

theorem vG_one : vG v (1 : MvPolynomial σ K) = 0 := by
  classical
  apply le_antisymm
  · have h := vG_le_coeff (v := v) (1 : MvPolynomial σ K) 0
    simpa using h
  · rw [le_vG_iff]
    intro α
    rw [coeff_one]
    split_ifs
    · simp
    · simp

theorem exists_coeff_eq_vG (F : MvPolynomial σ K) (hF : F ≠ 0) :
    ∃ α ∈ F.support, v (F.coeff α) = vG v F := by
  have hne : F.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]; intro h; exact hF (support_eq_empty.mp h)
  obtain ⟨α, hα, h⟩ := Finset.exists_mem_eq_inf F.support hne fun α => v (F.coeff α)
  exact ⟨α, hα, h.symm⟩

theorem vG_ne_top (F : MvPolynomial σ K) (hF : F ≠ 0) : vG v F ≠ ⊤ := by
  obtain ⟨α, hα, h⟩ := exists_coeff_eq_vG (v := v) F hF
  rw [← h]
  intro ht
  exact (mem_support_iff.mp hα) ((AddValuation.top_iff v).mp ht)

theorem vG_add_vG_le_vG_mul (F G : MvPolynomial σ K) : vG v F + vG v G ≤ vG v (F * G) := by
  classical
  rw [le_vG_iff]
  intro γ
  rw [coeff_mul]
  apply AddValuation.map_le_sum
  intro x _
  rw [AddValuation.map_mul]
  exact add_le_add (vG_le_coeff F _) (vG_le_coeff G _)

theorem exists_monomialOrder (σ : Type) : Nonempty (MonomialOrder.{0, 0} σ) := by
  obtain ⟨lo, wf⟩ := exists_wellFoundedLT σ
  let _ : LinearOrder σ := @OrderDual.instLinearOrder σ lo
  have : WellFoundedGT σ := wf
  exact ⟨MonomialOrder.lex⟩

theorem vG_mul (F G : MvPolynomial σ K) : vG v (F * G) = vG v F + vG v G := by
  classical
  by_cases hF : F = 0
  · simp [hF, vG_zero]
  by_cases hG : G = 0
  · simp [hG, vG_zero]
  refine le_antisymm ?_ (vG_add_vG_le_vG_mul F G)
  obtain ⟨m⟩ := exists_monomialOrder σ
  have haT := vG_ne_top (v := v) F hF
  have hbT := vG_ne_top (v := v) G hG
  set SF := F.support.filter fun α => v (F.coeff α) = vG v F with hSF
  set SG := G.support.filter fun α => v (G.coeff α) = vG v G with hSG
  have hSFne : SF.Nonempty := by
    obtain ⟨α, hα, h⟩ := exists_coeff_eq_vG (v := v) F hF
    exact ⟨α, Finset.mem_filter.mpr ⟨hα, h⟩⟩
  have hSGne : SG.Nonempty := by
    obtain ⟨α, hα, h⟩ := exists_coeff_eq_vG (v := v) G hG
    exact ⟨α, Finset.mem_filter.mpr ⟨hα, h⟩⟩
  obtain ⟨α0, hα0, hαmin⟩ := Finset.exists_min_image SF m.toSyn hSFne
  obtain ⟨β0, hβ0, hβmin⟩ := Finset.exists_min_image SG m.toSyn hSGne
  have hα0v : v (F.coeff α0) = vG v F := (Finset.mem_filter.mp hα0).2
  have hβ0v : v (G.coeff β0) = vG v G := (Finset.mem_filter.mp hβ0).2
  have hmem : (α0, β0) ∈ antidiagonal (α0 + β0) := by simp
  have hrest : vG v F + vG v G <
      v (∑ x ∈ (antidiagonal (α0 + β0)).erase (α0, β0), F.coeff x.1 * G.coeff x.2) := by
    apply AddValuation.map_lt_sum
    · exact WithTop.add_ne_top.mpr ⟨haT, hbT⟩
    intro x hx
    obtain ⟨hxne, hxa⟩ := Finset.mem_erase.mp hx
    have hsum : x.1 + x.2 = α0 + β0 := by simpa using hxa
    rw [AddValuation.map_mul]
    rcases lt_or_eq_of_le (vG_le_coeff (v := v) F x.1) with h1 | h1
    · exact WithTop.add_lt_add_of_lt_of_le hbT h1 (vG_le_coeff G x.2)
    rcases lt_or_eq_of_le (vG_le_coeff (v := v) G x.2) with h2 | h2
    · exact WithTop.add_lt_add_of_le_of_lt haT (vG_le_coeff F x.1) h2
    exfalso
    have hx1 : x.1 ∈ SF := by
      refine Finset.mem_filter.mpr ⟨?_, h1.symm⟩
      rw [mem_support_iff]; intro h0
      rw [h0, AddValuation.map_zero] at h1; exact haT h1
    have hx2 : x.2 ∈ SG := by
      refine Finset.mem_filter.mpr ⟨?_, h2.symm⟩
      rw [mem_support_iff]; intro h0
      rw [h0, AddValuation.map_zero] at h2; exact hbT h2
    have l1 := hαmin x.1 hx1
    have l2 := hβmin x.2 hx2
    have hs : m.toSyn x.1 + m.toSyn x.2 = m.toSyn α0 + m.toSyn β0 := by
      rw [← map_add (f := _), ← map_add (f := _), hsum]
    have e1 : m.toSyn x.1 = m.toSyn α0 := by
      rcases lt_or_eq_of_le l1 with h | h
      · exact absurd hs (ne_of_gt (add_lt_add_of_lt_of_le h l2))
      · exact h.symm
    have e2 : m.toSyn x.2 = m.toSyn β0 := by
      rw [e1] at hs; exact add_left_cancel hs
    exact hxne (Prod.ext (m.toSyn.injective e1) (m.toSyn.injective e2))
  have hc : v ((F * G).coeff (α0 + β0)) = vG v F + vG v G := by
    rw [coeff_mul, ← Finset.add_sum_erase _ _ hmem]
    have h0 : v (F.coeff α0 * G.coeff β0) = vG v F + vG v G := by
      rw [AddValuation.map_mul, hα0v, hβ0v]
    rw [← h0] at hrest ⊢
    exact AddValuation.map_add_eq_of_lt_left v hrest
  rw [← hc]
  exact vG_le_coeff _ _

theorem vG_prod {ι : Type} (s : Finset ι) (f : ι → MvPolynomial σ K) :
    vG v (∏ k ∈ s, f k) = ∑ k ∈ s, vG v (f k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [vG_one]
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, vG_mul, ih]

theorem vG_rename (f : σ → τ) (hf : Function.Injective f) (F : MvPolynomial σ K) :
    vG v (rename f F) = vG v F := by
  classical
  apply le_antisymm
  · rw [le_vG_iff]
    intro α
    rw [← coeff_rename_mapDomain f hf F α]
    exact vG_le_coeff _ _
  · rw [le_vG_iff]
    intro β
    by_cases h : ∃ u : σ →₀ ℕ, u.mapDomain f = β
    · obtain ⟨u, rfl⟩ := h
      rw [coeff_rename_mapDomain f hf]
      exact vG_le_coeff _ _
    · rw [coeff_rename_eq_zero f F β (fun u hu => absurd ⟨u, hu⟩ h), AddValuation.map_zero]
      exact le_top

theorem integral_prod_rename {ι : Type} [Fintype ι] (col : ι → MvPolynomial σ K) (f : ι → σ → τ)
    (hf : ∀ k, Function.Injective (f k)) (h : Integral v (∏ k, col k)) :
    Integral v (∏ k, rename (f k) (col k)) := by
  rw [integral_iff] at h ⊢
  rw [vG_prod] at h ⊢
  simpa only [vG_rename _ (hf _)] using h

end Formalism.MainNotions.PlaneGram
end
end

