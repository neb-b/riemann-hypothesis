module

public import Formalism.SharpRestriction.GrowthBounds.IntegralWeylLatticeSpan.WeylLatticeDescent

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.IntegralWeylLatticeSpan.CoreDesc
section
open MvPolynomial

noncomputable section

namespace Formalism.L2.G.RelativeIndexFlags

section Desc

variable {LL Kf ι : Type} [Field LL] [Field Kf] [Algebra LL Kf]

theorem desc_fun (ℓ : Kf →ₗ[LL] LL) (t : Finset (MvPolynomial ι LL)) (c : MvPolynomial ι LL → Kf) (c0 : Kf)
    (Q : MvPolynomial ι LL)
    (h : ∑ x ∈ t, C (c x) * map (algebraMap LL Kf) x = C c0 * map (algebraMap LL Kf) Q) :
    ∑ x ∈ t, ℓ (c x) • x = ℓ c0 • Q := by
  ext m
  have hm := congrArg (fun P => ℓ (AddMonoidAlgebra.coeff P m)) h
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [coeff_sum, coeff_C_mul, coeff_map, map_sum] at hm
  simp only [coeff_sum, coeff_smul, smul_eq_mul]
  have e : ∀ (a : Kf) (r : LL), ℓ (a * algebraMap LL Kf r) = ℓ a * r := by
    intro a r
    rw [mul_comm, ← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul, mul_comm]
  simp only [e] at hm
  exact hm

theorem exists_pivot {α : Type} [DecidableEq α] (R0 : Subring LL) (hv : ∀ x : LL, x ∈ R0 ∨ x⁻¹ ∈ R0) (f : α → LL)
    (t : Finset α) : (∃ x ∈ t, f x ≠ 0) → ∃ j ∈ t, f j ≠ 0 ∧ ∀ x ∈ t, f x / f j ∈ R0 := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    rintro ⟨x, hx, _⟩
    simp at hx
  | insert a t' ha ih =>
    rintro ⟨x, hx, hfx⟩
    by_cases hex : ∃ x ∈ t', f x ≠ 0
    · obtain ⟨j, hj, hfj, hall⟩ := ih hex
      by_cases hr : f a / f j ∈ R0
      · refine ⟨j, Finset.mem_insert_of_mem hj, hfj, ?_⟩
        intro y hy
        rcases Finset.mem_insert.mp hy with rfl | hy
        · exact hr
        · exact hall y hy
      · have hinv : f j / f a ∈ R0 := by
          have h2 := (hv (f a / f j)).resolve_left hr
          rwa [inv_div] at h2
        have hfa : f a ≠ 0 := by
          intro h0
          apply hr
          rw [h0, zero_div]
          exact R0.zero_mem
        refine ⟨a, Finset.mem_insert_self _ _, hfa, ?_⟩
        intro y hy
        rcases Finset.mem_insert.mp hy with rfl | hy
        · rw [div_self hfa]
          exact R0.one_mem
        · have h3 := R0.mul_mem (hall y hy) hinv
          have e : f y / f j * (f j / f a) = f y / f a := by
            field_simp
          rwa [e] at h3
    · push_neg at hex
      have hfa : f a ≠ 0 := by
        rcases Finset.mem_insert.mp hx with rfl | hx'
        · exact hfx
        · exact absurd (hex x hx') hfx
      refine ⟨a, Finset.mem_insert_self _ _, hfa, ?_⟩
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · rw [div_self hfa]
        exact R0.one_mem
      · rw [hex y hy, zero_div]
        exact R0.zero_mem

theorem exists_dual_ne {v : Kf} (hv : v ≠ 0) : ∃ ℓ : Kf →ₗ[LL] LL, ℓ v ≠ 0 := by
  by_contra hc
  push_neg at hc
  exact hv ((Module.forall_dual_apply_eq_zero_iff LL v).mp hc)

theorem desc_main (A : Subring Kf) (hA : ∀ x : Kf, x ∈ A ∨ x⁻¹ ∈ A) (R0 : Subring LL)
    (hR0 : ∀ x, x ∈ R0 ↔ algebraMap LL Kf x ∈ A) :
    ∀ (n : ℕ) (t : Finset (MvPolynomial ι LL)), t.card = n → ∀ c : MvPolynomial ι LL → Kf, (∀ x ∈ t, c x ∈ A) →
    ∀ Q : MvPolynomial ι LL, ∑ x ∈ t, C (c x) * map (algebraMap LL Kf) x = map (algebraMap LL Kf) Q →
    Q ∈ Submodule.span R0 (t : Set (MvPolynomial ι LL)) := by
  classical
  intro n
  induction n with
  | zero =>
    intro t ht c _ Q hQ
    rw [Finset.card_eq_zero] at ht
    subst ht
    simp only [Finset.sum_empty] at hQ
    have hQ0 : Q = 0 := by
      apply MvPolynomial.map_injective _ (algebraMap LL Kf).injective
      rw [← hQ, map_zero]
    rw [hQ0]
    exact zero_mem _
  | succ k ih =>
    intro t ht c hc Q hQ
    by_cases hdep : LinearIndependent LL (fun x : t => (x : MvPolynomial ι LL))
    ·
      have hsum : ∀ ℓ : Kf →ₗ[LL] LL, ∑ x ∈ t, ℓ (c x) • x = ℓ 1 • Q := by
        intro ℓ
        apply desc_fun ℓ t c 1 Q
        rw [map_one, one_mul]
        exact hQ
      have hrange : ∀ x ∈ t, c x ∈ Set.range (algebraMap LL Kf) := by
        intro x0 hx0
        by_contra hnot
        have hmk : (Submodule.span LL {(1 : Kf)}).mkQ (c x0) ≠ 0 := by
          rw [ne_eq, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_span_singleton]
          rintro ⟨a, ha⟩
          apply hnot
          exact ⟨a, by rw [Algebra.algebraMap_eq_smul_one]; exact ha⟩
        obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual LL (Kf ⧸ Submodule.span LL {(1 : Kf)}),
            φ ((Submodule.span LL {(1 : Kf)}).mkQ (c x0)) ≠ 0 := by
          by_contra hc'
          push_neg at hc'
          exact hmk ((Module.forall_dual_apply_eq_zero_iff LL _).mp hc')
        set ℓ : Kf →ₗ[LL] LL := φ.comp (Submodule.span LL {(1 : Kf)}).mkQ with hℓ
        have hℓ1 : ℓ 1 = 0 := by
          simp only [hℓ, LinearMap.comp_apply, Submodule.mkQ_apply]
          rw [(Submodule.Quotient.mk_eq_zero _).mpr (Submodule.mem_span_singleton_self 1), map_zero]
        have h0 := hsum ℓ
        rw [hℓ1, zero_smul, ← Finset.sum_coe_sort t] at h0
        have h1 := Fintype.linearIndependent_iff.mp hdep (fun x : t => ℓ (c x)) h0 ⟨x0, hx0⟩
        exact hφ h1
      choose d hd using fun x (hx : x ∈ t) => hrange x hx
      obtain ⟨ℓ0, hℓ0⟩ := exists_dual_ne (LL := LL) (Kf := Kf) (one_ne_zero : (1 : Kf) ≠ 0)
      set ℓ1 : Kf →ₗ[LL] LL := (ℓ0 1)⁻¹ • ℓ0 with hℓ1def
      have hℓ11 : ℓ1 1 = 1 := by
        simp only [hℓ1def, LinearMap.smul_apply, smul_eq_mul]
        exact inv_mul_cancel₀ hℓ0
      have h0 := hsum ℓ1
      rw [hℓ11, one_smul] at h0
      rw [← h0]
      refine Submodule.sum_mem _ fun x hx => ?_
      have hdx : ℓ1 (c x) = d x hx := by
        rw [← hd x hx, Algebra.algebraMap_eq_smul_one, LinearMap.map_smul, hℓ11, smul_eq_mul, mul_one]
      have hR : d x hx ∈ R0 := by
        rw [hR0, hd x hx]
        exact hc x hx
      rw [hdx]
      exact Submodule.smul_mem _ (⟨d x hx, hR⟩ : R0) (Submodule.subset_span hx)
    ·
      obtain ⟨g, hg, i0, hi0⟩ := Fintype.not_linearIndependent_iff.mp hdep
      set f : MvPolynomial ι LL → LL := fun x => if h : x ∈ t then g ⟨x, h⟩ else 0 with hfdef
      have hfsum : ∑ x ∈ t, f x • x = 0 := by
        rw [← hg, ← Finset.sum_coe_sort t]
        refine Finset.sum_congr rfl fun x _ => ?_
        simp [hfdef, x.2]
      obtain ⟨j, hj, hfj, hpiv⟩ := exists_pivot R0
        (fun x => by
          by_cases hx : algebraMap LL Kf x ∈ A
          · exact Or.inl ((hR0 x).mpr hx)
          · right
            rw [hR0, map_inv₀]
            exact (hA _).resolve_left hx) f t ⟨i0, i0.2, by simpa [hfdef] using hi0⟩
      have hcard : (t.erase j).card = k := by
        rw [Finset.card_erase_of_mem hj, ht]
        simp
      set c' : MvPolynomial ι LL → Kf := fun x => c x - c j * algebraMap LL Kf (f x / f j) with hc'def
      have hc' : ∀ x ∈ (t.erase j), c' x ∈ A := by
        intro x hx
        have hx' := Finset.mem_of_mem_erase hx
        have hr : algebraMap LL Kf (f x / f j) ∈ A := (hR0 _).mp (hpiv x hx')
        exact A.sub_mem (hc x hx') (A.mul_mem (hc j hj) hr)
      have hrel : ∑ x ∈ t.erase j, (f x / f j) • x = -j := by
        have h1 := hfsum
        rw [← Finset.add_sum_erase t _ hj] at h1
        have h2 : ∑ x ∈ t.erase j, (f x / f j) • x = (f j)⁻¹ • ∑ x ∈ t.erase j, f x • x := by
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [smul_smul, div_eq_mul_inv, mul_comm]
        rw [h2, eq_neg_of_add_eq_zero_right h1, smul_neg, smul_smul, inv_mul_cancel₀ hfj, one_smul]
      have hQ' : ∑ x ∈ (t.erase j), C (c' x) * map (algebraMap LL Kf) x = map (algebraMap LL Kf) Q := by
        rw [← hQ, ← Finset.add_sum_erase t _ hj]
        simp only [hc'def, map_sub, map_mul, sub_mul, Finset.sum_sub_distrib]
        have e1 : ∑ x ∈ (t.erase j), C (c j) * C (algebraMap LL Kf (f x / f j)) * map (algebraMap LL Kf) x =
            C (c j) * map (algebraMap LL Kf) (∑ x ∈ (t.erase j), (f x / f j) • x) := by
          set_option synthInstance.maxHeartbeats 100000 in
            rw [map_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, mul_assoc]
        rw [e1]
        have e2 : map (algebraMap LL Kf) (∑ x ∈ (t.erase j), (f x / f j) • x) = -map (algebraMap LL Kf) j := by
          rw [hrel, map_neg]
        rw [e2]
        ring
      have hmem := ih (t.erase j) hcard c' hc' Q hQ'
      exact Submodule.span_mono (by
        intro x hx
        exact Finset.mem_of_mem_erase hx) hmem

end Desc

theorem descVal : DescVal := by
  intro LL Kf O ι _ _ _ _ _ _ _ e R0 hR0 S Q hQ
  classical
  letI : Algebra LL Kf := e.toAlgebra
  have he : ∀ x, algebraMap LL Kf x = e x := fun x => rfl
  let A : Subring Kf := (algebraMap O Kf).range
  have hA : ∀ x : Kf, x ∈ A ∨ x⁻¹ ∈ A := by
    intro x
    rcases ValuationRing.isInteger_or_isInteger O x with ⟨r, hr⟩ | ⟨r, hr⟩
    · exact Or.inl ⟨r, hr⟩
    · exact Or.inr ⟨r, hr⟩
  have hR0' : ∀ x, x ∈ R0 ↔ algebraMap LL Kf x ∈ A := by
    intro x
    rw [hR0 x, he]
    rfl
  obtain ⟨cc, hsupp, hsum⟩ := Submodule.mem_span_set.mp hQ
  have hpre : ∀ y ∈ cc.support, ∃ q ∈ S, MvPolynomial.map e q = y := fun y hy => hsupp hy
  choose! qof hqS hqy using hpre
  have htS : ((cc.support.image qof : Finset (MvPolynomial ι LL)) : Set (MvPolynomial ι LL)) ⊆ S := by
    intro q hq
    rw [Finset.coe_image] at hq
    obtain ⟨y, hy, rfl⟩ := hq
    exact hqS y hy
  have hinjOn : Set.InjOn qof (cc.support : Set (MvPolynomial ι Kf)) := by
    intro y hy y' hy' h
    rw [← hqy y hy, ← hqy y' hy', h]
  let c' : MvPolynomial ι LL → Kf := fun q => algebraMap O Kf (cc (MvPolynomial.map e q))
  have hc' : ∀ q ∈ cc.support.image qof, c' q ∈ A := fun q _ => ⟨_, rfl⟩
  have hrel : ∑ q ∈ cc.support.image qof, C (c' q) * MvPolynomial.map (algebraMap LL Kf) q =
      MvPolynomial.map (algebraMap LL Kf) Q := by
    show ∑ q ∈ cc.support.image qof, C (c' q) * MvPolynomial.map e q = MvPolynomial.map e Q
    rw [Finset.sum_image hinjOn, ← hsum, Finsupp.sum]
    refine Finset.sum_congr rfl fun y hy => ?_
    simp only [c', hqy y hy]
    rw [Algebra.smul_def, MvPolynomial.algebraMap_apply]
  exact Submodule.span_mono htS
    (desc_main A hA R0 hR0' (cc.support.image qof).card (cc.support.image qof) rfl c' hc' Q hrel)

end Formalism.L2.G.RelativeIndexFlags
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.IntegralWeylLatticeSpan.IntSpanGSmul
section
open MvPolynomial Matrix Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.BasicNotions Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.G.RelativeIndexFlags

open Formalism.L2.G.Cmp

section Gen

variable {Tau : Type} [Fintype Tau] {n : ℕ} {LL : Type} [Field LL]

theorem intSpanG_smul (embLL : LL →+* ℂ) (R0 : Subring LL) (lam : Tau → DomWeight n) (a : LL) (ha : a ∈ R0)
    {P : MvPolynomial (Tau × Fin n × Fin n) ℂ} (hP : P ∈ IntSpanG embLL R0 lam) : embLL a • P ∈ IntSpanG embLL R0 lam := by
  induction hP using AddSubgroup.closure_induction with
  | mem q hq =>
    obtain ⟨s, f, hs, hf, rfl⟩ := hq
    exact AddSubgroup.subset_closure ⟨a * s, f, mul_mem ha hs, hf, by rw [map_mul, mul_smul]⟩
  | zero => rw [smul_zero]; exact AddSubgroup.zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact AddSubgroup.add_mem _ hx hy
  | neg x _ hx => rw [smul_neg]; exact AddSubgroup.neg_mem _ hx

theorem fnOf_congr (G : Tau → Matrix (Fin n) (Fin n) ℂ) (s : Tau → ℤ) (M M' : Tau → Matrix (Fin n) (Fin n) ℂ)
    (P : MvPolynomial (Tau × Fin n × Fin n) ℂ) (y y' : Frames G) (h : ∀ τ, M τ * y.1 τ = M' τ * y'.1 τ) :
    fnOf G s M P y = fnOf G s M' P y' := by
  show (∏ τ, (M τ * y.1 τ).det ^ s τ) * MvPolynomial.eval (fun x : Tau × Fin n × Fin n => (M x.1 * y.1 x.1) x.2.1 x.2.2) P =
    (∏ τ, (M' τ * y'.1 τ).det ^ s τ) * MvPolynomial.eval (fun x : Tau × Fin n × Fin n => (M' x.1 * y'.1 x.1) x.2.1 x.2.2) P
  simp only [h]

end Gen

section Gen2

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
  {Tau : Type} [Fintype Tau] {LL : Type} [Field LL] {p : ℕ}
  {S : StepLevel F E σ J T f bad} {emb : Tau → E →+* ℂ} {embLL : LL →+* ℂ}
  {G : GAtP p} {e : LL →+* G.Kf} {A : LocAt F E n G} {pos : (Σ v : Fin G.P.nV, Fin (G.P.n' v)) ≃ Tau}
  {V cls : Type} [AddCommGroup V] [Module LL V] {embV : V →ₛₗ[embLL] (cls → Frames (gramC J emb) → ℂ)}
  {yc : cls → UPts σ J (FiniteAdeleRing (𝓞 F) F)}

theorem atInf_bc (emb : Tau → E →+* ℂ) (γ : GL (Fin n) E) (τ : Tau) :
    atInf emb (γ : Matrix (Fin n) (Fin n) E) τ = ((bc (emb τ) γ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) := rfl

def trF (emb : Tau → E →+* ℂ) (γ : GL (Fin n) E) (z : Frames (gramC J emb)) : Frames (gramC J emb) :=
  ⟨fun τ => atInf emb (γ : Matrix (Fin n) (Fin n) E) τ * z.1 τ, fun τ => by
    rw [Matrix.det_mul]
    exact ((Matrix.isUnit_iff_isUnit_det _).1 (bc (emb τ) γ).isUnit).mul (z.2 τ)⟩

theorem isTr_trF (emb : Tau → E →+* ℂ) (γ : GL (Fin n) E) (z : Frames (gramC J emb)) :
    IsTr (atInf emb (γ : Matrix (Fin n) (Fin n) E)) z (trF emb γ z) := fun _ => rfl

theorem isTr_trF_inv (emb : Tau → E →+* ℂ) (γ : GL (Fin n) E) (z : Frames (gramC J emb)) :
    IsTr (atInf emb (γ : Matrix (Fin n) (Fin n) E)) (trF emb γ⁻¹ z) z := by
  intro τ
  show z.1 τ = atInf emb (γ : Matrix (Fin n) (Fin n) E) τ * (atInf emb ((γ⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) τ * z.1 τ)
  rw [atInf_bc, atInf_bc, ← Matrix.mul_assoc, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one, Matrix.one_mul]

theorem valIntAt_of (hcore : WeylLatticeDescent) (hfrac : IsFractionRing G.O G.Kf)
    (tE : Tau → E →+* LL) (htE : ∀ τ x, embLL (tE τ x) = emb τ x)
    (R0 : Subring LL) (hR0 : ∀ x, x ∈ R0 ↔ e x ∈ Set.range (algebraMap G.O G.Kf))
    (lam : Tau → DomWeight n) (hw : WtTie G.P A.rk pos lam)
    (hex : ValEx S emb embLL G A pos embV yc)
    (Bas : cls → GL (Fin n) E → Prop) (hBex : ∀ c, ∃ B', Bas c B')
    (hlat : ∀ (i : G.comp) (L : G.P.Tup) (c : cls) (g : ∀ v, GL (Fin (G.P.m + 1)) (G.P.Qq v)) (γ : GL (Fin n) E) (κ : S.U),
      (∀ v, L v = colSpan (G.P.W v) (g v : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v))) →
      γ ∈ UJ (σ : E →+* E) J → A.IsPt i g (bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * (yc c).1 * κ.1) →
      ∀ B', Bas c B' → ∀ v (s : Fin (G.P.n' v)), extO G.O (G.P.ι v) (G.P.σ v) s.val (L v) =
        colSpan G.O ((nAt G.P A.rk pos (fun τ => bc (tE τ) (A.B⁻¹ * γ * B')) v s).map e))
    (hchi : ∀ κ : S.U, ∃ r ∈ R0, r⁻¹ ∈ R0 ∧ embLL r = (S.chi κ : ℂ)) :
    ValIntAt S emb embLL G e A pos embV yc (fun x c => ∀ B', Bas c B' → ∃ P ∈ IntSpanG embLL R0 lam,
      ∀ z, embV x c z = fnOf _ (shiftOf lam) (atInf emb ((B'⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E)) P z) := by
  rintro x i L c hL ⟨g, γ, κ, hg, hγ, hpt⟩
  have hQ := valC_spec hex x i L hL
  have hval := hQ.2 g hg c γ hγ κ hpt
  have hcmp : cmpC S emb embLL G e A pos embV yc x i L = MvPolynomial.map e (valC S emb embLL G A pos embV yc x i L) := by
    unfold cmpC; rw [if_pos hL]
  rw [hcmp]
  obtain ⟨r, hr, hr', hrχ⟩ := hchi κ
  have hr0 : embLL r ≠ 0 := by rw [hrχ]; exact (S.chi κ).ne_zero
  have hM : (fun τ => ((bc (tE τ) A.B⁻¹ : GL (Fin n) LL) : Matrix (Fin n) (Fin n) LL).map embLL) = crdB emb A.B := by
    funext τ; ext a b; exact htE τ _
  have hNM : ∀ B' : GL (Fin n) E, (fun τ => (((bc (tE τ) (A.B⁻¹ * γ * B'))⁻¹ * bc (tE τ) A.B⁻¹ : GL (Fin n) LL) :
      Matrix (Fin n) (Fin n) LL).map embLL) = atInf emb ((B'⁻¹ * γ⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) := by
    intro B'
    funext τ
    have e1 : (bc (tE τ) (A.B⁻¹ * γ * B'))⁻¹ * bc (tE τ) A.B⁻¹ = bc (tE τ) (B'⁻¹ * γ⁻¹) := by
      rw [← map_inv, ← map_mul]; congr 1; group
    rw [e1]
    ext a b; exact htE τ _
  have hfn : ∀ (B' : GL (Fin n) E) (Pp : MvPolynomial (Tau × Fin n × Fin n) ℂ) (z z' : Frames (gramC J emb)),
      IsTr (atInf emb (γ : Matrix (Fin n) (Fin n) E)) z' z →
      fnOf (gramC J emb) (shiftOf lam) (atInf emb ((B'⁻¹ * γ⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E)) Pp z =
        fnOf (gramC J emb) (shiftOf lam) (atInf emb ((B'⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E)) Pp z' := by
    intro B' Pp z z' hz
    refine fnOf_congr _ _ _ _ _ _ _ fun τ => ?_
    rw [hz τ, atInf_bc, atInf_bc, atInf_bc, ← Matrix.mul_assoc, ← Units.val_mul, ← map_mul]
    congr 3
    group
  have hc := fun B' (hB' : Bas c B') => hcore G.P A.rk pos (gramC J emb) embLL e R0 hfrac hR0 lam hw (fun τ => bc (tE τ) A.B⁻¹)
    (fun τ => bc (tE τ) (A.B⁻¹ * γ * B')) L (hlat i L c g γ κ hg hγ hpt B' hB') (valC S emb embLL G A pos embV yc x i L)
  constructor
  · intro hmem B' hB'
    obtain ⟨Pp, hPp, hev⟩ := (hc B' hB').1 hmem
    refine ⟨embLL r⁻¹ • Pp, intSpanG_smul _ _ _ _ hr' hPp, fun z' => ?_⟩
    have h1 := hev (trF emb γ z')
    rw [hM, hNM, hval _ z' (isTr_trF emb γ z'), hfn B' Pp _ z' (isTr_trF emb γ z'), ← hrχ] at h1
    rw [map_smul, Pi.smul_apply, ← h1, smul_eq_mul, map_inv₀, inv_mul_cancel_left₀ hr0]
  · intro hI
    obtain ⟨B', hB'⟩ := hBex c
    obtain ⟨Pp, hPp, hev⟩ := hI B' hB'
    refine (hc B' hB').2 ⟨embLL r • Pp, intSpanG_smul _ _ _ _ hr hPp, fun z => ?_⟩
    rw [hM, hNM, hval z _ (isTr_trF_inv emb γ z), hfn B' _ z _ (isTr_trF_inv emb γ z), map_smul, Pi.smul_apply, ← hev, hrχ,
      smul_eq_mul]

end Gen2

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : Formalism.L2.Herm.Herm0 D}

def RestExB (D : D7) : Prop :=
  ∀ (u : D.what₂.Word) (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) → ∀ c : (D.mem u).C.cls 0,
    ∃ B' : GL (Fin (D.R.N 0)) D.host.E, Formalism.L2.Forms.IsLocBasis (D.what₂.places.resChar w)
      (dualSet (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)) (clsCrd D u 0 (Nat.zero_le _) c)) B'

def RestChi (T : ∀ u : D.what₂.Word, Forms0 D u) : Prop :=
  ∀ (u : D.what₂.Word) (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
    ∀ κ : ((T u).cls0).lev.U, ∃ r ∈ intW D.what₂.places w, r⁻¹ ∈ intW D.what₂.places w ∧
      D.what₂.embLL r = (((T u).cls0).lev.chi κ : ℂ)

def RestLatO (T : ∀ u : D.what₂.Word, Forms0 D u) (Gt : GatTies D) (I : CmpIn D X) : Prop :=
  ∀ u w hg (i : (D.gat u w hg).comp) (L : (D.gat u w hg).P.Tup) (c : (D.mem u).C.cls 0)
    (g : ∀ v, GL (Fin ((D.gat u w hg).P.m + 1)) ((D.gat u w hg).P.Qq v)) (γ : GL (Fin (D.R.N 0)) D.host.E)
    (κ : ((T u).cls0).lev.U),
    (∀ v, L v = colSpan ((D.gat u w hg).P.W v) (g v : Matrix (Fin ((D.gat u w hg).P.m + 1)) (Fin ((D.gat u w hg).P.m + 1)) ((D.gat u w hg).P.Qq v))) →
    γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)) →
    (locAt X u w hg I.B).IsPt i g (bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ *
      (((T u).cls0).y c).1 * κ.1) →
    ∀ B' : GL (Fin (D.R.N 0)) D.host.E, Formalism.L2.Forms.IsLocBasis (D.what₂.places.resChar w)
      (dualSet (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)) (clsCrd D u 0 (Nat.zero_le _) c)) B' →
    ∀ v (s : Fin ((D.gat u w hg).P.n' v)),
      extO (D.gat u w hg).O ((D.gat u w hg).P.ι v) ((D.gat u w hg).P.σ v) s.val (L v) =
        colSpan (D.gat u w hg).O ((nAt (D.gat u w hg).P (locAt X u w hg I.B).rk (Gt.gat_pos u w hg)
          (fun τ => bc (tEL D τ) ((locAt X u w hg I.B).B⁻¹ * γ * B')) v s).map (I.embW u w hg))


set_option maxHeartbeats 4000000 in
theorem valIntRec_of {T : ∀ u : D.what₂.Word, Forms0 D u} {Gt : GatTies D} {I : CmpIn D X} (hcore : WeylLatticeDescent)
    (hex : ∀ u w hg, ValEx ((T u).cls0).lev (embT D) D.what₂.embLL (D.gat u w hg)
      (locAt X u w hg I.B) (Gt.gat_pos u w hg) (embFr T u) ((T u).cls0).y)
    (hfrac : ∀ u w hg, IsFractionRing (D.gat u w hg).O (D.gat u w hg).Kf)
    (hB : RestExB D) (hlat : RestLatO T Gt I) (hchi : RestChi T) : ValIntRec T Gt I := by
  intro u w hg x i L c hL hpt
  have h := valIntAt_of (S := ((T u).cls0).lev) (emb := embT D) (embLL := D.what₂.embLL) (G := D.gat u w hg)
    (e := I.embW u w hg) (A := locAt X u w hg I.B) (pos := Gt.gat_pos u w hg) (embV := embFr T u)
    (yc := ((T u).cls0).y) hcore (hfrac u w hg) (tEL D) (tEL_emb D) (intW D.what₂.places w)
    (fun a => I.embW_int u w hg a) ((D.fm u).lam 0) (fun v s i => Gt.gat_lam u w hg v s i) (hex u w hg)
    (fun c B' => Formalism.L2.Forms.IsLocBasis (D.what₂.places.resChar w)
      (dualSet (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)) (clsCrd D u 0 (Nat.zero_le _) c)) B')
    (hB u w hg) (hlat u w hg) (hchi u w hg) x i L c hL hpt
  rw [h]
  constructor
  · intro h1 B' hB'
    obtain ⟨P, hP, hz⟩ := h1 B' hB'
    refine ⟨P, hP, fun z => ?_⟩
    have := hz (((T u).val0).eY z)
    rw [lamT_zero]
    rw [← this]
    show _ = (D.fm u).emb 0 x c (((T u).val0).eY.symm (((T u).val0).eY z))
    rw [Equiv.symm_apply_apply]
  · intro h1 B' hB'
    obtain ⟨P, hP, hz⟩ := h1 B' hB'
    refine ⟨P, hP, fun z => ?_⟩
    have := hz (((T u).val0).eY.symm z)
    rw [lamT_zero, Equiv.apply_symm_apply] at this
    exact this

end Formalism.L2.G.RelativeIndexFlags
end
end

