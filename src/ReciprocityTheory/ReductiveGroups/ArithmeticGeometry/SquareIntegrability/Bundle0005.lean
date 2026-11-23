module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle0001

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.PolyDerivMonomialOne
section
namespace ReciprocityTheory.ChartRestriction.G.I2

noncomputable section

section ItD

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]

def itD (f : W → ℂ) (l : List W) (z : W) : ℂ :=
  iteratedFDeriv ℂ l.length f z (fun j => l.get j)

theorem itD_nil (f : W → ℂ) (z : W) : itD f [] z = f z := by
  simp only [itD]
  first
    | exact iteratedFDeriv_zero_apply _
    | simp

theorem itD_differentiable {f : W → ℂ} (hf : ContDiff ℂ (⊤ : ℕ∞) f) (l : List W) :
    Differentiable ℂ (fun y => itD f l y) := by
  have hD : Differentiable ℂ (iteratedFDeriv ℂ l.length f) := by
    refine hf.differentiable_iteratedFDeriv ?_
    first
      | exact_mod_cast ENat.coe_lt_top _
      | exact WithTop.coe_lt_coe.2 (ENat.coe_lt_top _)
      | simp
  unfold itD
  exact (ContinuousMultilinearMap.apply ℂ (fun _ : Fin l.length => W) ℂ _).differentiable.comp hD

theorem itD_cons {f : W → ℂ} (hf : ContDiff ℂ (⊤ : ℕ∞) f) (e : W) (l : List W) (z : W) :
    itD f (e :: l) z = fderiv ℂ (fun y => itD f l y) z e := by
  have hD : Differentiable ℂ (iteratedFDeriv ℂ l.length f) := by
    refine hf.differentiable_iteratedFDeriv ?_
    first
      | exact_mod_cast ENat.coe_lt_top _
      | exact WithTop.coe_lt_coe.2 (ENat.coe_lt_top _)
      | simp
  show iteratedFDeriv ℂ (l.length + 1) f z (fun j => (e :: l).get j) = _
  rw [iteratedFDeriv_succ_apply_left]
  have hc : (fun y => itD f l y) =
      (ContinuousMultilinearMap.apply ℂ (fun _ : Fin l.length => W) ℂ (fun j => l.get j)) ∘
        iteratedFDeriv ℂ l.length f := rfl
  rw [hc, fderiv_comp z (ContinuousLinearMap.differentiableAt _) (hD z), ContinuousLinearMap.fderiv]
  rfl

theorem fderiv_prod_single {n : ℕ} {h : Fin n → W → ℂ} (hh : ∀ k, Differentiable ℂ (h k))
    (x : Fin n → W) (k0 : Fin n) (e : W) :
    fderiv ℂ (fun y : Fin n → W => ∏ k, h k (y k)) x (Pi.single k0 e) =
      (∏ k ∈ Finset.univ.erase k0, h k (x k)) * fderiv ℂ (h k0) (x k0) e := by
  classical
  have hd : ∀ k, HasFDerivAt (fun y : Fin n → W => h k (y k))
      ((fderiv ℂ (h k) (x k)).comp (ContinuousLinearMap.proj k)) x :=
    fun k => ((hh k) (x k)).hasFDerivAt.comp x (hasFDerivAt_apply k x)
  have hP : HasFDerivAt (fun y : Fin n → W => ∏ k, h k (y k))
      (∑ k, (∏ j ∈ Finset.univ.erase k, h j (x j)) •
        ((fderiv ℂ (h k) (x k)).comp (ContinuousLinearMap.proj k))) x :=
    HasFDerivAt.finsetProd (fun k _ => hd k)
  rw [hP.fderiv]
  simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.coe_smul',
    Pi.smul_apply, ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.proj_apply,
    smul_eq_mul]
  rw [Finset.sum_eq_single k0]
  · simp
  · intro b _ hb
    simp [hb]
  · simp

def colL {n : ℕ} (L : List (Fin n × W)) (k : Fin n) : List W :=
  (L.filter (fun p => p.1 = k)).map Prod.snd

theorem colL_cons {n : ℕ} (a : Fin n × W) (L : List (Fin n × W)) (k : Fin n) :
    colL (a :: L) k = if a.1 = k then a.2 :: colL L k else colL L k := by
  unfold colL
  by_cases h : a.1 = k <;> simp [List.filter_cons, h]

theorem itD_prod {n : ℕ} {g : Fin n → W → ℂ} (hg : ∀ k, ContDiff ℂ (⊤ : ℕ∞) (g k))
    (L : List (Fin n × W)) (x : Fin n → W) :
    itD (fun v : Fin n → W => ∏ k, g k (v k)) (L.map fun p => Pi.single p.1 p.2) x =
      ∏ k, itD (g k) (colL L k) (x k) := by
  have hP : ContDiff ℂ (⊤ : ℕ∞) (fun v : Fin n → W => ∏ k, g k (v k)) := by
    first
      | exact contDiff_prod fun k _ => (hg k).comp (contDiff_apply ℂ W k)
      | fun_prop
  induction L generalizing x with
  | nil => simp [itD_nil, colL]
  | cons a L ih =>
    simp only [List.map_cons]
    rw [itD_cons hP]
    have hfun : (fun y => itD (fun v : Fin n → W => ∏ k, g k (v k))
        (L.map fun p => Pi.single p.1 p.2) y) = fun y => ∏ k, itD (g k) (colL L k) (y k) :=
      funext fun y => ih y
    rw [hfun, fderiv_prod_single (h := fun k y => itD (g k) (colL L k) y)
      (fun k => itD_differentiable (hg k) _)]
    rw [← Finset.prod_erase_mul Finset.univ _ (Finset.mem_univ a.1)]
    congr 1
    · refine Finset.prod_congr rfl fun k hk => ?_
      rw [colL_cons, if_neg (Ne.symm (Finset.ne_of_mem_erase hk))]
    · rw [colL_cons, if_pos rfl, itD_cons (hg _)]

theorem itD_col {s : (Fin 1 → W) → ℂ} (hs : ContDiff ℂ (⊤ : ℕ∞) s) (l : List W) :
    itD (fun z : W => s (fun _ => z)) l 0 = iteratedFDeriv ℂ l.length s 0 (fun j _ => l.get j) := by
  unfold itD
  have hi : ((l.length : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
    first
      | exact_mod_cast le_top
      | exact WithTop.coe_le_coe.2 le_top
  have h := (ContinuousLinearMap.pi fun _ : Fin 1 => ContinuousLinearMap.id ℂ W).iteratedFDeriv_comp_right
    hs (0 : W) hi
  exact congrArg (fun T => T (fun j => l.get j)) h

end ItD

section PD

variable {σ W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]

def pdTerm (u : σ → W) (F : W → ℂ) (x : W) (m : σ →₀ ℕ) : ℂ :=
  iteratedFDeriv ℂ (Multiset.card (Finsupp.toMultiset m)) F x
    (fun k => u ((Finsupp.toMultiset m).toList.get (k.cast (Multiset.length_toList _).symm)))

theorem polyDeriv_eq_of_subset (P : MvPolynomial σ ℂ) (u : σ → W) (F : W → ℂ) (x : W)
    {S : Finset (σ →₀ ℕ)} (hS : P.support ⊆ S) :
    polyDeriv P u F x = ∑ m ∈ S, P.coeff m * pdTerm u F x m := by
  unfold polyDeriv
  refine Finset.sum_subset hS fun m _ hm => ?_
  first
    | rw [MvPolynomial.notMem_support_iff.1 hm, zero_mul]
    | rw [MvPolynomial.not_mem_support_iff.1 hm, zero_mul]

theorem polyDeriv_add (P Q : MvPolynomial σ ℂ) (u : σ → W) (F : W → ℂ) (x : W) :
    polyDeriv (P + Q) u F x = polyDeriv P u F x + polyDeriv Q u F x := by
  classical
  rw [polyDeriv_eq_of_subset (P + Q) u F x (S := P.support ∪ Q.support) MvPolynomial.support_add,
    polyDeriv_eq_of_subset P u F x (S := P.support ∪ Q.support) (fun _ h => Finset.mem_union_left _ h),
    polyDeriv_eq_of_subset Q u F x (S := P.support ∪ Q.support) (fun _ h => Finset.mem_union_right _ h),
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_add, add_mul]

theorem jof_polyDeriv_sum {ι : Type*} (s : Finset ι) (P : ι → MvPolynomial σ ℂ) (u : σ → W) (F : W → ℂ)
    (x : W) : polyDeriv (∑ i ∈ s, P i) u F x = ∑ i ∈ s, polyDeriv (P i) u F x := by
  exact map_sum (AddMonoidHom.mk' (fun Q : MvPolynomial σ ℂ => polyDeriv Q u F x)
    (fun Q R => polyDeriv_add Q R u F x)) P s

theorem polyDeriv_smul (c : ℂ) (P : MvPolynomial σ ℂ) (u : σ → W) (F : W → ℂ) (x : W) :
    polyDeriv (c • P) u F x = c * polyDeriv P u F x := by
  classical
  rw [polyDeriv_eq_of_subset (c • P) u F x (S := P.support) MvPolynomial.support_smul,
    polyDeriv_eq_of_subset P u F x (S := P.support) subset_rfl, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_smul, smul_eq_mul, mul_assoc]

theorem polyDeriv_monomial_one (m : σ →₀ ℕ) (u : σ → W) (F : W → ℂ) (x : W) :
    polyDeriv (MvPolynomial.monomial m (1 : ℂ)) u F x = pdTerm u F x m := by
  classical
  rw [polyDeriv_eq_of_subset _ u F x (S := {m}) MvPolynomial.support_monomial_subset,
    Finset.sum_singleton, MvPolynomial.coeff_monomial, if_pos rfl, one_mul]

theorem pdTerm_eq_itD (u : σ → W) (F : W → ℂ) (x : W) (m : σ →₀ ℕ) :
    pdTerm u F x m = itD F ((Finsupp.toMultiset m).toList.map u) x := by
  have gen : ∀ (n₁ n₂ : ℕ) (h : n₁ = n₂) (v₁ : Fin n₁ → W) (v₂ : Fin n₂ → W),
      (∀ i, v₁ i = v₂ (i.cast h)) → iteratedFDeriv ℂ n₁ F x v₁ = iteratedFDeriv ℂ n₂ F x v₂ := by
    intro n₁ n₂ h v₁ v₂ hv
    subst h
    exact congrArg _ (funext fun i => hv i)
  unfold pdTerm itD
  refine gen _ _ (by simp) _ _ fun i => ?_
  simp

end PD

end

end ReciprocityTheory.ChartRestriction.G.I2
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.PropASt
section
namespace ReciprocityTheory.ChartRestriction.G.I2

open MeasureTheory Complex

noncomputable section

def GT.Coc {ι : Type} [Fintype ι] (Y : GT ι) (q : ℕ) : Prop :=
  ∀ γ ∈ lat Y.b, ∀ γ' ∈ lat Y.b,
    Y.ka (γ + γ') = Y.ka γ * Y.ka γ' * cexp (-(Real.pi * q * (Hf γ γ').im) * I)


open scoped Classical in
open Classical in
def PropAStatement : Prop :=
  ∀ (ι : Type) [Fintype ι] (Y : GT ι) (q c : ℕ) (R0 : ℝ), 1 ≤ q → Y.Coc q → 0 < R0 →
    (∀ γ ∈ lat Y.b, γ ≠ 0 → R0 ≤ Real.sqrt (q * Real.pi) * ‖γ‖) →
    270 ≤ R0 ^ 2 → 90 * ((Fintype.card ι : ℝ) + c) ≤ R0 ^ 2 →
    ∀ p : MvPolynomial ι ℂ, p.totalDegree ≤ c →
      ∃ β ∈ Y.Sec q,
        (∀ α : ι →₀ ℕ, α.degree ≤ c →
          polyDeriv (MvPolynomial.monomial α 1) (fun i => EuclideanSpace.single i 1) β 0 =
            polyDeriv (MvPolynomial.monomial α 1) (fun i => EuclideanSpace.single i 1)
              (fun v : EuclideanSpace ℂ ι => MvPolynomial.eval (fun i => v i) p) 0) ∧
        Y.l2 q β ≤ 6 * ∫ v : EuclideanSpace ℂ ι, ‖MvPolynomial.eval (fun i => v i) p‖ ^ 2 *
          Real.exp (-(q * Real.pi) * ‖v‖ ^ 2)

end

end ReciprocityTheory.ChartRestriction.G.I2
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.SplitSt
section
namespace ReciprocityTheory.ChartRestriction.G.I2

open NumberField Complex

noncomputable section

variable {E : Type} [Field E] [NumberField E]

abbrev IR {dim : (E →+* ℂ) → ℕ} (I : Submodule ℤ (Vsp dim)) : Submodule ℝ (Vsp dim) :=
  Submodule.span ℝ (I : Set (Vsp dim))

def IsU {dim : (E →+* ℂ) → ℕ} (I : Submodule ℤ (Vsp dim)) (x u : Vsp dim) : Prop :=
  u ∈ IR I ∧ ∀ a ∈ IR I, inner ℝ u a = (Hf x a).im

def InPart {dim : (E →+* ℂ) → ℕ} (σ : E →+* ℂ) (v : Vsp dim) : Prop := ∀ j : Idx dim, j.1 ≠ σ → v j = 0

def d1 {dim : (E →+* ℂ) → ℕ} (F : (Fin 1 → Vsp dim) → ℂ) (c : ℕ) (x : Fin c → Vsp dim) : ℂ :=
  iteratedFDeriv ℂ c F 0 (fun k _ => x k)

section

variable {DF : ℕ} {X : PT E}

def Par.th (P : Par X DF) : ℝ := ReciprocityTheory.ChartRestriction.G.I2.th (E := E) P.q P.R0

def Par.eps1 (P : Par X DF) : ℝ :=
  7 * 2 ^ X.gA * (4.3 : ℝ) ^ dstar (E := E) P.m * Real.exp (-t0 (E := E) P.q P.R0)

def Par.K6 (P : Par X DF) : ℝ :=
  6 * (2 * (dstar (E := E) P.m : ℝ)) ^ ((dstar (E := E) P.m : ℝ) / 2)

structure IsSplit (P : Par X DF) (I : Submodule ℤ (Vsp X.dim)) : Prop where
  le : I ≤ X.L
  sat : ∀ x ∈ X.L, ∀ k : ℤ, k ≠ 0 → k • x ∈ I → x ∈ I
  stable : ∀ (α : 𝓞 E) x, x ∈ I → act α x ∈ I
  iso : ∀ x ∈ I, ∀ y ∈ I, (Hf x y).im = 0
  eps : ∀ x ∈ I, X.eps x = 1
  rank : ∃ ρ ≤ P.m, Module.finrank ℝ (IR I) = 2 * PT.f E * ρ
  ne_bot : I ≠ ⊥ ↔ X.la1 < P.th

  thick : ∀ x ∈ X.L, (∀ a ∈ I, (Hf x a).im = 0) → x ∉ I → P.th ≤ Metric.infDist x (IR I)

  sep : ∀ x ∈ X.L, ∀ u, IsU I x u → u ≠ 0 → b0 (E := E) P.q P.R0 ≤ ‖u‖ ^ 2

  u1 : ∃ x : Fin (Module.finrank ℝ (IR I)) → Vsp X.dim, ∃ u : Fin (Module.finrank ℝ (IR I)) → Vsp X.dim,
    (∀ j, x j ∈ X.L ∧ IsU I (x j) (u j)) ∧ LinearIndependent ℝ u ∧
      ∀ j, ‖u j‖ ^ 2 ≤ PT.rd E ^ 2 * (dstar (E := E) P.m : ℝ) ^ 4 * P.ph / (2 * PT.f E)

  u2 : ∀ (k : ℕ) (x u : Fin k → Vsp X.dim), (∀ j, x j ∈ X.L ∧ IsU I (x j) (u j)) →
    Submodule.span ℝ {w | ∃ j, ∃ α : 𝓞 E, IsU I (act α (x j)) w} = IR I →
      P.ph ≤ ∑ j, ‖u j‖ ^ 2 / 2

end

def SplitStatement : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (X : PT E) (DF : ℕ) (P : Par X DF),
    ∃ I, IsSplit P I

def CharStatement : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (X : PT E) (DF : ℕ) (P : Par X DF)
    (I : Submodule ℤ (Vsp X.dim)), IsSplit P I → ∀ σ : E →+* ℂ, ∀ ρ : ℕ,
    Module.finrank ℂ ((Submodule.span ℂ (I : Set (Vsp X.dim))) ⊓
      {carrier := {v | InPart σ v}, add_mem' := fun {a b} ha hb j hj => by
          simp [ha j hj, hb j hj], zero_mem' := fun j _ => rfl,
        smul_mem' := fun c v hv j hj => by simp [hv j hj]} : Submodule ℂ (Vsp X.dim)) = ρ →
    ∃ (w : Fin ρ → Vsp X.dim) (x u : Fin ρ → Vsp X.dim) (R : Fin ρ → ℝ) (ε : Fin ρ → Fin ρ → ℂ),
      (∀ s, InPart σ (w s) ∧ w s ∈ Submodule.span ℂ (I : Set (Vsp X.dim))) ∧
      (∀ s s', Hf (w s) (w s') = if s = s' then 1 else 0) ∧
      (∀ s, x s ∈ X.L ∧ IsU I (x s) (u s)) ∧
      (∀ s s', s < s' → ε s s' = 0) ∧
      (∀ s, Real.sqrt (∑ s', ‖ε s s'‖ ^ 2) ≤ 1 / (30 * ρ ^ 2) ∧
        ∑ s', ‖ε s s'‖ ≤ Real.sqrt ρ / (30 * ρ ^ 2)) ∧
      (∀ s v, InPart σ v → Hf v (u s) / R s = Hf v (w s) + ∑ s', ε s s' * Hf v (w s')) ∧
      (∀ s, ‖u s‖ ≤ 1.5 * R s ∧ 1 ≤ 2 * Real.pi * R s) ∧
      (∀ s, ∀ y ∈ X.L, ∀ uy, IsU I y uy → |2 * inner ℝ (u s) uy| ≤ M1 (E := E) P.m * ‖uy‖ ^ 2) ∧
      (∀ s, ‖u s‖ ^ 2 ≤ Cchi (E := E) P.m * P.ph)

def ColTorusStatement : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (X : PT E) (DF : ℕ) (P : Par X DF)
    (I : Submodule ℤ (Vsp X.dim)), IsSplit P I → ∀ (c : ℕ), c ≤ DF → ∀ (σ : E →+* ℂ)
    (x0 u : Vsp X.dim), x0 ∈ X.L → IsU I x0 u → ∀ n : ℝ, 1 ≤ n → 2 * Real.pi * ‖u‖ ≤ 1.5 * n →
    (∀ y ∈ X.L, ∀ uy, IsU I y uy → |2 * inner ℝ u uy| ≤ M1 (E := E) P.m * ‖uy‖ ^ 2) →
    ∃ s' ∈ X.Sec P.q 1, ∃ ζ : ℂ, ‖ζ‖ = 1 ∧
      (∀ xs : Fin c → Vsp X.dim, (∀ k, InPart σ (xs k) ∧ ‖xs k‖ = 1) →
        ‖d1 s' c xs - ζ * (2 * Real.pi) ^ c * ∏ k, Hf (xs k) u‖ ≤ P.eps1 * n ^ c) ∧
      P.K6⁻¹ * Real.exp (-(2 * Real.pi * ‖u‖ ^ 2 / P.q)) * X.l2 P.q s' ≤ n ^ (2 * c)

def ColAbelStatement : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (X : PT E) (DF : ℕ) (P : Par X DF)
    (I : Submodule ℤ (Vsp X.dim)), IsSplit P I → ∀ (c : ℕ), c ≤ DF → ∀ (σ : E →+* ℂ)
    (ξ : Vsp X.dim), InPart σ ξ → ‖ξ‖ = 1 → (∀ a ∈ I, Hf ξ a = 0) →
    ∃ s' ∈ X.Sec P.q 1,
      (∀ xs : Fin c → Vsp X.dim, (∀ k, InPart σ (xs k) ∧ ‖xs k‖ = 1) →
        ‖d1 s' c xs - (c.factorial : ℂ) * ∏ k, Hf (xs k) ξ‖ ≤ P.eps1 * c.factorial) ∧
      P.K6⁻¹ * X.l2 P.q s' ≤ (c.factorial : ℝ) ^ 2

def ColEmptyStatement : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (X : PT E) (DF : ℕ) (P : Par X DF)
    (I : Submodule ℤ (Vsp X.dim)), IsSplit P I →
    ∃ s' ∈ X.Sec P.q 1, 1 / 2 ≤ ‖s' 0‖ ∧ P.K6⁻¹ * X.l2 P.q s' ≤ 1

end

end ReciprocityTheory.ChartRestriction.G.I2
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TorusAt
section
namespace ReciprocityTheory.ChartRestriction.G.I2

open NumberField

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def IsTorusAt (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (x : ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r) (T : PT E) : Prop :=
  ∃ φ : (Fin r → E) →+ Vsp T.dim, ∃ s : ℝ, (s = 1 ∨ s = -1) ∧
    (∀ y, y ∈ T.L ↔ ∃ v ∈ X.Λ, φ v = y) ∧
    (∀ (α : 𝓞 E) (v : Fin r → E), φ ((α : E) • v) = act α (φ v)) ∧
    (∀ v ∈ X.Λ, ‖φ v‖ ^ 2 = ∑ τ : X.Ψ, X.c τ * X.maj x τ (ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ.1 v)) ∧
    (∀ u ∈ X.Λ, ∀ v ∈ X.Λ, (Hf (φ u) (φ v)).im =
      s * ((Algebra.trace ℚ E (X.ξ0 * ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm u v) : ℚ) : ℝ))

def phiFD (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (th : ℝ) (x : ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r) : ℝ :=
  if X.la1 x < th then 2 * PT.f E / (PT.rd E ^ 2 * X.la1 x ^ 2) else 0

def TorusAtLa1Statement : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r)
    (x : ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r), x ∈ X.dom → ∀ T : PT E, IsTorusAt X x T →
      T.la1 = X.la1 x ∧ ∀ th : ℝ, T.ph th = phiFD X th x

end

end ReciprocityTheory.ChartRestriction.G.I2
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.UnfoldZn
section
namespace ReciprocityTheory.ChartRestriction.G.I2

open MeasureTheory

noncomputable section

theorem unfold_Zn {d : ℕ} (g : (Fin d → ℝ) → ENNReal) :
    ∫⁻ x, g x = ∑' n : Fin d → ℤ, ∫⁻ x in cubeIco (Fin d), g (x + fun i => (n i : ℝ)) := by
  classical
  set b := Pi.basisFun ℝ (Fin d) with hb
  haveI : VAddInvariantMeasure (Submodule.span ℤ (Set.range b)) (Fin d → ℝ) volume :=
    ⟨fun c s _ => by
      show volume ((fun x => (c : Fin d → ℝ) + x) ⁻¹' s) = volume s
      exact measure_preimage_add _ _ _⟩
  have hF := ZSpan.isAddFundamentalDomain b (volume : Measure (Fin d → ℝ))
  have hdom : ZSpan.fundamentalDomain b = cubeIco (Fin d) := by
    ext x; simp [ZSpan.fundamentalDomain, cubeIco, b]
  rw [hF.lintegral_eq_tsum'', hdom]
  have hmem : ∀ n : Fin d → ℤ, (fun i => (n i : ℝ)) ∈ Submodule.span ℤ (Set.range b) := by
    intro n
    rw [Module.Basis.mem_span_iff_repr_mem]
    intro i; simp [b]
  let e : (Fin d → ℤ) → Submodule.span ℤ (Set.range b) := fun n => ⟨_, hmem n⟩
  have he : Function.Bijective e := by
    constructor
    · intro n m h
      funext i
      have := congrFun (congrArg Subtype.val h) i
      have h2 : (n i : ℝ) = m i := by simpa [e] using this
      exact_mod_cast h2
    · rintro ⟨y, hy⟩
      have hy' := hy
      rw [Module.Basis.mem_span_iff_repr_mem] at hy'
      choose n hn using hy'
      refine ⟨n, Subtype.ext ?_⟩
      funext i
      simpa [b, e] using hn i
  rw [← (Equiv.ofBijective e he).tsum_eq]
  congr 1; funext n
  congr 1; funext x
  show g ((fun i => (n i : ℝ)) + x) = _
  rw [add_comm]

theorem gauss_lin {d : ℕ} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [FiniteDimensional ℝ W] (ob : OrthonormalBasis (Fin d) ℝ W) (u b : Fin d → W)
    (hub : ∀ j i, inner ℝ (u j) (b i) = if j = i then (1 : ℝ) else 0) :
    ∫⁻ a : Fin d → ℝ, ENNReal.ofReal (Real.exp (-(2 * Real.pi) * ‖∑ j, a j • u j‖ ^ 2)) =
      ENNReal.ofReal (|ob.toBasis.det b| * (2 : ℝ) ^ (-(d : ℝ) / 2)) := by
  classical
  set M : Matrix (Fin d) (Fin d) ℝ := fun i j => ob.repr (u j) i with hM
  set B : Matrix (Fin d) (Fin d) ℝ := ob.toBasis.toMatrix b with hB
  have hMB : M.transpose * B = 1 := by
    ext j k
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, hM, hB,
      Module.Basis.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
      OrthonormalBasis.repr_apply_apply]
    rw [← hub j k, ← ob.sum_inner_mul_inner (u j) (b k)]
    refine Finset.sum_congr rfl fun i _ => ?_
    show inner ℝ (ob i) (u j) * _ = _
    rw [real_inner_comm (u j) (ob i)]
  have hdet : M.det * B.det = 1 := by
    have := congrArg Matrix.det hMB
    rwa [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at this
  have hdetB : ob.toBasis.det b = B.det := by rw [Module.Basis.det_apply]
  have hM0 : M.det ≠ 0 := left_ne_zero_of_mul_eq_one hdet
  have hnorm : ∀ a : Fin d → ℝ,
      ‖∑ j, a j • u j‖ = ‖(WithLp.toLp 2 (M.mulVec a) : EuclideanSpace ℝ (Fin d))‖ := by
    intro a
    rw [← ob.repr.norm_map]
    congr 1
    ext i
    set_option synthInstance.maxHeartbeats 100000 in
      simp [hM, Matrix.mulVec, dotProduct, map_sum, mul_comm]
  set G : (Fin d → ℝ) → ENNReal := fun y =>
    ENNReal.ofReal (Real.exp (-(2 * Real.pi) * ‖(WithLp.toLp 2 y : EuclideanSpace ℝ (Fin d))‖ ^ 2))
    with hG
  have hGm : Measurable G := by
    refine (Continuous.measurable ?_)
    exact ENNReal.continuous_ofReal.comp (Real.continuous_exp.comp
      (continuous_const.mul ((PiLp.continuous_toLp 2 _).norm.pow 2)))
  have hL : (fun a : Fin d → ℝ =>
      ENNReal.ofReal (Real.exp (-(2 * Real.pi) * ‖∑ j, a j • u j‖ ^ 2))) =
      fun a => G (Matrix.toLin' M a) := by
    funext a; simp only [hG, hnorm, Matrix.toLin'_apply]
  rw [hL, ← lintegral_map hGm (Matrix.toLin' M).continuous_of_finiteDimensional.measurable,
    Measure.map_linearMap_addHaar_eq_smul_addHaar _ (by rwa [LinearMap.det_toLin']),
    lintegral_smul_measure, LinearMap.det_toLin']
  have hE : ∫⁻ y, G y =
      ∫⁻ v : EuclideanSpace ℝ (Fin d), ENNReal.ofReal (Real.exp (-(2 * Real.pi) * ‖v‖ ^ 2)) := by
    have hp := MeasurePreserving.symm _
      (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin d))
    exact hp.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)
      (fun v : EuclideanSpace ℝ (Fin d) => ENNReal.ofReal (Real.exp (-(2 * Real.pi) * ‖v‖ ^ 2)))
  have hI : ∫ v : EuclideanSpace ℝ (Fin d), Real.exp (-(2 * Real.pi) * ‖v‖ ^ 2) =
      (2 : ℝ) ^ (-(d : ℝ) / 2) := by
    rw [GaussianFourier.integral_rexp_neg_mul_sq_norm (by positivity), finrank_euclideanSpace,
      Fintype.card_fin]
    have h2 : Real.pi / (2 * Real.pi) = (2 : ℝ)⁻¹ := by field_simp
    rw [h2, Real.inv_rpow (by norm_num), ← Real.rpow_neg (by norm_num), neg_div]
  have hint : Integrable (fun v : EuclideanSpace ℝ (Fin d) =>
      Real.exp (-(2 * Real.pi) * ‖v‖ ^ 2)) := by
    refine Integrable.of_integral_ne_zero ?_
    rw [hI]; positivity
  rw [hE, ← ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le), hI, smul_eq_mul,
    ← ENNReal.ofReal_mul (abs_nonneg _), hdetB, eq_inv_of_mul_eq_one_right hdet]

end

end ReciprocityTheory.ChartRestriction.G.I2
end

