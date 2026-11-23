module

public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0022
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0021
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0008
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0009
public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0005
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0018
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0017
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0071
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0016
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0015
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0019
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0011

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.CntCoord
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

noncomputable section

namespace PositivityTheory.HtPt.Ra

theorem smith : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (AA : HopfOrder (C := C) R (ι → ZMod p)), ∃ (Λ : Matrix ι ι R) (ε : ι → R), IsUnit Λ.det ∧ afLat p AA.carrier = Submodule.span R (Set.range fun j => ε j • Λ j) ∧ (∀ j, v (p : C) ≤ v (algebraMap R C (ε j)) ^ (p - 1)) ∧ HasLen v R (AFQuot p AA.carrier) (∏ j, v (algebraMap R C (ε j))) :=
  smith_of PositivityTheory.HtPt.Rh.aflat_fg PositivityTheory.HtPt.Rh.afquot

theorem cnt_coord : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (AA : HopfOrder (C := C) R (ι → ZMod p)), ∀ cA cN, HasLen v R (AFQuot p AA.carrier) cA → HasColen R v AA.carrier cN → cA ^ (Fintype.card (ι → ZMod p) * (p - 1)) ≤ cN ^ 2 ∧ (cA ^ (Fintype.card (ι → ZMod p) * (p - 1)) = cN ^ 2 → ∃ x : ι → (ι → ZMod p) → C, (∀ j, x j ∈ afFun p AA.carrier) ∧ AA.carrier = Submodule.span R (Set.range fun (α : ι → ZMod p) (y : ι → ZMod p) => ∏ j, x j y ^ (α j).val)) :=
  cnt_coord_of smith

theorem cnt : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N], (∀ x : N, p • x = 0) → ∀ AA : HopfOrder (C := C) R N, ∀ cA cN, HasLen v R (AFQuot p AA.carrier) cA → HasColen R v AA.carrier cN → cA ^ (Fintype.card N * (p - 1)) ≤ cN ^ 2 ∧ (cA ^ (Fintype.card N * (p - 1)) = cN ^ 2 → GenAF p AA.carrier ⊥) :=
  cnt_of cnt_coord

end PositivityTheory.HtPt.Ra
end
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.CoefMemDual
section
open Module NumberField GlobalTheory.CompanionTheory.Ar.HT TensorProduct Filter

namespace PositivityTheory.HtPt.Ge

section Loc
variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

def loc (B : Subalgebra o Ω) (u : Ω) (hu : u ∈ B) : Subring Ω where
  carrier := {a | ∃ n : ℕ, u ^ n * a ∈ B}
  one_mem' := ⟨0, by simp⟩
  zero_mem' := ⟨0, by simp⟩
  neg_mem' := fun ⟨n, h⟩ => ⟨n, by rw [mul_neg]; exact neg_mem h⟩
  mul_mem' := fun ⟨n, h⟩ ⟨n', h'⟩ => ⟨n + n', by
    have := mul_mem h h'
    rwa [mul_mul_mul_comm, ← pow_add] at this⟩
  add_mem' := fun {a b} ⟨n, h⟩ ⟨n', h'⟩ => ⟨n + n', by
    have := add_mem (mul_mem (pow_mem hu n') h) (mul_mem (pow_mem hu n) h')
    convert this using 1
    ring⟩

variable {B : Subalgebra o Ω} {u : Ω} {hu : u ∈ B}

theorem loc_of_mem {a : Ω} (h : a ∈ B) : a ∈ loc B u hu := ⟨0, by simpa using h⟩

theorem loc_ev {a : Ω} (h : a ∈ loc B u hu) : ∀ᶠ n in atTop, u ^ n * a ∈ B := by
  obtain ⟨n, h⟩ := h
  filter_upwards [eventually_ge_atTop n] with m hm
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm
  have := mul_mem (pow_mem hu d) h
  convert this using 1
  ring

theorem loc_of_pow {a : Ω} (n : ℕ) (h : u ^ n * a ∈ loc B u hu) : a ∈ loc B u hu := by
  obtain ⟨m, h⟩ := h
  exact ⟨m + n, by rwa [pow_add, mul_assoc]⟩

variable {V : Type} [AddCommGroup V] [Module Ω V]

def locM (M : Submodule B V) (u : Ω) (hu : u ∈ B) : AddSubgroup V where
  carrier := {v | ∃ n : ℕ, u ^ n • v ∈ M}
  zero_mem' := ⟨0, by simp⟩
  neg_mem' := fun ⟨n, h⟩ => ⟨n, by rw [smul_neg]; exact neg_mem h⟩
  add_mem' := fun {a b} ⟨n, h⟩ ⟨n', h'⟩ => ⟨n + n', by
    have := add_mem (M.smul_mem ⟨_, pow_mem hu n'⟩ h) (M.smul_mem ⟨_, pow_mem hu n⟩ h')
    simp only [Subalgebra.smul_def, smul_smul, ← pow_add] at this
    rwa [smul_add, add_comm n' n] at *⟩

theorem locM_smul {M : Submodule B V} {a : Ω} {v : V} (ha : a ∈ loc B u hu) (hv : v ∈ locM M u hu) :
    a • v ∈ locM M u hu := by
  obtain ⟨n, h⟩ := ha
  obtain ⟨n', h'⟩ := hv
  refine ⟨n + n', ?_⟩
  have := M.smul_mem ⟨_, h⟩ h'
  simp only [Subalgebra.smul_def, smul_smul] at this ⊢
  convert this using 2
  ring

theorem locM_ev {M : Submodule B V} {v : V} (h : v ∈ locM M u hu) : ∀ᶠ n in atTop, u ^ n • v ∈ M := by
  obtain ⟨n, h⟩ := h
  filter_upwards [eventually_ge_atTop n] with m hm
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm
  have := M.smul_mem ⟨_, pow_mem hu d⟩ h
  simp only [Subalgebra.smul_def, smul_smul] at this
  rwa [add_comm, pow_add]

theorem coef_mem [IsFractionRing B Ω] {P : Type} [AddCommGroup P] [Module B P] (ι : P →ₗ[B] V)
    (hι : Function.Injective ι) {k : ℕ} (b : Basis (Fin k) B P) (T : Fin k → Ω) (n : ℕ) (x : P)
    (e : u ^ n • ∑ a, T a • ι (b a) = ι x) (a : Fin k) : T a ∈ loc B u hu := by
  have h1 : LinearIndependent Ω (fun a => ι (b a)) :=
    (LinearIndependent.iff_fractionRing B Ω).1 (b.linearIndependent.map' ι (LinearMap.ker_eq_bot.2 hι))
  have h2 : ∑ a, (u ^ n * T a - (b.repr x a : Ω)) • ι (b a) = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib, mul_smul, ← Finset.smul_sum, e]
    have := congrArg ι (b.sum_repr x)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, Subalgebra.smul_def] at this
    rw [this, sub_self]
  have := Fintype.linearIndependent_iff.1 h1 _ h2 a
  exact ⟨n, by rw [sub_eq_zero.1 this]; exact (b.repr x a).2⟩

theorem coef_mem_dual [IsFractionRing B Ω] (W : Submodule B V) (hW : W.FG) {j : ℕ}
    (b : Basis (Fin j) B (Dual B W)) (φ : Fin j → Dual Ω V) (hφ : ∀ a (z : W), (b a z : Ω) = φ a z)
    (T : Fin j → Ω) (h : ∀ z ∈ W, (∑ a, T a • φ a) z ∈ loc B u hu) (a : Fin j) : T a ∈ loc B u hu := by
  set ψ := ∑ a, T a • φ a with hψ
  obtain ⟨S, hS⟩ := hW
  obtain ⟨n, hn⟩ := ((eventually_all_finset S).2 fun z hz =>
    loc_ev (h z (hS ▸ Submodule.subset_span hz))).exists
  have hn' : ∀ z ∈ W, u ^ n * ψ z ∈ B := by
    intro z hz
    rw [← hS] at hz
    induction hz using Submodule.span_induction with
    | mem x hx => exact hn x hx
    | zero => simp
    | add x y _ _ hx hy => rw [map_add (f := _), mul_add]; exact add_mem hx hy
    | smul c x _ hx =>
      rw [Subalgebra.smul_def, map_smul, smul_eq_mul, mul_left_comm]; exact mul_mem c.2 hx
  let x : Dual B W :=
    { toFun := fun z => ⟨_, hn' z z.2⟩
      map_add' := fun z z' => Subtype.ext (by simp [mul_add])
      map_smul' := fun c z => Subtype.ext (by simp [Subalgebra.smul_def, mul_left_comm]) }
  let ι : Dual B W →ₗ[B] (W → Ω) :=
    { toFun := fun f z => (f z : Ω)
      map_add' := fun f g => by ext z; simp
      map_smul' := fun c f => by ext z; simp [Subalgebra.smul_def] }
  refine coef_mem ι (fun f g e => LinearMap.ext fun z => Subtype.ext (congrFun e z)) b T n x ?_ a
  ext z
  simp [ι, x, hψ, hφ]

end Loc

theorem tri {Ω V : Type} [Field Ω] [AddCommGroup V] [Module Ω V] {n : ℕ} (w f g : Fin n → V) (df dg : Fin n → Ω)
    (hg0 : ∀ a, dg a ≠ 0)
    (hf : ∀ a, ∃ cf : Fin n → Ω, (∀ a', a < a' → cf a' = 0) ∧ cf a = df a ∧ f a = ∑ a', cf a' • w a')
    (hg : ∀ a, ∃ cf : Fin n → Ω, (∀ a', a < a' → cf a' = 0) ∧ cf a = dg a ∧ g a = ∑ a', cf a' • w a') :
    ∃ T : Matrix (Fin n) (Fin n) Ω, (∀ a' a, a < a' → T a' a = 0) ∧ (∀ a, T a a = df a / dg a) ∧
      ∀ a, f a = ∑ a', T a' a • g a' := by
  choose cf f1 f2 f3 using hf
  choose cg g1 g2 g3 using hg
  let F : Matrix (Fin n) (Fin n) Ω := Matrix.of fun a' a => cf a a'
  let G : Matrix (Fin n) (Fin n) Ω := Matrix.of fun a' a => cg a a'
  have hF : F.BlockTriangular id := fun a' a h => f1 a a' h
  have hG : G.BlockTriangular id := fun a' a h => g1 a a' h
  have hdet : IsUnit G.det := by
    rw [Matrix.det_of_upperTriangular hG, isUnit_iff_ne_zero, Finset.prod_ne_zero_iff]
    intro a _
    simpa [G, g2] using hg0 a
  haveI := G.invertibleOfIsUnitDet hdet
  have hT : (G⁻¹ * F).BlockTriangular id := (Matrix.blockTriangular_inv_of_blockTriangular hG).mul hF
  have e : G * (G⁻¹ * F) = F := Matrix.mul_nonsing_inv_cancel_left _ _ hdet
  refine ⟨G⁻¹ * F, fun a' a h => hT h, fun a => ?_, fun a => ?_⟩
  · have := congrFun (congrFun e a) a
    rw [Matrix.mul_apply, Finset.sum_eq_single a] at this
    · rw [eq_div_iff (hg0 a), ← g2, ← f2, mul_comm]
      exact this
    · intro l _ hl
      rcases lt_or_gt_of_ne hl with h | h
      · rw [hG h, zero_mul]
      · rw [hT h, mul_zero]
    · simp
  · simp only [g3, Finset.smul_sum, smul_smul]
    rw [f3, Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← Finset.sum_smul]
    congr 1
    have := congrFun (congrFun e l) a
    rw [Matrix.mul_apply] at this
    refine Eq.trans ?_ (this.symm.trans (Finset.sum_congr rfl fun _ _ => mul_comm _ _))
    rfl

section
variable {A K : Type} [CommRing A] [Field K] [Algebra A K] {E : Type} [Field E] [NumberField E]
  {c : E ≃+* E} {p R N : ℕ}
  {Ω : Type} [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω]
  (D : HTChart A K c p R N Ω)

theorem omHT_fg (σ : E →+* K) : (D.omHT σ).FG :=
  by apply _root_.UpperTheory.Reformulated.B.FinitelyGeneratedHomology.omHT_fg <;> assumption

end

end PositivityTheory.HtPt.Ge
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.DualUnique
section
noncomputable section

namespace PositivityTheory.HtPt.Ga

open Module NumberField GlobalTheory.CompanionTheory.Ar.HT TensorProduct

section

variable {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] {N : ℕ}

theorem dual_exists (y : Fin N → M) (t : A) (G H Z : Matrix (Fin N) (Fin N) A)
    (h : H * G = 1 + t • Z) :
    ∃ i : Module.Dual A M →ₗ[A] (Fin N → A), ∀ w j, ∃ z, ∑ l, i w l * G l j = w (y j) + t * z := by
  let ev : Module.Dual A M →ₗ[A] (Fin N → A) := LinearMap.pi fun j => Module.Dual.eval A M (y j)
  refine ⟨(Matrix.vecMulLinear H).comp ev, fun w j => ⟨Matrix.vecMul (ev w) Z j, ?_⟩⟩
  change Matrix.vecMul (Matrix.vecMul (ev w) H) G j = _
  rw [Matrix.vecMul_vecMul, h, Matrix.vecMul_add, Matrix.vecMul_one, Matrix.vecMul_smul]
  rfl

theorem dual_unique (t : A) (G H Z : Matrix (Fin N) (Fin N) A) (h : G * H = 1 + t • Z)
    (a a' r : Fin N → A) (ha : ∀ j, ∃ z, ∑ l, a l * G l j = r j + t * z)
    (ha' : ∀ j, ∃ z, ∑ l, a' l * G l j = r j + t * z) : ∃ x : Fin N → A, a = a' + t • x := by
  choose z hz using ha
  choose z' hz' using ha'
  have h1 : Matrix.vecMul (a - a') G = t • (z - z') := by
    ext j
    rw [Matrix.sub_vecMul]
    change ∑ l, a l * G l j - ∑ l, a' l * G l j = t * (z j - z' j)
    rw [hz, hz']
    ring
  have h2 := congrArg (fun v => Matrix.vecMul v H) h1
  simp only [Matrix.vecMul_vecMul, h, Matrix.vecMul_add, Matrix.vecMul_one, Matrix.vecMul_smul,
    Matrix.smul_vecMul] at h2
  refine ⟨Matrix.vecMul (z - z') H - Matrix.vecMul (a - a') Z, ?_⟩
  rw [smul_sub, ← h2]
  abel

theorem dual_split [Module.Projective A M] (y : Fin N → M) (t : A) (G : Matrix (Fin N) (Fin N) A)
    (hs : ∀ x : M, ∃ a : Fin N → A, ∃ x' : M, x = ∑ j, a j • y j + t • x')
    (i : Module.Dual A M →ₗ[A] (Fin N → A))
    (hi : ∀ w j, ∃ z, ∑ l, i w l * G l j = w (y j) + t * z) :
    ∃ r : (Fin N → A) →ₗ[A] Module.Dual A M, ∀ w, ∃ w', r (i w) = w + t • w' := by
  let f : ((Fin N → A) × M) →ₗ[A] M :=
    (Fintype.linearCombination A y).coprod (t • LinearMap.id)
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨a, x', e⟩ := hs x
    exact ⟨(a, x'), by rw [e]; simp [f, Fintype.linearCombination_apply]⟩
  obtain ⟨s, hs⟩ := Module.projective_lifting_property f LinearMap.id hf
  let s₁ := (LinearMap.fst A _ _).comp s
  let s₂ := (LinearMap.snd A _ _).comp s
  have hs' : ∀ x, ∑ j, s₁ x j • y j + t • s₂ x = x := by
    intro x
    have := LinearMap.congr_fun hs x
    simpa [f, s₁, s₂, Fintype.linearCombination_apply] using this
  let B : (Fin N → A) →ₗ[A] Module.Dual A M := (dotProductBilin A A).compl₂ s₁
  refine ⟨B.comp (Matrix.vecMulLinear G), fun w => ?_⟩
  choose z hz using hi w
  refine ⟨B z - w.comp s₂, ?_⟩
  ext x
  change ∑ j, (∑ l, i w l * G l j) * s₁ x j = w x + t * (∑ j, z j * s₁ x j - w (s₂ x))
  conv_rhs => rw [← hs' x]
  rw [hs' x]
  nth_rewrite 2 [← hs' x]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hz, map_add (f := _), map_sum, map_smul, smul_eq_mul, add_mul, Finset.sum_add_distrib, mul_sub,
    Finset.mul_sum, mul_assoc]
  simp only [mul_comm (w _)]
  ring

end

theorem dual_map : ∀ (A K : Type) [CommRing A] [Field K] [Algebra A K] [CharZero K] (hAK : Function.Injective (algebraMap A K)) (E : Type) [Field E] [NumberField E] (c : E ≃+* E) (hc : ∀ x, c (c x) = x) (p R N : ℕ) [Fact p.Prime] (Ω : Type) [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω] (D : HTChart A K c p R N Ω) (κ : A) (σ : E →+* K) (d : A) (m : ℕ), (∀ (σ : E →+* K) (a : 𝓞 E), σ (a : E) ∈ (algebraMap A K).range) → GeneratesDiff σ d → κ * (p : A) ^ m ∣ (p : A) ^ R → (∀ x ∈ D.om, κ • x ∈ D.om') → Module.Projective A (D.omHT (σ.comp c.toRingHom)) → (∃ (i : Module.Dual A (D.omHT (σ.comp c.toRingHom)) →ₗ[A] (Fin N → A)), D.IsDualMap σ d m i) ∧ (∀ i i', D.IsDualMap σ d m i → D.IsDualMap σ d m i' → ∀ w, ∃ x : Fin N → A, i w = i' w + ((p : A) ^ m) • x) ∧ ∀ i, D.IsDualMap σ d m i → ∃ r : (Fin N → A) →ₗ[A] Module.Dual A (D.omHT (σ.comp c.toRingHom)), ∀ w, ∃ w', r (i w) = w + ((p : A) ^ m) • w' := by
  intro A K _ _ _ _ hAK E _ _ c hc p R N _ Ω _ _ _ _ D κ σ d m hσ hd hκ hom hproj
  obtain ⟨G, H, Z, Z', hG, hGH, hHG⟩ := gram_unit A K hAK E c hc p R N Ω D σ d (hσ σ) hd
  obtain ⟨-, -, hsurj⟩ := q_surj A K hAK E c hc p R N Ω D κ (σ.comp c.toRingHom) m (hσ _) hκ hom
  obtain ⟨t, ht⟩ := hκ
  have hR : ∀ Y : Matrix (Fin N) (Fin N) A, ((p : A) ^ R) • Y = ((p : A) ^ m) • (κ * t) • Y := by
    intro Y
    rw [ht, smul_smul]
    congr 1
    ring
  rw [hR] at hGH hHG
  let y : Fin N → D.omHT (σ.comp c.toRingHom) := fun j =>
    ⟨_, proj_mem_omHT D (σ.comp c.toRingHom) (h_mem_om' D (Pi.single j 1))⟩
  have key : ∀ i, D.IsDualMap σ d m i ↔
      ∀ w j, ∃ z, ∑ l, i w l * G l j = w (y j) + (p : A) ^ m * z := by
    intro i
    constructor
    · intro h w j
      obtain ⟨z, hz⟩ := h w j (y j) rfl
      refine ⟨z, hAK ?_⟩
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← hz, map_sum]
      exact Finset.sum_congr rfl fun l _ => by rw [map_mul, hG]
    · intro h w j y' hy'
      obtain rfl : y' = y j := Subtype.ext hy'
      obtain ⟨z, hz⟩ := h w j
      refine ⟨z, ?_⟩
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← hz, map_sum]
      exact Finset.sum_congr rfl fun l _ => by rw [map_mul, hG]
  simp only [key]
  refine ⟨dual_exists y _ G H _ hHG, fun i i' hi hi' w =>
    dual_unique _ G H _ hGH _ _ (fun j => w (y j)) (hi w) (hi' w), fun i hi =>
    dual_split y _ G (fun x => ?_) i hi⟩
  obtain ⟨a, x', hx', e⟩ := hsurj x x.2
  refine ⟨a, ⟨x', hx'⟩, Subtype.ext ?_⟩
  rw [e, Submodule.coe_add, Submodule.coe_sum]
  rfl

end PositivityTheory.HtPt.Ga
end
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.FirstPowerZeroAt
section
noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

namespace PositivityTheory.HtPt.Cc

variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O] (B : FB R d O) {l : ℕ}

theorem pow_sy_at {x z : Pt R l d} (hx : Z x) (hz : Z z) (n : ℕ) :
    ev ![x, z] (pow2 B n) * ev ![x, z] B.sy ^ n =
      ev ![x, comp1 (B.A.act (n : O)) z] B.sy * ev ![z, x] (pow1 B n) := by
  induction n with
  | zero =>
    rw [act_zero_at, symmetric_zero_right_at B hx]
    simp only [second_power_zero, first_power_zero, ev_one, pow_zero, mul_one]
  | succ n ih =>
    rw [second_power_succ_at B n hx hz, first_power_succ_at B n hz hx, act_succ_at B n hz, pow_succ]
    have hl := sy_law_at B hx (Z_comp1 (Z_act B.A (n : O)) hz) hz
    linear_combination (ev ![x, comp1 (B.A.act (n : O)) z, z] B.ph2 * ev ![x, z] B.sy) * ih
      + ev ![z, x] (pow1 B n) * hl

theorem first_power_zero_at {x : Pt R l d} (hx : Z x) (m : ℕ) : ev ![x, 0] (pow1 B m) = 1 := by
  induction m with
  | zero => simp only [first_power_zero, ev_one]
  | succ k ih =>
    rw [first_power_succ_at B k hx Z_zero, ih, first_form_zero_right_at B (Z_comp1 (Z_act _ _) hx) hx, one_mul]

theorem first_power_add_at {x z w : Pt R l d} (hx : Z x) (hz : Z z) (hw : Z w) (m : ℕ) :
    ev ![x, z] (pow1 B m) * ev ![x, w] (pow1 B m) * ev ![comp1 (B.A.act (m : O)) x, z, w] B.ph2 =
      ev ![x, z, w] B.ph2 ^ m * ev ![x, addOf B.G.F z w] (pow1 B m) := by
  induction m with
  | zero => rw [act_zero_at, second_form_zero_left_at B hz hw, first_power_zero, ev_one, ev_one, ev_one]; simp
  | succ m ih =>
    have hm : Z (comp1 (B.A.act (m : O)) x) := Z_comp1 (Z_act B.A (m : O)) hx
    rw [first_power_succ_at B m hx hz, first_power_succ_at B m hx hw, first_power_succ_at B m hx (Z_add _ hz hw), act_succ_at B m hx,
      pow_succ]
    have h1 := interchange_at B hm hx hz hw
    linear_combination (ev ![x, z] (pow1 B m) * ev ![x, w] (pow1 B m)) * h1 +
      (ev ![x, z, w] B.ph2 * ev ![comp1 (B.A.act (m : O)) x, x, addOf B.G.F z w] B.ph1) * ih

theorem pow_inter_at {x z : Pt R l d} (hx : Z x) (hz : Z z) (m n : ℕ) :
    ev ![x, z] (pow2 B n) ^ m * ev ![x, comp1 (B.A.act (n : O)) z] (pow1 B m) =
      ev ![x, z] (pow1 B m) ^ n * ev ![comp1 (B.A.act (m : O)) x, z] (pow2 B n) := by
  induction n with
  | zero => rw [act_zero_at, first_power_zero_at B hx, second_power_zero, ev_one, ev_one]; simp
  | succ n ih =>
    have hn : Z (comp1 (B.A.act (n : O)) z) := Z_comp1 (Z_act B.A (n : O)) hz
    have hm : Z (comp1 (B.A.act (m : O)) x) := Z_comp1 (Z_act B.A (m : O)) hx
    rw [second_power_succ_at B n hx hz, second_power_succ_at B n hm hz, act_succ_at B n hz, pow_succ, mul_pow]
    have h1 := first_power_add_at B hx hn hz m
    linear_combination (-ev ![x, z] (pow2 B n) ^ m) * h1 +
      (ev ![x, z] (pow1 B m) * ev ![comp1 (B.A.act (m : O)) x, comp1 (B.A.act (n : O)) z, z] B.ph2) * ih

private theorem ev_ph1_mul_ev_lam_addOf_of_isIso {B B₂ : FB R d O} {φ ψ : Pt R 1 d} {lam : PS R 2 d} (h : IsIso B B₂ φ ψ lam)
    {X Y z : Pt R l d} (hX : Z X) (hY : Z Y) (hz : Z z) :
    ev ![X, Y, z] B₂.ph1 * ev ![addOf B₂.G.F X Y, z] lam
      = ev ![X, z] lam * ev ![Y, z] lam * ev ![comp1 φ X, comp1 φ Y, comp1 φ z] B.ph1 := by
  have hφ : Z φ := h.c₁
  have hb : ZZ ![X, Y, z] := ZZ_cons hX (ZZ_cons hY (ZZ_cons hz ZZ_nil))
  have e := congrArg (ev ![X, Y, z]) h.ph1
  simp only [FGLaw.add] at e
  simp only [ev_mul' hb] at e
  rw [ev_ev hb (ZZ_cons (Z_add B₂.G (Z_pt 0) (Z_pt 1)) (ZZ_cons (Z_pt 2) ZZ_nil)),
    ev_ev hb (ZZ_cons (Z_pt 0) (ZZ_cons (Z_pt 2) ZZ_nil)),
    ev_ev hb (ZZ_cons (Z_pt 1) (ZZ_cons (Z_pt 2) ZZ_nil)),
    ev_ev hb (ZZ_cons (Z_comp1 hφ (Z_pt 0)) (ZZ_cons (Z_comp1 hφ (Z_pt 1)) (ZZ_cons (Z_comp1 hφ (Z_pt 2)) ZZ_nil)))] at e
  simp only [evV_cons, evV_nil, evalPoints_coordinatePoint hb, evalPoints_add hb _ (Z_pt _) (Z_pt _), evalPoints_comp hb _ (Z_pt _)] at e
  simpa using e

private theorem ev_zero_lam_eq_one_of_isIso {B B₂ : FB R d O} {φ ψ : Pt R 1 d} {lam : PS R 2 d} (h : IsIso B B₂ φ ψ lam)
    {z : Pt R l d} (hz : Z z) : ev ![0, z] lam = 1 := by
  have hb : ZZ ![z] := ZZ_cons hz ZZ_nil
  have e := congrArg (ev ![z]) h.ax.1
  rw [ev_ev hb (ZZ_cons Z_zero (ZZ_cons (Z_pt 0) ZZ_nil)), ev_one] at e
  simpa [evV_cons, evV_nil, evalPoints_zero, evalPoints_coordinatePoint hb] using e

theorem iso_first_power_at {B} {B₂ : FB R d O} {φ ψ : Pt R 1 d} {lam : PS R 2 d} (h : IsIso B B₂ φ ψ lam)
    {x z : Pt R l d} (hx : Z x) (hz : Z z) (n : ℕ) :
    ev ![x, z] (pow1 B₂ n) * ev ![comp1 (B₂.A.act (n : O)) x, z] lam =
      ev ![x, z] lam ^ n * ev ![comp1 φ x, comp1 φ z] (pow1 B n) := by
  have hφ : Z φ := h.c₁
  induction n with
  | zero =>
    rw [act_zero_at, ev_zero_lam_eq_one_of_isIso h hz]
    simp only [first_power_zero, ev_one, pow_zero, mul_one]
  | succ n ih =>
    rw [first_power_succ_at B₂ n hx hz, act_succ_at B₂ n hx, first_power_succ_at B n (Z_comp1 hφ hx) (Z_comp1 hφ hz), pow_succ]
    have hP := ev_ph1_mul_ev_lam_addOf_of_isIso h (Z_comp1 (Z_act B₂.A (n : O)) hx) hx hz
    have hc : comp1 φ (comp1 (B₂.A.act (n : O)) x) = comp1 (B.A.act (n : O)) (comp1 φ x) := by
      rw [← germComp1_germComp1_eq_substitute φ (Z_act B₂.A _) hx, h.act, germComp1_germComp1_eq_substitute _ hφ hx]
    rw [hc] at hP
    linear_combination ev ![x, z] (pow1 B₂ n) * hP
      + (ev ![x, z] lam * ev ![comp1 (B.A.act (n : O)) (comp1 φ x), comp1 φ x, comp1 φ z] B.ph1) * ih

theorem pow_sy : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB R d O) (n : ℕ), pow2 B n * B.sy ^ n = ev (n := 2) ![pt R d 0, comp1 (B.A.act (n : O)) (pt R d 1)] B.sy * ev (n := 2) ![pt R d 1, pt R d 0] (pow1 B n) := by
  intro R _ d O _ _ B n
  have e := pow_sy_at B (Z_pt (R := R) (d := d) (0 : Fin 2)) (Z_pt 1) n
  simp only [eval_identity_two] at e
  exact e

theorem pow_inter : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB R d O) (m n : ℕ), pow2 B n ^ m * ev (n := 2) ![pt R d 0, comp1 (B.A.act (n : O)) (pt R d 1)] (pow1 B m) = pow1 B m ^ n * ev (n := 2) ![comp1 (B.A.act (m : O)) (pt R d 0), pt R d 1] (pow2 B n) := by
  intro R _ d O _ _ B m n
  have e := pow_inter_at B (Z_pt (R := R) (d := d) (0 : Fin 2)) (Z_pt 1) m n
  simp only [eval_identity_two] at e
  exact e

theorem iso_first_power : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB R d O) (B₂ : FB R d O) (φ ψ : Pt R 1 d) (lam : PS R 2 d) (n : ℕ), IsIso B B₂ φ ψ lam → pow1 B₂ n * ev (n := 2) ![comp1 (B₂.A.act (n : O)) (pt R d 0), pt R d 1] lam = lam ^ n * ev (n := 2) ![comp1 φ (pt R d 0), comp1 φ (pt R d 1)] (pow1 B n) := by
  intro R _ d O _ _ B B₂ φ ψ lam n h
  have e := iso_first_power_at h (Z_pt (R := R) (d := d) (0 : Fin 2)) (Z_pt 1) n
  simp only [eval_identity_two] at e
  exact e

end PositivityTheory.HtPt.Cc
end
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.MbLPulllocCentre
section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

namespace PositivityTheory.HtPt.Mb.LPulllocCentre

theorem pullLoc_eq_span_centre : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (E : Type) [AddCommGroup E] [Module Ω E] (L : Lat M.ξ E) (X' : Scheme.{0}) (Ω' : Type) [Field Ω'] (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (i : Ω →+* Ω') (F : Type) [AddCommGroup F] [Module Ω' F] (j : E →+ F) (p₀ : Cpt M.ξ) (p' : Cpt ξ'), L.IsCohOn Set.univ → ((∀ a ∈ regAt M.ξ p₀, i a ∈ regAt ξ' p') ∧ ∀ a ∈ regAt M.ξ p₀, unitAt ξ' p' (i a) → unitAt M.ξ p₀ a) → L.pullLoc ξ' i j p' = Submodule.span (regAt ξ' p') (j '' (L p₀ : Set E)) := by
  intro o _ Ω _ _ κ _ x M E _ _ L X' Ω' _ ξ' i F _ _ j p₀ p' hcoh hdom
  obtain ⟨hd1, hd2⟩ := hdom
  obtain ⟨c, hc⟩ := M.tie.cover p₀
  have hcx : x c ≠ 0 := hc.1
  have hch0 : ∀ a ∈ chRing o x c, a ∈ regAt M.ξ p₀ := fun a ha => (M.tie.ring c hcx a).1 ha p₀ hc
  have hctr : p' ∈ ctrSet o x i ξ' := ⟨c, hcx, fun a ha => hd1 a (hch0 a ha)⟩
  obtain ⟨p₁, ⟨h11, -⟩, h13, h14⟩ := PositivityTheory.HtPt.Mb.centre o Ω κ x M X' Ω' ξ' i p' hctr
  have hp1c : InChart M.ξ x c p₁ := h14 c hcx fun k => hd1 _ (hc.2 k)
  have hle : regAt M.ξ p₁ ≤ regAt M.ξ p₀ := by
    intro a ha
    obtain ⟨u, hu, v, hv, hvu, rfl⟩ := ((PositivityTheory.HtPt.Ma.regat_loc o Ω κ x M c p₁ hp1c).2 a).1 ha
    have hiv : unitAt ξ' p' (i v) :=
      ⟨(map_ne_zero i).2 hvu.1, h11 _ hvu.2.1, by rw [← map_inv₀]; exact h11 _ hvu.2.2⟩
    have hv0 : unitAt M.ξ p₀ v := hd2 v (hch0 v hv) hiv
    rw [div_eq_mul_inv]
    exact mul_mem (hch0 u hu) hv0.2.2
  have hsp : p₀.1 ⤳ p₁.1 := (PositivityTheory.HtPt.Ma.reg_le_spec o Ω κ x M p₁ p₀).1 hle
  have hstalk : ∀ p : Cpt M.ξ, (∀ a ∈ regAt M.ξ p, i a ∈ regAt ξ' p') → ∀ e ∈ L p, e ∈ L p₀ := by
    intro p hp e he
    have hs : p₀.1 ⤳ p.1 := hsp.trans (h13 p hp)
    obtain ⟨U, hU, n, b, hb⟩ := hcoh p (Set.mem_univ p)
    have h0U : p₀.1 ∈ U := hs.mem_open U.isOpen hU
    have hreg : regAt M.ξ p ≤ regAt M.ξ p₀ := (PositivityTheory.HtPt.Ma.reg_le_spec o Ω κ x M p p₀).2 hs
    rw [hb p (Set.mem_univ p) hU] at he
    rw [hb p₀ (Set.mem_univ p₀) h0U]
    induction he using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span hy
    | zero => exact zero_mem _
    | add y z _ _ hy hz => exact add_mem hy hz
    | smul a y _ hy => exact Submodule.smul_mem _ (⟨a, hreg a.2⟩ : regAt M.ξ p₀) hy
  exact Lat.pullLoc_eq_span_of_ctr j ⟨hd1, hd2⟩ fun p hp => hstalk p hp.1

end PositivityTheory.HtPt.Mb.LPulllocCentre


open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField in
theorem PositivityTheory.HtPt.Mb.pullloc_centre : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (E : Type) [AddCommGroup E] [Module Ω E] (L : Lat M.ξ E) (X' : Scheme.{0}) (Ω' : Type) [Field Ω'] (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (i : Ω →+* Ω') (F : Type) [AddCommGroup F] [Module Ω' F] (j : E →+ F) (p₀ : Cpt M.ξ) (p' : Cpt ξ'), L.IsCohOn Set.univ → ((∀ a ∈ regAt M.ξ p₀, i a ∈ regAt ξ' p') ∧ ∀ a ∈ regAt M.ξ p₀, unitAt ξ' p' (i a) → unitAt M.ξ p₀ a) → L.pullLoc ξ' i j p' = Submodule.span (regAt ξ' p') (j '' (L p₀ : Set E)) :=
  @PositivityTheory.HtPt.Mb.LPulllocCentre.pullLoc_eq_span_centre
end

