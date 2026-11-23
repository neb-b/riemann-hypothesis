module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0012
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1162
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2061
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1128
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2047

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicValIntDiscrDivLeDeltaVp
section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal UpperHalfPlane ReciprocityTheory.ChartRestriction.L1
open scoped UpperHalfPlane

namespace GlobalTheory.DiscrTower

theorem finrank_mul_padicValInt_discr_le (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (l : ℕ) (hl : l.Prime) :
    Module.finrank K L * padicValInt l (discr K) ≤ padicValInt l (discr L) := by
  haveI : Fact l.Prime := ⟨hl⟩
  have h := natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow K (𝓞 K) L (𝓞 L)
  have hL : (discr L).natAbs ≠ 0 := Int.natAbs_ne_zero.2 (discr_ne_zero L)
  rw [h] at hL
  unfold padicValInt
  rw [h, Nat.multiplicity_mul (left_ne_zero_of_mul hL) (right_ne_zero_of_mul hL),
    Nat.multiplicity_pow]
  omega

theorem padicValInt_discr_div_le_delta_vp :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l : ℕ), l.Prime →
      (padicValInt l (discr (maximalRealSubfield E)) : ℝ) / Module.finrank ℚ (maximalRealSubfield E) ≤
        GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.delta_vp E l := by
  intro E _ _ _ l hl
  have h := finrank_mul_padicValInt_discr_le (maximalRealSubfield E) E l hl
  have h2 := (letI : Module.Free (maximalRealSubfield E) E := Module.Free.of_divisionRing _ _; Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E)
  have hF : (0 : ℝ) < Module.finrank ℚ (maximalRealSubfield E) := by exact_mod_cast Module.finrank_pos
  have hE : (0 : ℝ) < Module.finrank ℚ E := by exact_mod_cast Module.finrank_pos
  unfold GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.delta_vp
  rw [div_le_div_iff₀ hF hE, ← h2]
  have h' : (Module.finrank (maximalRealSubfield E) E : ℝ) * padicValInt l (discr (maximalRealSubfield E)) ≤
      padicValInt l (discr E) := by exact_mod_cast h
  push_cast
  nlinarith

end GlobalTheory.DiscrTower
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairSectionMemBallExpOfProjArithVariety
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSNef

theorem sec_nsq_le {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {D : ℕ} (hX : IsArithVar p D)
    (M : HermLB p) (u : M.B.Sec) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (σ : k →+* ℂ) (y : CxPts p σ), (M.φ σ).nsq (CxPts.secVal p σ u) y ≤ C := by
  have := hX.finite_emb
  have hb : ∀ σ : k →+* ℂ, ∃ K : ℝ, ∀ y, (M.φ σ).nsq (CxPts.secVal p σ u) y ≤ K := fun σ => by
    have := hX.compactSpace σ
    obtain ⟨K, hK⟩ := (isCompact_range ((M.cInf σ).continuous_nsq u)).bddAbove
    exact ⟨K, fun y => hK ⟨y, rfl⟩⟩
  choose K hK using hb
  have := Fintype.ofFinite (k →+* ℂ)
  refine ⟨∑ τ, |K τ| + 1, ?_, fun σ y => (hK σ y).trans ?_⟩
  · linarith [Finset.sum_nonneg fun τ (_ : τ ∈ Finset.univ) => abs_nonneg (K τ)]
  · have := Finset.single_le_sum (fun τ (_ : τ ∈ Finset.univ) => abs_nonneg (K τ)) (Finset.mem_univ σ)
    linarith [le_abs_self (K σ)]

theorem bounded_norm : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D →
    ∀ (P : Pair p) (a b : ℤ) (f : X.functionField), f ∈ P.H a b → ∃ u : ℝ, 0 ≤ u ∧ f ∈ P.Bl a b (Real.exp u) := by
  intro k _ X _ p D hX P a b f hf
  obtain ⟨M, hM⟩ := _root_.GlobalTheory.VolBr.Pair.exists_rep k X p P a b
  obtain ⟨e, -, hrng, hnu, -⟩ := GlobalTheory.VolBr.RepDict.rep_dict k X p P a b M hM
  obtain ⟨u, rfl⟩ : f ∈ Set.range e := by rw [hrng]; exact hf
  obtain ⟨C, hC1, hC⟩ := sec_nsq_le hX M u
  refine ⟨Real.log C, Real.log_nonneg hC1, hf, fun σ y => ?_⟩
  rw [Real.exp_log (by linarith)]
  have h1 := hnu u σ y
  have h2 := hC σ y
  have h3 : 0 ≤ P.nu a b σ y (e u) := by unfold Pair.nu; positivity
  nlinarith

end GlobalTheory.HSNef
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairSectionsFgOfProjArithVariety
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.HSNef.PairFG

theorem exists_hom {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} (P : Pair p) (a b : ℤ)
    (M : HermLB p) (hM : P.Rep a b M) :
    ∃ φ : M.B.Sec →+ X.functionField, φ.range = P.H a b := by
  obtain ⟨ρ, hρ, hu, -⟩ := hM
  obtain ⟨e, he⟩ := RepDict.exists_quot M.isLB hρ
  have hcov {B : LB X} (hB : B.IsLB) (x : X) : ∃ c, x ∈ B.U c :=
    Opens.mem_iSup.1 (hB.cover.ge (Opens.mem_top _))
  obtain ⟨c₀, h₀⟩ := hcov M.isLB (genericPoint X)
  have hρ₀ := (ρ c₀).ne_zero
  let φ : M.B.Sec →+ X.functionField :=
    { toFun := e
      map_zero' := by
        refine mul_right_cancel₀ hρ₀ ?_
        rw [he 0 c₀ h₀, zero_mul]
        exact map_zero _
      map_add' := fun u v => by
        refine mul_right_cancel₀ hρ₀ ?_
        rw [he (u + v) c₀ h₀, add_mul, he u c₀ h₀, he v c₀ h₀]
        exact map_add _ _ _ }
  have hl (f : X.functionField) c i j :
      P.loc a b f i j * ((ρ c : X.functionField) / P.loc a b 1 i j) = f * ρ c := by
    have := (P.r i).ne_zero
    have := (P.r' j).ne_zero
    simp only [Pair.loc]
    field_simp
  have hl' (f : X.functionField) c i j :
      P.loc a b f i j = f * ρ c * ((ρ c : X.functionField) / P.loc a b 1 i j)⁻¹ := by
    have := (P.r i).ne_zero
    have := (P.r' j).ne_zero
    have := (ρ c).ne_zero
    simp only [Pair.loc]
    field_simp
  refine ⟨φ, le_antisymm ?_ fun f hf => ?_⟩
  · rintro _ ⟨u, rfl⟩ x i j hi hj
    obtain ⟨c, hc⟩ := hcov M.isLB x
    change RegAt x (P.loc a b (e u) i j)
    rw [hl' _ c, he u c (gen_mem hc)]
    exact (regAt_fnOf hc _ _).mul (hu x c i j hc hi hj).inv.regAt
  · obtain ⟨u, hu'⟩ := RepDict.exists_sec hρ (f := f) fun c x hc => by
      obtain ⟨i, hi⟩ := hcov P.L.isLB x
      obtain ⟨j, hj⟩ := hcov P.A.isLB x
      rw [← hl f c i j]
      exact (hf x i j hi hj).mul (hu x c i j hc hi hj).regAt
    exact ⟨u, mul_right_cancel₀ hρ₀ ((he u c₀ h₀).trans (hu' c₀ h₀))⟩

theorem h_fg : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D →
    ∀ (P : Pair p) (a b : ℤ), (P.H a b).FG := by
  intro k _ X _ p D hX P a b
  obtain ⟨M, hM⟩ := _root_.GlobalTheory.VolBr.Pair.exists_rep k X p P a b
  obtain ⟨φ, hφ⟩ := exists_hom P a b M hM
  have := _root_.GlobalTheory.addGroupFG_sec_of_isArithVar k X p D hX M.B M.isLB
  rw [← hφ, AddMonoidHom.range_eq_map]
  obtain ⟨S, hS, hfin⟩ := AddGroup.fg_iff.mp this
  apply (AddSubgroup.fg_iff _).mpr
  refine ⟨(φ : M.B.Sec → X.functionField) '' S, ?_, hfin.image φ⟩
  rw [← AddMonoidHom.map_closure, hS]

end GlobalTheory.HSNef.PairFG
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PdPolynomialCompatibleFormsGeneratedInduction
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.PDForm

theorem rel_mul_mem_right {R B : Type} [CommRing R] [CommRing B] [Algebra R B] {J : Ideal B}
    (δ : DividedPowers J) {x : DR R B} (hx : x ∈ rel R δ) (y : DR R B) : x * y ∈ rel R δ := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨n, a, ha, rfl⟩ := hx
    rw [ι_mul]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨n, a, ha, rfl⟩)
  | zero => simp
  | add x z _ _ hx hz => rw [add_mul]; exact add_mem hx hz
  | smul a x _ ih => rw [smul_eq_mul, mul_assoc]; exact Ideal.mul_mem_left _ _ ih

section Poly

variable {R B : Type} [CommRing R] [CommRing B] [Algebra R B] {J : Ideal B}
  {Q : PDPoly B} [Algebra R Q.P] [IsScalarTower R B Q.P] (η : DividedPowers (Q.ext J))
  (h : SemiHom (RingHom.id R) (algebraMap B Q.P))

def pdGen : Set (DR R Q.P) :=
  {x | ∃ n α, x = Q.e n • h.mDR α} ∪ {x | ∃ n α, x = Q.e n • (ι1 (D R Q.P (Q.e 1)) * h.mDR α)} ∪
    (rel R η : Set (DR R Q.P))

theorem pdGen_mem_one (n : ℕ) (α : DR R B) : Q.e n • h.mDR α ∈ pdGen η h :=
  Set.mem_union_left _ (Set.mem_union_left _ ⟨n, α, rfl⟩)

theorem pdGen_mem_two (n : ℕ) (α : DR R B) : Q.e n • (ι1 (D R Q.P (Q.e 1)) * h.mDR α) ∈ pdGen η h :=
  Set.mem_union_left _ (Set.mem_union_right _ ⟨n, α, rfl⟩)

theorem pdGen_mem_rel {x : DR R Q.P} (hx : x ∈ rel R η) : x ∈ pdGen η h :=
  Set.mem_union_right _ hx

theorem smul_gen_mem (b : Q.P) : ∀ α : DR R B,
    b • h.mDR α ∈ AddSubgroup.closure (pdGen η h) ∧
      b • (ι1 (D R Q.P (Q.e 1)) * h.mDR α) ∈ AddSubgroup.closure (pdGen η h) := by
  have hb : b ∈ Submodule.span B (Set.range Q.e) := by rw [Q.e.span_eq]; trivial
  induction hb using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨n, rfl⟩ := hx
    exact fun α ↦ ⟨AddSubgroup.subset_closure (pdGen_mem_one η h n α),
      AddSubgroup.subset_closure (pdGen_mem_two η h n α)⟩
  | zero => intro α; simp only [zero_smul]; exact ⟨zero_mem _, zero_mem _⟩
  | add x y _ _ hx hy =>
    intro α
    rw [add_smul, add_smul]
    exact ⟨add_mem (hx α).1 (hy α).1, add_mem (hx α).2 (hy α).2⟩
  | smul c x _ ih =>
    intro α
    have e1 : (c • x) • h.mDR α = x • h.mDR (c • α) := by
      rw [h.mDR_smul, Algebra.smul_def c x, mul_comm, mul_smul]
    have e2 : (c • x) • (ι1 (D R Q.P (Q.e 1)) * h.mDR α) = x • (ι1 (D R Q.P (Q.e 1)) * h.mDR (c • α)) := by
      rw [h.mDR_smul, mul_smul_comm, Algebra.smul_def c x, mul_comm, mul_smul]
    rw [e1, e2]
    exact ih (c • α)

theorem smul_mem_closure (b : Q.P) {x : DR R Q.P} (hx : x ∈ AddSubgroup.closure (pdGen η h)) :
    b • x ∈ AddSubgroup.closure (pdGen η h) := by
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    rcases hx with (⟨n, α, rfl⟩ | ⟨n, α, rfl⟩) | hx
    · rw [smul_smul]; exact (smul_gen_mem η h _ α).1
    · rw [smul_smul]; exact (smul_gen_mem η h _ α).2
    · refine AddSubgroup.subset_closure (pdGen_mem_rel η h ?_)
      rw [Algebra.smul_def]; exact Ideal.mul_mem_left _ _ hx
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

theorem D_mem_closure {δ : DividedPowers J} (hs : Q.IsStd δ η) (b : Q.P) :
    ι1 (D R Q.P b) ∈ AddSubgroup.closure (pdGen η h) := by
  have hb : b ∈ Submodule.span B (Set.range Q.e) := by rw [Q.e.span_eq]; trivial
  induction hb using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨n, rfl⟩ := hx
    cases n with
    | zero => rw [Q.e_zero, Derivation.map_one_eq_zero, map_zero]; exact zero_mem _
    | succ n =>
      have hr : ι1 (D R Q.P (η.dpow (n + 1) (Q.e 1)) - η.dpow n (Q.e 1) • D R Q.P (Q.e 1)) ∈ rel R η :=
        Ideal.subset_span ⟨n, Q.e 1, Q.e_one_mem_ext J, rfl⟩
      rw [hs.var, hs.var] at hr
      have e : ι1 (D R Q.P (Q.e (n + 1))) = ι1 (D R Q.P (Q.e (n + 1)) - Q.e n • D R Q.P (Q.e 1)) +
          Q.e n • (ι1 (D R Q.P (Q.e 1)) * h.mDR 1) := by
        rw [map_one h.mDR, mul_one, map_sub, map_smul, sub_add_cancel]
      rw [e]
      exact add_mem (AddSubgroup.subset_closure (pdGen_mem_rel η h hr))
        (AddSubgroup.subset_closure (pdGen_mem_two η h n 1))
  | zero => rw [map_zero, map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add (f := _), map_add (f := _)]; exact add_mem hx hy
  | smul c x _ ih =>
    rw [Algebra.smul_def, Derivation.leibniz, map_add (f := _), map_smul, map_smul]
    refine add_mem (smul_mem_closure η h _ ih) ?_
    have e : ι1 (D R Q.P (algebraMap B Q.P c)) = h.mDR (ι1 (D R B c)) := by rw [h.mDR_ι, h.m1_D]
    rw [e]; exact (smul_gen_mem η h x _).1


omit [IsScalarTower R B Q.P] in
theorem mDR_mul_dtau (α β : DR R B) :
    h.mDR α * (ι1 (D R Q.P (Q.e 1)) * h.mDR β) = ι1 (D R Q.P (Q.e 1)) * h.mDR (sgn α * β) := by
  rw [← mul_assoc, map_mul, h.mDR_sgn, ← mul_assoc, ι_mul (D R Q.P (Q.e 1)) (sgn (h.mDR α)), sgn_sgn]

theorem gen_mul_gen {x y : DR R Q.P} (hx : x ∈ pdGen η h) (hy : y ∈ pdGen η h) :
    x * y ∈ AddSubgroup.closure (pdGen η h) := by
  have base : ∀ α : DR R B, h.mDR α ∈ AddSubgroup.closure (pdGen η h) := fun α ↦ by
    have := (smul_gen_mem η h 1 α).1; rwa [one_smul] at this
  have base2 : ∀ α : DR R B, ι1 (D R Q.P (Q.e 1)) * h.mDR α ∈ AddSubgroup.closure (pdGen η h) := fun α ↦ by
    have := (smul_gen_mem η h 1 α).2; rwa [one_smul] at this
  have relL : ∀ {z : DR R Q.P} (w : DR R Q.P), z ∈ rel R η → w * z ∈ AddSubgroup.closure (pdGen η h) :=
    fun w hz ↦ AddSubgroup.subset_closure (pdGen_mem_rel η h (Ideal.mul_mem_left _ w hz))
  rcases hx with (⟨m, α, rfl⟩ | ⟨m, α, rfl⟩) | hx
  · rcases hy with (⟨n, β, rfl⟩ | ⟨n, β, rfl⟩) | hy
    · rw [smul_mul_assoc, mul_smul_comm, ← map_mul]
      exact smul_mem_closure η h _ (smul_mem_closure η h _ (base _))
    · rw [smul_mul_assoc, mul_smul_comm, mDR_mul_dtau]
      exact smul_mem_closure η h _ (smul_mem_closure η h _ (base2 _))
    · exact relL _ hy
  · rcases hy with (⟨n, β, rfl⟩ | ⟨n, β, rfl⟩) | hy
    · rw [smul_mul_assoc, mul_smul_comm, mul_assoc, ← map_mul]
      exact smul_mem_closure η h _ (smul_mem_closure η h _ (base2 _))
    · rw [smul_mul_assoc, mul_smul_comm, mul_assoc, mDR_mul_dtau, ← mul_assoc, ExteriorAlgebra.ι_sq_zero,
        zero_mul, smul_zero, smul_zero]
      exact zero_mem _
    · exact relL _ hy
  · exact AddSubgroup.subset_closure (pdGen_mem_rel η h (rel_mul_mem_right η hx _))

theorem mul_mem_closure {x y : DR R Q.P} (hx : x ∈ AddSubgroup.closure (pdGen η h))
    (hy : y ∈ AddSubgroup.closure (pdGen η h)) : x * y ∈ AddSubgroup.closure (pdGen η h) := by
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    induction hy using AddSubgroup.closure_induction with
    | mem y hy => exact gen_mul_gen η h hx hy
    | zero => rw [mul_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [mul_add]; exact add_mem hy hz
    | neg y _ hy => rw [mul_neg]; exact neg_mem hy
  | zero => rw [zero_mul]; exact zero_mem _
  | add x z _ _ hx hz => rw [add_mul]; exact add_mem hx hz
  | neg x _ hx => rw [neg_mul]; exact neg_mem hx

end Poly

theorem pdPoly_forms_induction : ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (J : Ideal B)
    (δ : DividedPowers J) (Q : PDPoly B) [Algebra R Q.P] [IsScalarTower R B Q.P] (η : DividedPowers (Q.ext J))
    (v : Derivation R Q.P Q.P) (h : SemiHom (RingHom.id R) (algebraMap B Q.P)), Q.IsStd δ η →
    (∀ b, v (algebraMap B Q.P b) = 0) → (∀ n, v (Q.e (n + 1)) = Q.e n) →
    (∀ n, ∀ a ∈ Q.ext J, v (η.dpow (n + 1) a) = η.dpow n a * v a) → ∀ (p : DR R Q.P → Prop),
    (∀ x ∈ rel R η, p x) → (∀ x y, p x → p y → p (x + y)) → (∀ n α, p (Q.e n • h.mDR α)) →
    (∀ n α, p (Q.e n • (ι1 (D R Q.P (Q.e 1)) * h.mDR α))) → ∀ x, p x := by
  intro R B _ _ _ J δ Q _ _ η _ h hs _ _ _ p hrel hadd h1 h2 x
  have hS : ∀ x, x ∈ AddSubgroup.closure (pdGen η h) := fun x ↦ by
    induction x using indDR with
    | h b =>
      have := (smul_gen_mem η h b 1).1
      rwa [map_one, ← Algebra.algebraMap_eq_smul_one] at this
    | hd b => exact D_mem_closure η h hs b
    | hm x y hx hy => exact mul_mem_closure η h hx hy
    | ha x y hx hy => exact add_mem hx hy
  have key : ∀ x ∈ AddSubgroup.closure (pdGen η h), p x ∧ p (-x) := by
    intro x hx
    induction hx using AddSubgroup.closure_induction with
    | mem x hx =>
      rcases hx with (⟨n, α, rfl⟩ | ⟨n, α, rfl⟩) | hx
      · exact ⟨h1 n α, by rw [← smul_neg, ← map_neg]; exact h1 n (-α)⟩
      · exact ⟨h2 n α, by rw [← smul_neg, ← mul_neg, ← map_neg]; exact h2 n (-α)⟩
      · exact ⟨hrel x hx, hrel _ (neg_mem hx)⟩
    | zero => exact ⟨hrel 0 (zero_mem _), by rw [neg_zero]; exact hrel 0 (zero_mem _)⟩
    | add x y _ _ hx hy => exact ⟨hadd _ _ hx.1 hy.1, by rw [neg_add]; exact hadd _ _ hx.2 hy.2⟩
    | neg x _ hx => exact ⟨hx.2, by rw [neg_neg]; exact hx.1⟩
  exact (key x (hS x)).1

end GlobalTheory.PDForm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PinchingSquareUnitsPatch
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.Pinch

theorem germ_app_congr {Y X : Scheme.{0}} {f g : Y ⟶ X} (e : f = g) (W : X.Opens) (y : Y) (hf : f y ∈ W)
    (hg : g y ∈ W) (s : Γ(X, W)) :
    Y.presheaf.germ (f ⁻¹ᵁ W) y hf ((f.app W).hom s) = Y.presheaf.germ (g ⁻¹ᵁ W) y hg ((g.app W).hom s) := by
  subst e; rfl

theorem affine_descent_units : ∀ (X X' Z Z' : Scheme.{0}) (p : X' ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ X') (p' : Z' ⟶ Z),
    IsPullback i' p' p i → IsAffineHom p → IsClosedImmersion i → GlobalTheory.Pinch.Cond p i →
    ∀ W : X.Opens, IsAffineOpen W → ∀ (u' : Γ(X', p ⁻¹ᵁ W)ˣ) (v : Γ(Z, i ⁻¹ᵁ W)ˣ),
      (∀ z : Z', p (i' z) ∈ W → gm i' z (p ⁻¹ᵁ W) u' = gm p' z (i ⁻¹ᵁ W) v) →
      ∃ u : Γ(X, W)ˣ, pullU p W u = u' := by
  intro X X' Z Z' p i i' p' h hp hi hc W hW u' v huv
  have hw : ∀ z : Z', p (i' z) = i (p' z) := fun z => by
    have := congrArg (fun f : Z' ⟶ X => f z) h.w
    simpa using this
  have claim : ∀ (s' : Γ(X', p ⁻¹ᵁ W)) (t : Γ(Z, i ⁻¹ᵁ W)),
      (∀ z : Z', ∀ hz : p (i' z) ∈ W,
        Z'.presheaf.germ (i' ⁻¹ᵁ (p ⁻¹ᵁ W)) z hz ((i'.app (p ⁻¹ᵁ W)).hom s') =
          Z'.presheaf.germ (p' ⁻¹ᵁ (i ⁻¹ᵁ W)) z (show i (p' z) ∈ W from hw z ▸ hz) ((p'.app (i ⁻¹ᵁ W)).hom t)) →
      ∃ s : Γ(X, W), (p.app W).hom s = s' := by
    intro s' t hst
    obtain ⟨s₀, rfl⟩ := Scheme.Hom.app_surjective i W hW t
    have hd : (i'.app (p ⁻¹ᵁ W)).hom (s' - (p.app W).hom s₀) = 0 := by
      apply TopCat.Presheaf.section_ext Z'.sheaf
      intro z hz
      show (Z'.presheaf.germ (i' ⁻¹ᵁ p ⁻¹ᵁ W) z hz).hom ((i'.app (p ⁻¹ᵁ W)).hom (s' - (p.app W).hom s₀)) =
        (Z'.presheaf.germ (i' ⁻¹ᵁ p ⁻¹ᵁ W) z hz).hom 0
      rw [map_sub, map_sub, map_zero, sub_eq_zero, hst z hz]
      have e1 := germ_app_congr h.w W z hz (show i (p' z) ∈ W from hw z ▸ hz) s₀
      exact e1.symm
    have hmem := _root_.GlobalTheory.closedImmersion_baseChange_ker_mem_map X X' Z Z' p i i' p' h hp hi W hW _ hd
    have key : ∃ y, (i.app W).hom y = 0 ∧ (p.app W).hom y = s' - (p.app W).hom s₀ := by
      refine Submodule.span_induction (p := fun x _ => ∃ y, (i.app W).hom y = 0 ∧ (p.app W).hom y = x)
        ?_ ?_ ?_ ?_ hmem
      · rintro _ ⟨y, hy, rfl⟩
        exact ⟨y, hy, rfl⟩
      · exact ⟨0, map_zero _, map_zero _⟩
      · rintro _ _ _ _ ⟨y₁, h₁, e₁⟩ ⟨y₂, h₂, e₂⟩
        exact ⟨y₁ + y₂, by rw [map_add (f := _), h₁, h₂, add_zero], by rw [map_add (f := _), e₁, e₂]⟩
      · rintro r _ _ ⟨y, hy, rfl⟩
        obtain ⟨y', hy', e'⟩ := (hc W hW).2 y hy r
        exact ⟨y', hy', by rw [smul_eq_mul, mul_comm]; exact e'⟩
    obtain ⟨y, -, hy⟩ := key
    exact ⟨s₀ + y, by rw [map_add (f := _), hy, add_sub_cancel]⟩
  have germs : ∀ (a : Γ(X', p ⁻¹ᵁ W)ˣ) (b : Γ(Z, i ⁻¹ᵁ W)ˣ),
      (∀ z : Z', p (i' z) ∈ W → gm i' z (p ⁻¹ᵁ W) a = gm p' z (i ⁻¹ᵁ W) b) →
      ∃ s : Γ(X, W), (p.app W).hom s = a.val := by
    intro a b hab
    refine claim a.val b.val fun z hz => ?_
    have := congrArg Units.val (hab z hz)
    rwa [gm_val i' z _ hz, gm_val p' z _ (show i (p' z) ∈ W from hw z ▸ hz)] at this
  obtain ⟨x, hx⟩ := germs u' v huv
  obtain ⟨y, hy⟩ := germs u'⁻¹ v⁻¹ fun z hz => by rw [map_inv, map_inv, huv z hz]
  have hxy : x * y = 1 := (hc W hW).1 (by
    show (p.app W).hom (x * y) = (p.app W).hom 1
    rw [map_mul, map_one, hx, hy, Units.mul_inv])
  exact ⟨⟨x, y, hxy, by rw [mul_comm]; exact hxy⟩, Units.ext hx⟩

theorem pullU_injective {X X' : Scheme.{0}} (p : X' ⟶ X)
    (hp : ∀ W : X.Opens, IsAffineOpen W → Function.Injective (p.app W)) (W : X.Opens) :
    Function.Injective (pullU p W) := by
  intro a b hab
  apply unit_ext
  intro x hx
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVW⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hx W.2
  have hle : V ≤ W := hVW
  have e : res hle a = res hle b := by
    apply Units.ext
    apply hp V hV
    have := congrArg Units.val (show pullU p V (res hle a) = pullU p V (res hle b) by
      rw [pullU_res₂, pullU_res₂, hab])
    exact this
  rw [← gm_res (𝟙 X) x hle hxV a, ← gm_res (𝟙 X) x hle hxV b, e]

theorem unitsPatch : ∀ (X X' Z Z' : Scheme.{0}) (p : X' ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ X') (p' : Z' ⟶ Z),
    IsPullback i' p' p i → IsAffineHom p → IsClosedImmersion i → GlobalTheory.Pinch.Cond p i →
    GlobalTheory.Pinch.UnitsPatch p i i' p' := by
  intro X X' Z Z' p i i' p' h hp hi hc W
  have hinj : ∀ V : X.Opens, Function.Injective (pullU p V) :=
    pullU_injective p (fun V hV => (hc V hV).1)
  refine ⟨hinj W, fun u' v huv => ?_⟩
  have hw : ∀ z : Z', p (i' z) = i (p' z) := fun z => by
    have := congrArg (fun f : Z' ⟶ X => f z) h.w
    simpa using this
  let J : Type := {V : X.Opens // IsAffineOpen V ∧ V ≤ W}
  have hsub : ∀ j : J, p ⁻¹ᵁ j.1 ≤ p ⁻¹ᵁ W := fun j x hx => j.2.2 hx
  have hsubZ : ∀ j : J, i ⁻¹ᵁ j.1 ≤ i ⁻¹ᵁ W := fun j x hx => j.2.2 hx
  have loc : ∀ j : J, ∃ a : Γ(X, j.1)ˣ, pullU p j.1 a = res (hsub j) u' := by
    intro j
    refine affine_descent_units X X' Z Z' p i i' p' h hp hi hc j.1 j.2.1 _ (res (hsubZ j) v) ?_
    intro z hz
    rw [gm_res i' z (hsub j) hz, gm_res p' z (hsubZ j) (show i (p' z) ∈ j.1 from hw z ▸ hz)]
    exact huv z (j.2.2 hz)
  choose a ha using loc

  have hD : ∀ j : J, ∀ y : X', ∀ hy : p y ∈ j.1, gm p y j.1 (a j) = gm (𝟙 X') y (p ⁻¹ᵁ W) u' := by
    intro j y hy
    rw [← gm_id_pull p y j.1 hy, ha j, gm_res (𝟙 X') y (hsub j) hy]
  obtain ⟨s, hs⟩ := glue_unit W (fun j : J => j.1) (fun j => j.2.2) (by
      intro x hx
      obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVW⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hx W.2
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨V, hV, hVW⟩, hxV⟩) a (by
      intro j k x hx
      have hle1 : j.1 ⊓ k.1 ≤ j.1 := inf_le_left
      have hle2 : j.1 ⊓ k.1 ≤ k.1 := inf_le_right
      have e : res hle1 (a j) = res hle2 (a k) := by
        apply hinj
        apply unit_ext
        intro y hy
        rw [gm_id_pull p y _ hy, gm_id_pull p y _ hy, gm_res p y hle1 hy, gm_res p y hle2 hy,
          hD j y (hle1 hy), hD k y (hle2 hy)]
      rw [← gm_res (𝟙 X) x hle1 hx, ← gm_res (𝟙 X) x hle2 hx, e])
  refine ⟨s, unit_ext fun y hy => ?_⟩
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVW⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open (show p y ∈ W from hy) W.2
  let j : J := ⟨V, hV, hVW⟩
  rw [gm_id_pull p y W hy, ← gm_res p y j.2.2 hxV, hs j]
  exact hD j y hxV

end GlobalTheory.Pinch
end
end

