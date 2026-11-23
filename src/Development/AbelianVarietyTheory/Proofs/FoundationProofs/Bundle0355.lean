module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InertiaTorsionQuotientConjInvariantDecomposition
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0348
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ResPlaneSmulEqZero
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0343
public import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0349
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0347
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0346
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LocalCochainsGlueGlobal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0341

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.InertiaCocycleEqZeroOfVanishWildTameGenerator
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.KA GlobalTheory.InertCoh
open scoped Matrix

namespace GlobalTheory.CocWildTame

theorem eq_zero_on_Ine : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : R2 Ω l) (B : ValuationSubring Ω) (γ : G ℚ Ω), Formalism.BasicNotions.TameGenAt B γ → ∀ z : G ℚ Ω → Fin 2 → Qbar l, (∀ i, Continuous fun s => z s i) → (∀ s ∈ Ine (F := ℚ) B, ∀ t ∈ Ine (F := ℚ) B, z (s * t) = z s + mat W s *ᵥ z t) → (∀ σ : G ℚ Ω, (∀ y : Ω, y ≠ 0 → B.valuation (σ y / y - 1) < 1) → z σ = 0) → z γ = 0 → ∀ s ∈ Ine (F := ℚ) B, z s = 0 := by
  intro l _ Ω _ _ W B γ hγ z hz hcoc hw hγ0 s hs
  have hwild : ∀ σ : G ℚ Ω, (∀ y : Ω, y ≠ 0 → B.valuation (σ y / y - 1) < 1) → σ ∈ Ine (F := ℚ) B :=
    fun σ hσ => GlobalTheory.TameConjInv.wild_mem_Ine B hσ
  have h1 : z 1 = 0 := hw 1 (fun y hy => by simp [div_self hy])
  have key : ∀ h ∈ Subgroup.closure (insert γ {σ : G ℚ Ω | ∀ y : Ω, y ≠ 0 → B.valuation (σ y / y - 1) < 1}),
      h ∈ Ine (F := ℚ) B ∧ z h = 0 := by
    intro h hh
    induction hh using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | hx
      · exact ⟨hγ.1, hγ0⟩
      · exact ⟨hwild x hx, hw x hx⟩
    | one => exact ⟨one_mem _, h1⟩
    | mul x y _ _ ihx ihy =>
      obtain ⟨hx, hzx⟩ := ihx
      obtain ⟨hy, hzy⟩ := ihy
      exact ⟨mul_mem hx hy, by rw [hcoc x hx y hy, hzx, hzy, Matrix.mulVec_zero, add_zero]⟩
    | inv x _ ihx =>
      obtain ⟨hx, hzx⟩ := ihx
      refine ⟨inv_mem hx, ?_⟩
      have := hcoc x⁻¹ (inv_mem hx) x hx
      rw [inv_mul_cancel, h1, hzx, Matrix.mulVec_zero, add_zero] at this
      exact this.symm
  have hclosed : IsClosed {t : G ℚ Ω | z t = 0} := by
    have : {t : G ℚ Ω | z t = 0} = ⋂ i, (fun t => z t i) ⁻¹' {0} := by
      ext t; simp [funext_iff]
    rw [this]
    exact isClosed_iInter fun i => (isClosed_singleton).preimage (hz i)
  have hsub : ((Subgroup.closure (insert γ {σ : G ℚ Ω | ∀ y : Ω, y ≠ 0 → B.valuation (σ y / y - 1) < 1}) :
      Subgroup (G ℚ Ω)) : Set (G ℚ Ω)) ⊆ {t : G ℚ Ω | z t = 0} := fun h hh => (key h hh).2
  exact (closure_minimal hsub hclosed) (hγ.2 hs)

end GlobalTheory.CocWildTame
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralGaloisRepLocallyConstantModPrimePow
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

theorem GlobalTheory.Ord2.locConst_mod_pow :
    ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (c : Coef l) (W : R2 Ω l), Continuous W →
      (∀ s i j, mat W s i j ∈ c.O) → ∀ (n : ℕ) (s : G ℚ Ω), ∀ᶠ t in nhds s, ∀ i j,
        ∃ o ∈ c.O, mat W t i j - mat W s i j = (l : Qbar l) ^ n * o := by
  intro l _ Ω _ _ c W hW hO n s
  have hc : ∀ i j, Continuous fun t => mat W t i j := fun i j =>
    ((Units.continuous_val (M := Matrix (Fin 2) (Fin 2) (Qbar l))).comp hW).matrix_elem i j
  have hr : 0 < ‖((l : ℕ) : Qbar l) ^ n‖ := by
    rw [norm_pos_iff]
    exact pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  refine Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => ?_
  have hev : ∀ᶠ t in nhds s, mat W t i j ∈ Metric.closedBall (mat W s i j) ‖((l : ℕ) : Qbar l) ^ n‖ :=
    (hc i j).continuousAt.preimage_mem_nhds (Metric.closedBall_mem_nhds _ hr)
  filter_upwards [hev] with t ht
  rw [Metric.mem_closedBall, dist_eq_norm] at ht
  have hmem : mat W t i j - mat W s i j ∈ c.O := c.O.sub_mem (hO t i j) (hO s i j)
  obtain ⟨o, ho⟩ := (GlobalTheory.Coef.norm_le_norm_pow_iff_dvd l c n ⟨_, hmem⟩).1 ht
  refine ⟨(o : Qbar l), o.2, ?_⟩
  have := congrArg (fun x : c.O => (x : Qbar l)) ho
  simpa using this
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralTwoCocycleReciprocityTrivialAtLastPlaceStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralTwoCocycle_reciprocity_trivial_at_last_place : GlobalTheory.Mem.LiteralAutomorphy.LitCoh → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (c : Coef l) (n : ℕ) (S : Finset Pl) (ξ : G ℚ Ω → G ℚ Ω → Qbar l) (v₀ : Pl), l ≠ 2 → ContainsAbove S l → Coc2 c n S ξ → v₀ ∈ S → (∀ v ∈ S, v ≠ v₀ → ∃ B : ValuationSubring Ω, IsPlaceOver B v ∧ Cob2 c n (Dec (F := ℚ) B) ξ) → ∀ B : ValuationSubring Ω, IsPlaceOver B v₀ → Cob2 c n (Dec (F := ℚ) B) ξ := by
  first | exact @GlobalTheory.Ord2.Rec.reciprocity | exact GlobalTheory.Ord2.Rec.reciprocity | (intros; apply GlobalTheory.Ord2.Rec.reciprocity <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsCuspFunctionalValueModPrimePowDiamondIndepende
section
open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue
open scoped MatrixGroups

noncomputable section

namespace GlobalTheory.KZ

theorem mul_inv_mem_Gam_of_isDiam {N l d : ℕ} {s t : SL(2, ℤ)} (hs : IsDiam N l d s) (ht : IsDiam N l d t) :
    s * t⁻¹ ∈ Gam N l := by
  obtain ⟨hs0, hsd⟩ := hs
  obtain ⟨ht0, htd⟩ := ht
  rw [Subgroup.mem_inf] at hs0 ht0
  refine Subgroup.mem_inf.2 ⟨?_, Subgroup.mul_mem _ hs0.2 (Subgroup.inv_mem _ ht0.2)⟩
  have hsN := CongruenceSubgroup.Gamma0_mem.1 hs0.1
  have htN := CongruenceSubgroup.Gamma0_mem.1 ht0.1
  have ds := s.det_coe
  have dt := t.det_coe
  rw [Matrix.det_fin_two] at ds dt
  have ds' : ((s 0 0 * s 1 1 - s 0 1 * s 1 0 : ℤ) : ZMod N) = 1 := by rw [ds]; simp
  have dt' : ((t 0 0 * t 1 1 - t 0 1 * t 1 0 : ℤ) : ZMod N) = 1 := by rw [dt]; simp
  push_cast at ds' dt'
  simp only [en] at hsd htd
  rw [CongruenceSubgroup.Gamma1_mem]
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two,
    Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.head_fin_const]
  push_cast
  refine ⟨?_, ?_, ?_⟩
  · linear_combination ds' + (s 0 0 : ZMod N) * (htd - hsd) + (s 0 1 : ZMod N) * hsN - (s 0 1 : ZMod N) * htN
  · linear_combination dt' + (t 0 0 : ZMod N) * (hsd - htd) + (t 0 1 : ZMod N) * htN - (t 0 1 : ZMod N) * hsN
  · linear_combination (t 1 1 : ZMod N) * hsN - (s 1 1 : ZMod N) * htN

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

theorem Tower.act_eq_of_mem_B (X : Tower Ω ε) {N l w : ℕ} [Fact l.Prime] {b : X.Fn l} (hb : b ∈ X.B N l w)
    {γ : SL(2, ℤ)} (hγ : γ ∈ Gam N l) : X.act l (γ : Matrix (Fin 2) (Fin 2) ℤ) b = b := by
  induction hb using Submodule.span_induction with
  | mem x hx => exact hx.2 γ hγ
  | zero => exact map_zero _
  | add x y _ _ hx hy => rw [map_add (f := _), hx, hy]
  | smul c x _ hx => rw [map_smul, hx]

theorem Tower.act_isDiam_eq (X : Tower Ω ε) {N l w d : ℕ} [Fact l.Prime] {b : X.Fn l} (hb : b ∈ X.B N l w)
    {s : SL(2, ℤ)} (hs : IsDiam N l d s) :
    X.act l (s : Matrix (Fin 2) (Fin 2) ℤ) b = X.act l (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) b := by
  have ht : IsDiam N l d (sgD N l d) := Classical.epsilon_spec ⟨s, hs⟩
  have hγ := mul_inv_mem_Gam_of_isDiam hs ht
  have e : s = (s * (sgD N l d)⁻¹) * sgD N l d := by group
  have hpos : ∀ g : SL(2, ℤ), 0 < (g : Matrix (Fin 2) (Fin 2) ℤ).det := fun g => by rw [g.det_coe]; exact one_pos
  rw [e, Matrix.SpecialLinearGroup.coe_mul, ← Tower.act_act Ω ε X l _ _ (hpos _) (hpos _) b,
    X.act_eq_of_mem_B hb hγ]

theorem isThB_act_isDiam_iff : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε)
    (A : ValuationSubring Ω) (N l : ℕ) [Fact l.Prime] (n w d : ℕ) (b : X.Fn l), b ∈ X.B N l w →
    ∀ s : SL(2, ℤ), IsDiam N l d s → ∀ φ : HahnSeries ℚ Ω,
  IsThB X A N l n (X.act l (s : Matrix (Fin 2) (Fin 2) ℤ) b) φ ↔
    IsThB X A N l n (X.act l (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) b) φ := by
  intro Ω _ _ _ ε X A N l _ n w d b hb s hs φ
  rw [X.act_isDiam_eq hb hs]

end GlobalTheory.KZ
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerScalarLayerLinkOfShapiroSpecializationApprStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.KA
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kummerScalarLayerLink_of_shapiroSpecialization_approx : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (A : ValuationSubring Ω) (e : ℕ) (χ : ∀ r : ℕ, (ZMod (l ^ r))ˣ → Qbar l) (Y : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Fin 2 → Qbar l) (y : G ℚ Ω → Fin 2 → Qbar l), (∀ r, ∀ s ∈ Ine (F := ℚ) A, cycBar ℚ Ω l s = 1 → ‖y s 1 - spec (fun x : (ZMod (l ^ r))ˣ => ((((x : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * χ r x) (Y r) s 1‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖) → SpLink A e χ (fun r s x => Y r s x 1) y := by
  first | exact @GlobalTheory.KZ.spLink_of_spec_approx | exact GlobalTheory.KZ.spLink_of_spec_approx | (intros; apply GlobalTheory.KZ.spLink_of_spec_approx <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LimitOfApproximateCocycles
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2

theorem qbarLVectorCongruent_integralMatrix_mulVec {l : ℕ} [Fact l.Prime] (c : Coef l) (M : Matrix (Fin 2) (Fin 2) (Qbar l))
    (hM : ∀ i j, M i j ∈ c.O) {n : ℕ} {v w : Fin 2 → Qbar l} (h : Cv n v w) :
    Cv n (M *ᵥ v) (M *ᵥ w) := by
  intro i
  unfold Cg
  have e : (M *ᵥ v) i - (M *ᵥ w) i = M i 0 * (v 0 - w 0) + M i 1 * (v 1 - w 1) := by
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]; ring
  rw [e]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (norm_le_one_of_mem_coef c (hM i 0))).trans (h 0)
  · rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (norm_le_one_of_mem_coef c (hM i 1))).trans (h 1)

theorem limit_cocycle_mem_cocycles : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : R2 Ω l) (c : Coef l), (∀ s i j, mat W s i j ∈ c.O) → ∀ (a : ℕ → G ℚ Ω → Fin 2 → Qbar l) (z : G ℚ Ω → Fin 2 → Qbar l), (∀ n s t, Cv n (a n (s * t)) (a n s + mat W s *ᵥ a n t)) → (∀ n s, ∀ᶠ t in nhds s, Cv n (a n t) (a n s)) → (∀ n s, Cv n (z s) (a n s)) → z ∈ Z1 (Loc.colRep W) := by
  intro l _ Ω _ _ W c hW a z hco hloc hz
  rw [mem_Z1_iff_cocycle]
  refine ⟨?_, ?_⟩
  · refine continuous_pi fun i => ?_
    refine continuous_iff_continuousAt.2 fun s => ?_
    have key : Filter.Tendsto (fun t => z t i) (nhds s) (@nhds (Qbar l) UniformSpace.toTopologicalSpace (z s i)) := by
      rw [Metric.tendsto_nhds]
      intro ε hε
      obtain ⟨n, hn⟩ := (tendsto_norm_l_pow (l := l)).eventually (gt_mem_nhds hε) |>.exists
      filter_upwards [hloc n s] with t ht
      have h1 : Cg n (z t i) (z s i) :=
        cg_trans (hz n t i) (cg_trans (ht i) (cg_symm (hz n s i)))
      rw [dist_eq_norm]
      exact lt_of_le_of_lt h1 hn
    exact key
  · intro s t
    have hcol : ∀ v, (Loc.colRep W s) v = mat W s *ᵥ v := by
      intro v; simp [Loc.colRep, Matrix.toLin'_apply]
    rw [hcol]
    funext i
    refine eq_of_forall_cg fun n => ?_
    have hA : Cv n (z (s * t)) (a n (s * t)) := hz n (s * t)
    have hB := hco n s t
    have hC : Cv n (a n s + mat W s *ᵥ a n t) (z s + mat W s *ᵥ z t) := by
      intro j
      have h2 := qbarLVectorCongruent_integralMatrix_mulVec c (mat W s) (hW s) (cv_symm (hz n t)) j
      have h3 := cg_symm (hz n s j)
      unfold Cg at h2 h3 ⊢
      have e : (a n s + mat W s *ᵥ a n t) j - (z s + mat W s *ᵥ z t) j
          = (a n s j - z s j) + ((mat W s *ᵥ a n t) j - (mat W s *ᵥ z t) j) := by
        simp only [Pi.add_apply]; ring
      rw [e]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h3 h2)
    exact (cv_trans hA (cv_trans hB hC)) i

end GlobalTheory.Ord2
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LocalCochainsGlueGlobalStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_cochains_glue_global : GlobalTheory.Mem.LiteralAutomorphy.LitCoh → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (c : Coef l) (n : ℕ) (S : Finset Pl) (ξ : G ℚ Ω → G ℚ Ω → Qbar l), l ≠ 2 → ContainsAbove S l → Coc2 c n S ξ → (∀ v ∈ S, ∃ B : ValuationSubring Ω, IsPlaceOver B v ∧ Cob2 c n (Dec (F := ℚ) B) ξ) → ∃ u : G ℚ Ω → Qbar l, Continuous u ∧ (∀ s, u s ∈ c.O) ∧ (∀ s, ∀ a ∈ (toGS Ω (S : Set Pl)).ker, Cg n (u (s * a)) (u s)) ∧ ∀ s t, Cg n (ξ s t) (eps l s * u t - u (s * t) + u s) := by
  first | exact @GlobalTheory.Ord2.TwistTriv.coboundary_of_locTriv | exact GlobalTheory.Ord2.TwistTriv.coboundary_of_locTriv | (intros; apply GlobalTheory.Ord2.TwistTriv.coboundary_of_locTriv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemCoefRingInvertPrimeInvOfMemNeZero
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

noncomputable section

namespace GlobalTheory.Ord2

theorem memE_inv_of_mem : ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (d : Qbar l), d ∈ c.O → d ≠ 0 → MemE c d⁻¹ := by
  intro l _ c d hd hd0
  set x : c.O := ⟨d, hd⟩ with hxdef
  have hx0 : x ≠ 0 := fun h => hd0 (congrArg Subtype.val h)
  set L : c.O := ((l : ℕ) : c.O) with hLdef
  have hLval : (L : Qbar l) = ((l : ℕ) : Qbar l) := by simp [hLdef]
  have hL0 : L ≠ 0 := by
    intro h
    have : ((l : ℕ) : Qbar l) = 0 := by rw [← hLval, h]; rfl
    have h1 := (norm_natCast_l (l := l))
    rw [this, norm_zero] at h1
    have : (0:ℝ) < (l:ℝ)⁻¹ := inv_pos.2 (by exact_mod_cast (Fact.out : l.Prime).pos)
    linarith
  have hLnu : ¬ IsUnit L := by
    rintro ⟨u, hu⟩
    have h1 : ((u : c.O) : Qbar l) * ((u⁻¹ : c.Oˣ) : c.O) = 1 := by
      rw [← Subalgebra.coe_mul, Units.mul_inv]; rfl
    have hn2 : ‖(((u⁻¹ : c.Oˣ) : c.O) : Qbar l)‖ ≤ 1 := norm_le_one_of_mem_coef c (SetLike.coe_mem _)
    have hu' : ((u : c.O) : Qbar l) = ((l : ℕ) : Qbar l) := by rw [hu, hLval]
    rw [hu'] at h1
    have h2 := congrArg norm h1
    rw [norm_mul, norm_one] at h2
    have h3 := norm_natCast_l_lt_one (l := l)
    have h4 : ‖((l : ℕ) : Qbar l)‖ * ‖(((u⁻¹ : c.Oˣ) : c.O) : Qbar l)‖ < 1 :=
      lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) hn2) h3
    linarith
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible c.O
  obtain ⟨v, u, hxu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0 hϖ
  obtain ⟨m, u', hLu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hL0 hϖ
  have hm : m ≠ 0 := by
    rintro rfl
    apply hLnu
    rw [hLu, pow_zero, mul_one]; exact u'.isUnit
  have hϖL : ϖ ∣ L := by
    rw [hLu]
    exact Dvd.dvd.mul_left (dvd_pow_self ϖ hm) _
  have hdiv : x ∣ L ^ v := by
    rw [hxu]
    exact (Units.mul_left_dvd).2 (pow_dvd_pow_of_dvd hϖL v)
  obtain ⟨q, hq⟩ := hdiv
  refine ⟨v, ?_⟩
  have hq' : ((l : ℕ) : Qbar l) ^ v = d * (q : Qbar l) := by
    have := congrArg (fun y : c.O => (y : Qbar l)) hq
    simpa [hLval, hxdef] using this
  rw [hq', mul_comm d, mul_assoc, mul_inv_cancel₀ hd0, mul_one]
  exact q.2

end GlobalTheory.Ord2

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NotCongruentZeroIntCastMulPrimePowStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.not_congruent_zero_intCast_mul_prime_pow : ∀ (l : ℕ) [Fact l.Prime] (t k : ℕ) (d : ℤ), d ≠ 0 → |d| < (l : ℤ) ^ t → ¬ Cg (t + k) ((d : Qbar l) * ((l : ℕ) : Qbar l) ^ k) 0 := by
  first | exact @GlobalTheory.Ord2.IntNorm.not_cg_int_mul_pow | exact GlobalTheory.Ord2.IntNorm.not_cg_int_mul_pow | (intros; apply GlobalTheory.Ord2.IntNorm.not_cg_int_mul_pow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.OpenSubgroupCochainInvariance
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
open Filter Topology

noncomputable section

namespace GlobalTheory.Ord2.OpenInv

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]

theorem cg_trans {n : ℕ} {a b c : Qbar l} (h1 : Cg n a b) (h2 : Cg n b c) : Cg n a c := by
  unfold Cg at *
  calc ‖a - c‖ = ‖(a - b) + (b - c)‖ := by rw [sub_add_sub_cancel]
    _ ≤ max ‖a - b‖ ‖b - c‖ := IsUltrametricDist.norm_add_le_max _ _
    _ ≤ _ := max_le h1 h2

theorem cg_symm {n : ℕ} {a b : Qbar l} (h1 : Cg n a b) : Cg n b a := by
  unfold Cg at *
  rwa [norm_sub_rev]

theorem cg_refl {n : ℕ} (a : Qbar l) : Cg n a a := by
  unfold Cg
  rw [sub_self, norm_zero]
  exact norm_nonneg _

private theorem eps_eq_algebraMap_cycZ (s : G ℚ Ω) :
    eps l s = algebraMap ℚ_[l] (Qbar l) ((ReciprocityTheory.Gal.cycZ ℚ Ω l s : ℤ_[l]) : ℚ_[l]) := by
  unfold eps cycBar
  rfl

theorem norm_eps_le (s : G ℚ Ω) : ‖eps l s‖ ≤ 1 := by
  rw [eps_eq_algebraMap_cycZ]
  unfold Qbar
  rw [PadicAlgCl.norm_extends]
  exact (ReciprocityTheory.Gal.cycZ ℚ Ω l s : ℤ_[l]).2

theorem cg_mul_eps {n : ℕ} (s : G ℚ Ω) {a b : Qbar l} (h : Cg n a b) : Cg n (eps l s * a) (eps l s * b) := by
  unfold Cg at *
  rw [← mul_sub, norm_mul]
  calc ‖eps l s‖ * ‖a - b‖ ≤ 1 * ‖a - b‖ := mul_le_mul_of_nonneg_right (norm_eps_le s) (norm_nonneg _)
    _ ≤ _ := by rw [one_mul]; exact h

theorem eps_mul (s t : G ℚ Ω) : eps l (s * t) = eps l s * eps l t := by
  unfold eps
  rw [map_mul, Units.val_mul]

theorem eps_one : eps l (1 : G ℚ Ω) = 1 := by
  unfold eps
  rw [map_one, Units.val_one]

theorem pow_pos' (n : ℕ) : 0 < ‖((l : ℕ) : Qbar l) ^ n‖ :=
  norm_pos_iff.mpr (pow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero))

private theorem continuous_eps' : Continuous (fun s : G ℚ Ω => eps l s) := by
  have h : (fun s : G ℚ Ω => eps l s) =
      fun s => algebraMap ℚ_[l] (Qbar l) ((ReciprocityTheory.Gal.cycZ ℚ Ω l s : ℤ_[l]) : ℚ_[l]) := by
    funext s
    exact eps_eq_algebraMap_cycZ s
  rw [h]
  have h1 : Continuous fun s : G ℚ Ω => ((ReciprocityTheory.Gal.cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l]) :=
    Units.continuous_val.comp (ReciprocityTheory.Gal.continuous_cycZ ℚ Ω l)
  have h2 : Continuous fun z : ℤ_[l] => (z : ℚ_[l]) := continuous_subtype_val
  exact (continuous_algebraMap ℚ_[l] (Qbar l)).comp (h2.comp h1)

theorem ev_cg {X : Type} [TopologicalSpace X] {n : ℕ} {f g : X → Qbar l} (hf : Continuous f) (hg : Continuous g)
    {x : X} (h : f x = g x) : ∀ᶠ y in 𝓝 x, Cg n (f y) (g y) := by
  have hc : Continuous fun y => ‖f y - g y‖ := (hf.sub hg).norm
  have h0 : ‖f x - g x‖ < ‖((l : ℕ) : Qbar l) ^ n‖ := by
    rw [h, sub_self, norm_zero]
    exact pow_pos' n
  filter_upwards [hc.continuousAt.eventually_lt continuousAt_const h0] with y hy
  unfold Cg
  exact hy.le

def invSub (n : ℕ) (H : Subgroup (G ℚ Ω)) (ξ : G ℚ Ω → G ℚ Ω → Qbar l) : Subgroup (G ℚ Ω) where
  carrier := {k | k ∈ H ∧ Cg n (eps l k) 1 ∧ ∀ s ∈ H, ∀ t ∈ H, Cg n (ξ (s * k) t) (ξ s t) ∧ Cg n (ξ s (t * k)) (ξ s t)}
  one_mem' := ⟨H.one_mem, by rw [eps_one]; exact cg_refl _, fun s _ t _ => by
    rw [mul_one, mul_one]; exact ⟨cg_refl _, cg_refl _⟩⟩
  mul_mem' := by
    rintro a b ⟨ha, ha1, ha2⟩ ⟨hb, hb1, hb2⟩
    refine ⟨H.mul_mem ha hb, ?_, fun s hs t ht => ⟨?_, ?_⟩⟩
    · rw [eps_mul]
      have := cg_mul_eps a hb1
      rw [mul_one] at this
      exact cg_trans this ha1
    · rw [← mul_assoc]
      exact cg_trans (hb2 _ (H.mul_mem hs ha) t ht).1 (ha2 s hs t ht).1
    · rw [← mul_assoc]
      exact cg_trans (hb2 s hs _ (H.mul_mem ht ha)).2 (ha2 s hs t ht).2
  inv_mem' := by
    rintro a ⟨ha, ha1, ha2⟩
    refine ⟨H.inv_mem ha, ?_, fun s hs t ht => ⟨?_, ?_⟩⟩
    · have := cg_mul_eps a⁻¹ ha1
      rw [mul_one, ← eps_mul, inv_mul_cancel, eps_one] at this
      exact cg_symm this
    · have := (ha2 _ (H.mul_mem hs (H.inv_mem ha)) t ht).1
      rw [inv_mul_cancel_right] at this
      exact cg_symm this
    · have := (ha2 s hs _ (H.mul_mem ht (H.inv_mem ha))).2
      rw [inv_mul_cancel_right] at this
      exact cg_symm this

theorem open_inv : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (n : ℕ) (H I : Subgroup (G ℚ Ω)) (ξ : G ℚ Ω → G ℚ Ω → Qbar l), IsClosed (H : Set (G ℚ Ω)) → I ≤ H → ContinuousOn (fun p : G ℚ Ω × G ℚ Ω => ξ p.1 p.2) ((H : Set (G ℚ Ω)) ×ˢ (H : Set (G ℚ Ω))) → (∀ i ∈ I, eps l i = 1) → (∀ s ∈ H, ∀ t ∈ H, ∀ i ∈ I, Cg n (ξ (s * i) t) (ξ s t) ∧ Cg n (ξ s (t * i)) (ξ s t)) → ∃ K : Subgroup (G ℚ Ω), I ≤ K ∧ K ≤ H ∧ IsOpen ((K.subgroupOf H : Subgroup ↥H) : Set ↥H) ∧ (∀ k ∈ K, Cg n (eps l k) 1) ∧ ∀ s ∈ H, ∀ t ∈ H, ∀ k ∈ K, Cg n (ξ (s * k) t) (ξ s t) ∧ Cg n (ξ s (t * k)) (ξ s t) := by
  intro l _ Ω _ _ _ n H I ξ hH hIH hξ hI hinv
  have : CompactSpace H := isCompact_iff_compactSpace.mp hH.isCompact
  have hξc : Continuous fun p : H × H => ξ p.1 p.2 := by
    have hp : Continuous fun p : H × H => ((p.1 : G ℚ Ω), (p.2 : G ℚ Ω)) :=
      (continuous_subtype_val.comp continuous_fst).prodMk (continuous_subtype_val.comp continuous_snd)
    exact hξ.comp_continuous hp (fun p => ⟨p.1.2, p.2.2⟩)
  have hL : ∀ᶠ k in 𝓝 (1 : H), ∀ y ∈ (Set.univ : Set (H × H)),
      Cg n (ξ ((y.1 * k : H) : G ℚ Ω) y.2) (ξ y.1 y.2) := by
    refine isCompact_univ.eventually_forall_of_forall_eventually fun y _ => ?_
    exact ev_cg (X := H × (H × H)) (n := n)
      (f := fun z => ξ ((z.2.1 * z.1 : H) : G ℚ Ω) z.2.2) (g := fun z => ξ z.2.1 z.2.2)
      (hξc.comp ((continuous_snd.fst.mul continuous_fst).prodMk continuous_snd.snd))
      (hξc.comp (continuous_snd.fst.prodMk continuous_snd.snd))
      (x := ((1 : H), y)) (by simp)
  have hR : ∀ᶠ k in 𝓝 (1 : H), ∀ y ∈ (Set.univ : Set (H × H)),
      Cg n (ξ y.1 ((y.2 * k : H) : G ℚ Ω)) (ξ y.1 y.2) := by
    refine isCompact_univ.eventually_forall_of_forall_eventually fun y _ => ?_
    exact ev_cg (X := H × (H × H)) (n := n)
      (f := fun z => ξ z.2.1 ((z.2.2 * z.1 : H) : G ℚ Ω)) (g := fun z => ξ z.2.1 z.2.2)
      (hξc.comp (continuous_snd.fst.prodMk (continuous_snd.snd.mul continuous_fst)))
      (hξc.comp (continuous_snd.fst.prodMk continuous_snd.snd))
      (x := ((1 : H), y)) (by simp)
  have hE : ∀ᶠ k : H in 𝓝 (1 : H), Cg n (eps l (k : G ℚ Ω)) 1 := by
    refine ev_cg (X := H) (n := n) (f := fun k => eps l (k : G ℚ Ω)) (g := fun _ => 1)
      (continuous_eps'.comp continuous_subtype_val) continuous_const ?_
    show eps l ((1 : H) : G ℚ Ω) = 1
    rw [OneMemClass.coe_one, eps_one]
  refine ⟨invSub n H ξ, ?_, fun k hk => hk.1, ?_, fun k hk => hk.2.1, fun s hs t ht k hk => hk.2.2 s hs t ht⟩
  · intro i hi
    have hiH : i ∈ H := hIH hi
    show i ∈ H ∧ Cg n (eps l i) 1 ∧ ∀ s ∈ H, ∀ t ∈ H, Cg n (ξ (s * i) t) (ξ s t) ∧ Cg n (ξ s (t * i)) (ξ s t)
    refine ⟨hiH, ?_, fun s hs t ht => hinv s hs t ht i hi⟩
    rw [hI i hi]
    exact cg_refl _
  · apply Subgroup.isOpen_of_mem_nhds (g := 1)
    filter_upwards [hL, hR, hE] with k hkL hkR hkE
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
    show (k : G ℚ Ω) ∈ H ∧ Cg n (eps l (k : G ℚ Ω)) 1 ∧ ∀ s ∈ H, ∀ t ∈ H,
      Cg n (ξ (s * k) t) (ξ s t) ∧ Cg n (ξ s (t * k)) (ξ s t)
    exact ⟨k.2, hkE, fun s hs t ht => ⟨hkL (⟨s, hs⟩, ⟨t, ht⟩) trivial, hkR (⟨s, hs⟩, ⟨t, ht⟩) trivial⟩⟩

end GlobalTheory.Ord2.OpenInv

end
end

