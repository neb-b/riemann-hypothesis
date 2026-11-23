module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0189
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0264
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0193
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0010
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.H2EquivOfTorsionCharacter
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffZeroEqZeroIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0249
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SmallTracesDvdSpanImage
section
open Formalism.MainNotions.N GlobalTheory.Cong GlobalTheory.PsChar

namespace GlobalTheory.SmallTrace

theorem exists_ball_sub_image {l : ℕ} [Fact l.Prime] {ι F : Type} [Fintype ι]
    [NormedAddCommGroup F] [NormedSpace ℚ_[l] F] (S : (ι → ℚ_[l]) →ₗ[ℚ_[l]] F) :
    ∃ ε > 0, ∀ w ∈ LinearMap.range S, ‖w‖ < ε → ∃ x : ι → ℚ_[l], ‖x‖ < 1 ∧ S x = w := by
  have hS' : Function.Surjective S.rangeRestrict := LinearMap.surjective_rangeRestrict S
  have ho : IsOpenMap S.rangeRestrict := LinearMap.isOpenMap_of_finiteDimensional _ hS'
  have hU : IsOpen (S.rangeRestrict '' Metric.ball 0 1) := ho _ Metric.isOpen_ball
  have h0 : (0 : LinearMap.range S) ∈ S.rangeRestrict '' Metric.ball 0 1 := ⟨0, by simp, by simp⟩
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU 0 h0
  refine ⟨ε, hε, fun w hw hwε => ?_⟩
  have hmem : (⟨w, hw⟩ : LinearMap.range S) ∈ Metric.ball 0 ε := by
    rw [Metric.mem_ball, dist_zero_right]; exact hwε
  obtain ⟨x, hx, hxw⟩ := hball hmem
  refine ⟨x, by simpa using hx, ?_⟩
  have := congrArg Subtype.val hxw
  simpa using this

variable {l : ℕ} [Fact l.Prime] {Γ : Type} [Group Γ] {a : ℕ}

noncomputable def matOf (r : Γ →* GL (Fin a) (PadicAlgCl l)) (f : Γ →₀ ℤ_[l]) :
    Matrix (Fin a) (Fin a) (PadicAlgCl l) :=
  f.sum fun h c => ((algebraMap ℚ_[l] (PadicAlgCl l)) (c : ℚ_[l])) •
    ((r h : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l))

theorem matOf_eq_lc (r : Γ →* GL (Fin a) (PadicAlgCl l)) (t : Finset Γ) (f : Γ →₀ ℤ_[l])
    (hf : f.support ⊆ t) :
    matOf r f = Fintype.linearCombination ℚ_[l]
      (fun i : t => ((r i : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l)))
      (fun i => (f i : ℚ_[l])) := by
  rw [Fintype.linearCombination_apply, matOf, Finsupp.sum_of_support_subset f hf _ (by simp)]
  rw [← Finset.sum_coe_sort t]
  simp [algebraMap_smul]

theorem exists_matOf_eq (r : Γ →* GL (Fin a) (PadicAlgCl l)) (t : Finset Γ) (y : t → ℤ_[l]) :
    ∃ f' : Γ →₀ ℤ_[l], matOf r f' = Fintype.linearCombination ℚ_[l]
      (fun i : t => ((r i : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l)))
      (fun i => (y i : ℚ_[l])) := by
  classical
  let f' : Γ →₀ ℤ_[l] := Finsupp.onFinset t (fun g => if h : g ∈ t then y ⟨g, h⟩ else 0)
    (by intro g hg; by_contra h; simp [h] at hg)
  refine ⟨f', ?_⟩
  rw [matOf_eq_lc r t f' (Finsupp.support_onFinset_subset)]
  congr 1
  funext i
  simp [f', Finsupp.onFinset_apply, i.2]

end GlobalTheory.SmallTrace

namespace GlobalTheory.SmallTrace
variable {l : ℕ} [Fact l.Prime] {Γ : Type} [Group Γ] {a : ℕ}

theorem matOf_single (r : Γ →* GL (Fin a) (PadicAlgCl l)) (g : Γ) :
    matOf r (Finsupp.single g 1) =
      ((r g : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l)) := by
  rw [matOf, Finsupp.sum_single_index (by simp)]
  simp

theorem matOf_mem_span (r : Γ →* GL (Fin a) (PadicAlgCl l)) (f : Γ →₀ ℤ_[l]) :
    matOf r f ∈ Submodule.span (PadicAlgCl l) (Set.range fun g =>
      ((r g : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l))) := by
  rw [matOf]
  exact Submodule.sum_mem _ fun h _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨h, rfl⟩)

theorem trace_zero_of_finset (r : Γ →* GL (Fin a) (PadicAlgCl l)) (t : Finset Γ)
    (ht : ∀ f : Γ →₀ ℤ_[l], ∃ f' : Γ →₀ ℤ_[l], f'.support ⊆ t ∧ matOf r f = matOf r f')
    (D : Matrix (Fin a) (Fin a) (PadicAlgCl l))
    (hD : ∀ i : t, (D * ((r i : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l))).trace = 0)
    (g : Γ) : (D * ((r g : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l))).trace = 0 := by
  obtain ⟨f', hf't, hf'⟩ := ht (Finsupp.single g 1)
  rw [matOf_single, matOf_eq_lc r t f' hf't, Fintype.linearCombination_apply] at hf'
  rw [hf', Matrix.mul_sum, Matrix.trace_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [Matrix.mul_smul, Matrix.trace_smul, hD i, smul_zero]

end GlobalTheory.SmallTrace

namespace GlobalTheory.SmallTrace
variable {l : ℕ} [Fact l.Prime] {Γ : Type} [Group Γ] {a : ℕ}

theorem finiteRing_sq_sub_mul_sq_eq_of_card [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
    (r : Γ →* GL (Fin a) (PadicAlgCl l)) (hr : Continuous r) (hss : IsSSRep r) :
    ∃ c : ℕ, ∀ (n : ℕ) (f : Γ →₀ ℤ_[l]),
      (∀ g, ‖(matOf r f * ((r g : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l))).trace‖
        ≤ ((l : ℝ)⁻¹) ^ (n + c)) →
      ∃ f' : Γ →₀ ℤ_[l], matOf r f = ((l : PadicAlgCl l) ^ n) • matOf r f' := by
  obtain ⟨t, ht⟩ := _root_.GlobalTheory.zl_span_image_finite l Γ a r hr
  have ht' : ∀ f : Γ →₀ ℤ_[l], ∃ f' : Γ →₀ ℤ_[l], f'.support ⊆ t ∧ matOf r f = matOf r f' := ht
  let v : t → Matrix (Fin a) (Fin a) (PadicAlgCl l) := fun i =>
    ((r i : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l))
  let Φ : Matrix (Fin a) (Fin a) (PadicAlgCl l) →ₗ[ℚ_[l]] (t → PadicAlgCl l) :=
    { toFun := fun M i => (M * v i).trace
      map_add' := by intro M N; funext i; simp [Matrix.add_mul, Matrix.trace_add]
      map_smul' := by intro c M; funext i; simp [Matrix.smul_mul, Matrix.trace_smul] }
  let S : (t → ℚ_[l]) →ₗ[ℚ_[l]] (t → PadicAlgCl l) := Φ ∘ₗ Fintype.linearCombination ℚ_[l] v
  obtain ⟨ε, hε, hball⟩ := exists_ball_sub_image S
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hl0 : (0 : ℝ) < l := by linarith
  obtain ⟨c, hc⟩ : ∃ c : ℕ, ((l : ℝ)⁻¹) ^ c < ε :=
    exists_pow_lt_of_lt_one hε (inv_lt_one_of_one_lt₀ hl1)
  refine ⟨c, fun n f hf => ?_⟩
  obtain ⟨f0, hf0t, hf0⟩ := ht' f
  set x0 : t → ℚ_[l] := fun i => (f0 i : ℚ_[l]) with hx0
  have hMf : matOf r f = Fintype.linearCombination ℚ_[l] v x0 := by
    rw [hf0]; exact matOf_eq_lc r t f0 hf0t
  have hΦf : ‖Φ (matOf r f)‖ ≤ ((l : ℝ)⁻¹) ^ (n + c) :=
    (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => hf i
  set q : ℚ_[l] := ((l : ℚ_[l]) ^ n)⁻¹ with hq
  have hlQ : (l : ℚ_[l]) ^ n ≠ 0 := pow_ne_zero _ (by exact_mod_cast (Fact.out : l.Prime).ne_zero)
  have hqn : ‖q‖ = (l : ℝ) ^ n := by
    rw [hq, norm_inv, norm_pow, Padic.norm_p, inv_pow, inv_inv]
  set w : t → PadicAlgCl l := q • Φ (matOf r f) with hw
  have hwS : w = S (q • x0) := by
    rw [hw, map_smul, hMf]; rfl
  have hwε : ‖w‖ < ε := by
    rw [hw, norm_smul, hqn]
    calc (l : ℝ) ^ n * ‖Φ (matOf r f)‖ ≤ (l : ℝ) ^ n * ((l : ℝ)⁻¹) ^ (n + c) :=
          mul_le_mul_of_nonneg_left hΦf (by positivity)
      _ = ((l : ℝ)⁻¹) ^ c := by
          rw [pow_add, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hl0.ne', one_pow, one_mul]
      _ < ε := hc
  obtain ⟨y, hy1, hy⟩ := hball w ⟨_, hwS.symm⟩ hwε
  have hyi : ∀ i, ‖y i‖ ≤ 1 := fun i => (norm_le_pi_norm y i).trans hy1.le
  let yz : t → ℤ_[l] := fun i => ⟨y i, hyi i⟩
  obtain ⟨f', hf'⟩ := exists_matOf_eq r t yz
  refine ⟨f', ?_⟩
  have hlK : ((l : PadicAlgCl l) ^ n) = algebraMap ℚ_[l] (PadicAlgCl l) ((l : ℚ_[l]) ^ n) := by simp
  rw [← sub_eq_zero]
  apply _root_.GlobalTheory.TrFormNd.eq_zero_of_trace_mul_eq_zero (PadicAlgCl l) Γ a r hss
  · exact Submodule.sub_mem _ (matOf_mem_span r f)
      (Submodule.smul_mem _ _ (matOf_mem_span r f'))
  · apply trace_zero_of_finset r t ht'
    intro i
    have hy' : Fintype.linearCombination ℚ_[l] v (fun i => (yz i : ℚ_[l])) = Fintype.linearCombination ℚ_[l] v y := rfl
    have key : Φ (matOf r f - ((l : PadicAlgCl l) ^ n) • matOf r f') = 0 := by
      rw [hf', hy', hlK, algebraMap_smul, map_sub, map_smul]
      have : Φ (Fintype.linearCombination ℚ_[l] v y) = w := hy
      rw [this, hw, smul_smul, hq, mul_inv_cancel₀ hlQ, one_smul, sub_self]
    exact congrFun key i

end GlobalTheory.SmallTrace

theorem GlobalTheory.smallTrace_dvd_span : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] (a : ℕ) (r : Γ →* GL (Fin a) (PadicAlgCl l)), Continuous r → IsSSRep r → ∃ c : ℕ, ∀ (n : ℕ) (f : Γ →₀ ℤ_[l]), (∀ g, ‖((f.sum fun h c => ((algebraMap ℚ_[l] (PadicAlgCl l)) (c : ℚ_[l])) • ((r h : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l))) * ((r g : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l))).trace‖ ≤ ((l : ℝ)⁻¹) ^ (n + c)) → ∃ f' : Γ →₀ ℤ_[l], (f.sum fun h c => ((algebraMap ℚ_[l] (PadicAlgCl l)) (c : ℚ_[l])) • ((r h : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l))) = ((l : PadicAlgCl l) ^ n) • (f'.sum fun h c => ((algebraMap ℚ_[l] (PadicAlgCl l)) (c : ℚ_[l])) • ((r h : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l))) := by
  intro l _ Γ _ _ _ _ a r hr hss
  exact GlobalTheory.SmallTrace.finiteRing_sq_sub_mul_sq_eq_of_card r hr hss
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameGeneratorImageEqCoprimePow
section
open GlobalTheory.TypeLeaf Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

namespace GlobalTheory.TypeLeaf

theorem tameGen_image_mem_zpowers {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    (A : ValuationSubring Ω) (γ γ' : G E Ω) (h : TameGenAt A γ) (h' : TameGenAt A γ')
    {M : Type} [Group M] (φ : G E Ω →* M) (hk : IsOpen (φ.ker : Set (G E Ω)))
    (hw : ∀ s : G E Ω, (∀ y : Ω, y ≠ 0 → A.valuation (s y / y - 1) < 1) → φ s = 1) :
    φ γ' ∈ Subgroup.zpowers (φ γ) := by
  have hle : φ.ker ≤ (Subgroup.zpowers (φ γ)).comap φ := by
    intro x hx
    rw [Subgroup.mem_comap, MonoidHom.mem_ker.1 hx]
    exact Subgroup.one_mem _
  have hop : IsOpen (((Subgroup.zpowers (φ γ)).comap φ : Subgroup (G E Ω)) : Set (G E Ω)) :=
    Subgroup.isOpen_mono hle hk
  have hcl := Subgroup.isClosed_of_isOpen _ hop
  have hsub : Subgroup.closure (insert γ {σ : G E Ω | ∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1})
      ≤ (Subgroup.zpowers (φ γ)).comap φ := by
    rw [Subgroup.closure_le]
    rintro x (rfl | hx)
    · exact Subgroup.mem_zpowers _
    · exact hle (hw x hx)
  exact closure_minimal hsub hcl (h.2 h'.1)

theorem tameGen_pow : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (γ γ' : G E Ω), TameGenAt A γ → TameGenAt A γ' → ∀ (M : Type) [Group M] (φ : G E Ω →* M), IsOpen (φ.ker : Set (G E Ω)) → (∀ s : G E Ω, (∀ y : Ω, y ≠ 0 → A.valuation (s y / y - 1) < 1) → φ s = 1) → ∃ n : ℕ, n.Coprime (orderOf (φ γ)) ∧ 0 < orderOf (φ γ) ∧ φ γ' = φ γ ^ n := by
  intro E Ω _ _ _ _ _ A γ γ' h h' M _ φ hk hw
  have h1 := tameGen_image_mem_zpowers A γ γ' h h' φ hk hw
  have h2 := tameGen_image_mem_zpowers A γ' γ h' h φ hk hw
  haveI : IsGalois E Ω := IsGalois.mk
  haveI : Finite (G E Ω ⧸ φ.ker) := Subgroup.quotient_finite_of_isOpen _ hk
  have hfin : IsOfFinOrder (φ γ) := by
    have h0 : IsOfFinOrder (QuotientGroup.mk γ : G E Ω ⧸ φ.ker) := isOfFinOrder_of_finite _
    have := (QuotientGroup.kerLift φ).isOfFinOrder h0
    simpa using this
  have hpos : 0 < orderOf (φ γ) := hfin.orderOf_pos
  obtain ⟨n, hn⟩ := (hfin.mem_powers_iff_mem_zpowers).2 h1
  have hn : φ γ ^ n = φ γ' := hn
  have heq : orderOf (φ γ') = orderOf (φ γ) :=
    Nat.dvd_antisymm (orderOf_dvd_of_mem_zpowers h1) (orderOf_dvd_of_mem_zpowers h2)
  refine ⟨n, ?_, hpos, hn.symm⟩
  rw [← hn, hfin.orderOf_pow] at heq
  have hg : (orderOf (φ γ)).gcd n = 1 := by
    rcases Nat.div_eq_self.1 heq with h | h
    · omega
    · exact h
  exact Nat.Coprime.symm hg

end GlobalTheory.TypeLeaf
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TateH2PeriodDatum
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
open Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Cyc.TwistLift GlobalTheory.TateTop

namespace GlobalTheory.TateTop

theorem tateH2_of_duality_loc (hT : Formalism.GaloisCohomology.LocalTateDualityK) :
    ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l), LocalTateTopDegree (P.PD K) := by
  intro l _ P K LL _ _ _ O _ _ hO L1 hL1
  obtain ⟨hΦ1, hΦ2⟩ := continuous_fixingSubgroupEquiv K.1
  set Φ := K.1.fixingSubgroupEquiv with hΦ
  have hcyc : IsCyc P.χQ := P.χQ_cyc
  let χZ : Formalism.GaloisCohomology.GK l K.1 →* ℤ_[l]ˣ := (cyclotomicCharacter (PadicAlgCl l) l).comp
      (MulSemiringAction.toRingAut (Formalism.GaloisCohomology.GK l K.1) (PadicAlgCl l))
  have hχZ : ∀ g, ((χZ g : ℤ_[l]) : ℚ_[l]) = (P.χQ (Φ.symm g : GQ l) : ℚ_[l]) := fun g => by
    rw [isCyc_unique hcyc (isCyc_cycChar l)]; rfl
  have hχc : Continuous fun g => (χZ g : ℤ_[l]) := by
    rw [continuous_iff_coe]
    simp only [hχZ]
    exact hcyc.continuous.comp (continuous_subtype_val.comp hΦ1)
  obtain ⟨c, hc⟩ := exists_gen_all hχc fun r => by
    have : NeZero (l ^ (r + 1)) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
    exact exists_gen hχc
      (hT l K.1 K.2 (r + 1) (ZMod (l ^ (r + 1))) (ReciprocityTheory.Gal.charRep (redChar χZ (r + 1)))
        (Nat.succ_pos _) (contAction_charRep _ ((continuous_toZModPow _).comp hχc))).1
      fun M _ _ _ _ _ rho hrho => (hT l K.1 K.2 (r + 1) M rho (Nat.succ_pos _) hrho).2.2.2.2
  have hcpt : CompactSpace (GK K) := Φ.symm.surjective.compactSpace hΦ1
  obtain ⟨ι, hι⟩ := exists_ringHom hO
  let : Module ℤ_[l] (LL ⧸ L1.T) := Module.compHom _ ι
  have : SMulCommClass ℤ_[l] O (LL ⧸ L1.T) := ⟨fun a o x => smul_comm (ι a) o x⟩
  have hs : ∀ (a : ℤ_[l]) (x : LL), a • (Submodule.Quotient.mk x : LL ⧸ L1.T) =
      Submodule.Quotient.mk (algebraMap ℚ_[l] LL a * x) := fun a x => by
    rw [← hι, ← Algebra.smul_def]
    rfl
  refine @h2_equiv_of_torsion_character l _ (GK K) _ _ _ _ _ _ hcpt _ (fun r => (hc r).transport Φ hΦ2 hΦ1)
    (fun x => ?_) O _ _ _ _ fun g x => ?_
  · obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨n, hn⟩ := exists_pow_smul_mem hO x
    refine ⟨n, ?_⟩
    rw [hs, Submodule.Quotient.mk_eq_zero, hL1]
    simpa using hn 1
  · obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [hs]
    have h1 := hχZ (Φ g)
    rw [show Φ.symm (Φ g) = g from Φ.symm_apply_apply g, ← P.PD_χ K g] at h1
    change Submodule.Quotient.mk (algebraMap ℚ_[l] LL ((P.PD K).χ g : ℚ_[l]) * x) = _
    rw [← h1]
    rfl

end GlobalTheory.TateTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TeichmullerEpsilonRootsMemFrobeniusPerfectionMod
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Decompl
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.DecomplPerf

section Generic

variable {U E R : Type} [CommRing U] [CommRing E] [CommRing R] (p : ℕ) (τ : U →* R)
  (φ : R →+* R) (io : E →+* R) (ψ : E → E)

theorem persist (hψ : ∀ e, io (ψ e) = φ (io e)) {x : R} {n : ℕ}
    (h : ∃ e r, φ^[n] x = io e + (p : R) * r) (k : ℕ) :
    ∃ e r, φ^[n + k] x = io e + (p : R) * r := by
  induction k with
  | zero => exact h
  | succ k ih =>
    obtain ⟨e, r, h⟩ := ih
    refine ⟨ψ e, φ r, ?_⟩
    rw [← add_assoc, Function.iterate_succ_apply', h, map_add (f := _), map_mul, map_natCast, hψ]

theorem closure_perf (hψ : ∀ e, io (ψ e) = φ (io e)) (h0 : τ 0 = 0)
    (hadd : ∀ x y, ∃ r, τ (x + y) = τ x + τ y + (p : R) * r)
    (hneg : ∀ x, ∃ r, τ (-x) = -τ x + (p : R) * r) (S : Set U)
    (hS : ∀ u ∈ S, ∃ n e r, φ^[n] (τ u) = io e + (p : R) * r) :
    ∀ u ∈ Subring.closure S, ∃ n e r, φ^[n] (τ u) = io e + (p : R) * r := by
  intro u hu
  induction hu using Subring.closure_induction with
  | mem x hx => exact hS x hx
  | zero => exact ⟨0, 0, 0, by simp [h0]⟩
  | one => exact ⟨0, 1, 0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨n, hn⟩ := hx
    obtain ⟨m, hm⟩ := hy
    obtain ⟨e, r, h⟩ := persist p φ io ψ hψ hn m
    obtain ⟨e', r', h'⟩ := persist p φ io ψ hψ hm n
    obtain ⟨c, hc⟩ := hadd x y
    rw [add_comm m n] at h'
    rw [← RingHom.coe_pow] at h h'
    refine ⟨n + m, e + e', r + r' + (φ ^ (n + m)) c, ?_⟩
    rw [← RingHom.coe_pow, hc, map_add (f := _), map_add (f := _), map_mul, map_natCast, h, h', map_add (f := _)]
    ring
  | neg x _ hx =>
    obtain ⟨n, e, r, h⟩ := hx
    obtain ⟨c, hc⟩ := hneg x
    rw [← RingHom.coe_pow] at h
    refine ⟨n, -e, -r + (φ ^ n) c, ?_⟩
    rw [← RingHom.coe_pow, hc, map_add (f := _), map_neg, map_mul, map_natCast, h, map_neg]
    ring
  | mul x y _ _ hx hy =>
    obtain ⟨n, hn⟩ := hx
    obtain ⟨m, hm⟩ := hy
    obtain ⟨e, r, h⟩ := persist p φ io ψ hψ hn m
    obtain ⟨e', r', h'⟩ := persist p φ io ψ hψ hm n
    rw [add_comm m n] at h'
    rw [← RingHom.coe_pow] at h h'
    refine ⟨n + m, e * e', io e * r' + r * (io e' + p * r'), ?_⟩
    rw [← RingHom.coe_pow, map_mul, map_mul, h, h', map_mul]
    ring

theorem iterate_τ (hφ : ∀ u, φ (τ u) = τ (u ^ p)) (n : ℕ) (u : U) :
    φ^[n] (τ u) = τ (u ^ p ^ n) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply', ih, hφ, ← pow_mul, pow_succ]

end Generic

variable {l : ℕ} [Fact l.Prime]

def teichW (l : ℕ) [Fact l.Prime] : OCb l →* WCb l :=
  (inclW l : Ainf l →* WCb l).comp (WittVector.teichmuller l)

theorem teichW_apply (u : OCb l) : teichW l u = inclW l (WittVector.teichmuller l u) := rfl

theorem teichW_coeff (u : OCb l) : (teichW l u).coeff 0 = algebraMap (OCb l) (Cb l) u := by
  rw [teichW_apply, coeff_inclW, WittVector.teichmuller_coeff_zero]

theorem teichW_add (x y : OCb l) :
    ∃ r, teichW l (x + y) = teichW l x + teichW l y + (l : WCb l) * r := by
  obtain ⟨r, hr⟩ := (coeff_zero_eq_zero_iff (teichW l (x + y) - teichW l x - teichW l y)).1 (by
    rw [sub_coeff_zero, sub_coeff_zero, teichW_coeff, teichW_coeff, teichW_coeff, map_add (f := _)]
    ring)
  exact ⟨r, by linear_combination hr⟩

theorem teichW_zero : teichW l 0 = 0 := by
  rw [teichW_apply, WittVector.teichmuller_zero, map_zero]

theorem teichW_neg (x : OCb l) : ∃ r, teichW l (-x) = -teichW l x + (l : WCb l) * r := by
  obtain ⟨r, hr⟩ := teichW_add x (-x)
  rw [add_neg_cancel, teichW_zero] at hr
  exact ⟨-r, by linear_combination -hr⟩

theorem frobW_teichW (u : OCb l) : frobW l (teichW l u) = teichW l (u ^ l) := by
  change WittVector.map (frobenius (Cb l) l) (teichW l u) = _
  rw [teichW_apply, teichW_apply, inclW, WittVector.map_teichmuller, WittVector.map_teichmuller,
    WittVector.map_teichmuller, frobenius_def, ← map_pow]

theorem εroot_pow {P : LocPrime l} (AI : LocAinf l P) (k : ℕ) : AI.εroot k ^ l ^ k = AI.ε := by
  induction k with
  | zero => simp [LocAinf.εroot]
  | succ k ih =>
    rw [LocAinf.εroot, Function.iterate_succ_apply', pow_succ', pow_mul, frobeniusEquiv_symm_pow_p]
    exact ih

def rightW (LL : FinExt l) : WCb l →+* RW LL :=
  (Algebra.TensorProduct.includeRight : WCb l →ₐ[ℤ_[l]] RW LL).toRingHom

def teichR (LL : FinExt l) : OCb l →* RW LL := (rightW LL : WCb l →* RW LL).comp (teichW l)

theorem teichR_apply (LL : FinExt l) (u : OCb l) : teichR LL u = rightW LL (teichW l u) := rfl

theorem φRW_teichR (LL : FinExt l) (u : OCb l) :
    (φRW LL : RW LL →+* RW LL) (teichR LL u) = teichR LL (u ^ l) :=
  congrArg (rightW LL) (frobW_teichW u)

theorem teichR_εroot {P : LocPrime l} (AI : LocAinf l P) (LL : FinExt l) (s : ℕ) :
    teichR LL (AI.εroot s) = piR AI LL s + 1 := by
  have h : teichW l (AI.εroot s) = inclW l (piW AI s) + 1 := by
    rw [piW, map_sub, map_one, sub_add_cancel, teichW_apply]
  rw [teichR_apply, h, map_add (f := _), map_one]
  rfl

theorem isIntegral_of_pow_eq_one {A B : Type} [CommRing A] [CommRing B] [Algebra A B] {x : B}
    {m : ℕ} (hm : 0 < m) (hx : x ^ m = 1) : IsIntegral A x :=
  IsIntegral.of_pow hm (hx ▸ isIntegral_one)

theorem add_one_pow_eq_ringHom_image_add_prime_mul_zero {E R : Type} [CommRing E] [CommRing R] (io : E →+* R) (p : ℕ) (a : E) (t : R)
    (ha : io a = t) (k : ℕ) : (t + 1) ^ k = io ((a + 1) ^ k) + (p : R) * 0 := by
  rw [map_pow, map_add (f := _), map_one, ha, mul_zero, add_zero]

theorem gen_aux₀ {E R : Type} [CommRing E] [CommRing R] (φ : R →+* R) (io : E →+* R) (p : ℕ)
    (a : E) (t : R) (ha : io a = t) : ∃ n e r, φ^[n] t = io e + (p : R) * r :=
  ⟨0, a, 0, by simp [ha]⟩


set_option maxHeartbeats 800000 in
theorem teich_mem_perfection : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (W : Wach P K LL) (E : EtSit P AI K s LL h W), ∀ u ∈ Subring.closure (Set.range AI.εroot ∪ {xb | ∃ c : Om l, c ∈ K0 K ∧ ∃ m : ℕ, 0 < m ∧ ¬ l ∣ m ∧ c ^ m = 1 ∧ IsTiltOf c m xb}), ∃ (n : ℕ) (e : W.EE) (r : RW LL), (φRW LL)^[n] ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] inclW l (WittVector.teichmuller l u)) = E.tie.ioE e + (l : RW LL) * r := by
  intro l _ P AI K s LL h W E
  obtain ⟨h1, -, h3, -⟩ := GlobalTheory.Decompl.ioE_compat l P AI K s LL h W E
  refine closure_perf l (teichR LL) (φRW LL : RW LL →+* RW LL) (E.tie.ioE : W.EE →+* RW LL)
    W.φE h1 ?_ ?_ ?_ _ ?_
  · rw [teichR_apply, teichW_zero]; exact (rightW LL).map_zero
  · intro x y
    obtain ⟨r, hr⟩ := teichW_add x y
    refine ⟨rightW LL r, ?_⟩
    rw [teichR_apply, teichR_apply, teichR_apply, hr, map_add (f := _), map_add (f := _),
      (rightW LL).map_mul, map_natCast (rightW LL)]
  · intro x
    obtain ⟨r, hr⟩ := teichW_neg x
    refine ⟨rightW LL r, ?_⟩
    rw [teichR_apply, teichR_apply, hr, map_add (f := _), (rightW LL).map_neg,
      (rightW LL).map_mul, map_natCast (rightW LL)]
  · rintro u (⟨k, rfl⟩ | ⟨c, hc, m, hm, hlm, hcm, hxb⟩)
    · refine ⟨k, (algebraMap (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) W.EE letπ + 1) ^ l ^ s,
        0, ?_⟩
      have e1 := iterate_τ l (teichR LL) (φRW LL : RW LL →+* RW LL) (φRW_teichR LL) k (AI.εroot k)
      have e2 : teichR LL (AI.εroot k ^ l ^ k) = teichR LL (AI.εroot s) ^ l ^ s := by
        rw [εroot_pow, ← εroot_pow AI s]
        exact (teichR LL).map_pow _ _
      rw [teichR_εroot] at e2
      exact (e1.trans e2).trans (add_one_pow_eq_ringHom_image_add_prime_mul_zero (E.tie.ioE : W.EE →+* RW LL) l _ _ h3 _)
    · have hc' : (⟨c, hc⟩ : ↥(K0 K)) ^ m = 1 := Subtype.ext hcm
      have hint : ∀ i, IsIntegral ℤ_[l] (W.emb i ⟨c, hc⟩) := fun i =>
        isIntegral_of_pow_eq_one hm (by rw [← map_pow, hc', map_one])
      have e1 := E.inertia_action_on_roots ⟨c, hc⟩ m hm hlm hcm u hxb (fun i => ⟨W.emb i ⟨c, hc⟩, hint i⟩)
        (fun i => rfl)
      have e2 := (E.tie.ioE_ext _).trans (congrArg (inclR LL) e1)
      exact gen_aux₀ (φRW LL : RW LL →+* RW LL) (E.tie.ioE : W.EE →+* RW LL) l _ _ e2

end GlobalTheory.DecomplPerf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ToMatrixRepOf
section
noncomputable section

namespace GlobalTheory.PMon

variable {F G ι : Type} [Field F] [Group G] [Fintype ι] [DecidableEq ι]

def repOf (ρ₀ : G →* GL ι F) : Representation F G (ι → F) where
  toFun g := Matrix.toLin' (ρ₀ g : Matrix ι ι F)
  map_one' := by simp; rfl
  map_mul' g h := by simp [Matrix.toLin'_mul]; rfl

@[simp] theorem repOf_apply (ρ₀ : G →* GL ι F) (g : G) (v : ι → F) :
    repOf ρ₀ g v = (ρ₀ g : Matrix ι ι F).mulVec v := rfl

theorem toMatrix_repOf (ρ₀ : G →* GL ι F) (g : G) :
    LinearMap.toMatrix (Pi.basisFun F ι) (Pi.basisFun F ι) (repOf ρ₀ g) = (ρ₀ g : Matrix ι ι F) := by
  rw [LinearMap.toMatrix_eq_toMatrix']
  exact LinearMap.toMatrix'_toLin' _

end GlobalTheory.PMon

end
end

