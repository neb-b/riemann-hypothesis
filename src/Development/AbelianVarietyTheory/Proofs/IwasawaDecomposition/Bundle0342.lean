module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IncludeLInjective
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0329
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentAndTwistData
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDimensionalForms
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0174
public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0254
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0327
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteCosetsHeckeSetAtSplitPlaceOutsideLevel
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmQuadraticFormEqAlternatingForm
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0110
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0330
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitsLiftSpec
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0334
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SideMultiplicityFamily
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
public import Formalism.LocalToGlobal.HermitianForms.Bundle0006

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryExtensionOfCmTypeFamily
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

namespace GlobalTheory.CMExt

def tinv {n : ℕ} {K : Type} [Field K] (A : GL (Fin n) K) : GL (Fin n) K :=
  ⟨Matrix.transpose ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K),
   Matrix.transpose ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K),
   by rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one],
   by rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]⟩

theorem coe_tinv {n : ℕ} {K : Type} [Field K] (A : GL (Fin n) K) :
    ((tinv A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      Matrix.transpose ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := rfl

theorem coe_tinv_inv {n : ℕ} {K : Type} [Field K] (A : GL (Fin n) K) :
    (((tinv A)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      Matrix.transpose ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := rfl

theorem comp_conj_conj {L : Type} [Field L] [NumberField L] [IsCMField L] {K : Type} [Field K] (σ : L →+* K) :
    (σ.comp (IsCMField.complexConj L : L →+* L)).comp (IsCMField.complexConj L : L →+* L) = σ := by
  ext x
  simp [IsCMField.complexConj_apply_apply]

noncomputable def cmExtend {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {ι : Type} {K : Type} [Field K]
    (emb : ι → L →+* K) (g : ι → GL (Fin n) K) (σ : L →+* K) : GL (Fin n) K := by
  classical
  exact if h : ∃ τ, σ = emb τ then g h.choose
    else if h' : ∃ τ, σ = (emb τ).comp (IsCMField.complexConj L : L →+* L) then tinv (g h'.choose) else 1

end GlobalTheory.CMExt

open GlobalTheory.CMExt in
theorem GlobalTheory.cmType_family_extend : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (ι : Type) [Fintype ι] (K : Type) [Field K]
    (emb : ι → L →+* K), GlobalTheory.AlgWtF.CMDist emb → ∀ g : ι → GL (Fin n) K, ∃ B : (L →+* K) → GL (Fin n) K,
    (∀ σ : L →+* K, ((B (σ.comp (IsCMField.complexConj L : L →+* L)) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        Matrix.transpose (((B σ)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) ∧ ∀ τ, B (emb τ) = g τ := by
  intro L _ _ _ n ι _ K _ emb hd g
  classical
  have hinj2 : ∀ τ τ', (emb τ).comp (IsCMField.complexConj L : L →+* L) = (emb τ').comp (IsCMField.complexConj L : L →+* L) → τ = τ' := by
    intro τ τ' h
    apply hd.1
    have := congrArg (fun s : L →+* K => s.comp (IsCMField.complexConj L : L →+* L)) h
    simpa [comp_conj_conj] using this
  have v1 : ∀ τ, cmExtend emb g (emb τ) = g τ := by
    intro τ
    have h : ∃ τ', emb τ = emb τ' := ⟨τ, rfl⟩
    simp only [cmExtend, dif_pos h]
    rw [hd.1 h.choose_spec.symm]
  have v2 : ∀ τ, cmExtend emb g ((emb τ).comp (IsCMField.complexConj L : L →+* L)) = tinv (g τ) := by
    intro τ
    have h : ¬ ∃ τ', (emb τ).comp (IsCMField.complexConj L : L →+* L) = emb τ' := by
      rintro ⟨τ', h⟩
      exact hd.2 τ' τ h.symm
    have h' : ∃ τ', (emb τ).comp (IsCMField.complexConj L : L →+* L) = (emb τ').comp (IsCMField.complexConj L : L →+* L) := ⟨τ, rfl⟩
    simp only [cmExtend, dif_neg h, dif_pos h']
    rw [hinj2 _ _ h'.choose_spec.symm]
  have v3 : ∀ σ, (¬ ∃ τ, σ = emb τ) → (¬ ∃ τ, σ = (emb τ).comp (IsCMField.complexConj L : L →+* L)) → cmExtend emb g σ = 1 := by
    intro σ h h'
    simp only [cmExtend, dif_neg h, dif_neg h']
  refine ⟨cmExtend emb g, ?_, v1⟩
  intro σ
  by_cases h : ∃ τ, σ = emb τ
  · obtain ⟨τ, rfl⟩ := h
    rw [v2, v1, coe_tinv]
  · by_cases h' : ∃ τ, σ = (emb τ).comp (IsCMField.complexConj L : L →+* L)
    · obtain ⟨τ, rfl⟩ := h'
      rw [comp_conj_conj, v1, v2, coe_tinv_inv, Matrix.transpose_transpose]
    · have e1 : ¬ ∃ τ, σ.comp (IsCMField.complexConj L : L →+* L) = emb τ := by
        rintro ⟨τ, hτ⟩
        apply h'
        refine ⟨τ, ?_⟩
        rw [← hτ, comp_conj_conj]
      have e2 : ¬ ∃ τ, σ.comp (IsCMField.complexConj L : L →+* L) = (emb τ).comp (IsCMField.complexConj L : L →+* L) := by
        rintro ⟨τ, hτ⟩
        apply h
        refine ⟨τ, ?_⟩
        have := congrArg (fun s : L →+* K => s.comp (IsCMField.complexConj L : L →+* L)) hτ
        simpa [comp_conj_conj] using this
      rw [v3 _ e1 e2, v3 _ h h']
      simp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FifteenNotMemAndDeltaInertiaOrderDividesFifteenPStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fifteen_not_mem_and_delta_inertia_order_divides_fifteen_pow : ∀ (D : D7) (T : TwR D.LL0 D.nd) (i : T.Tw) (P : PlE D.host), P ∈ T.pD i →
    ((15 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal ∧ ∀ A : ValuationSubring D.nd.Om, IsPlaceOver A P → ∀ σ ∈ Ine (F := D.host.E) A,
      ∃ N : ℕ, T.delta i σ ^ (15 ^ N) = 1 := by
  first | exact @GlobalTheory.Member.DeltaTame.delta_tame_and_15 | exact GlobalTheory.Member.DeltaTame.delta_tame_and_15 | (intros; apply GlobalTheory.Member.DeltaTame.delta_tame_and_15 <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteHeckeDoubleCosetCosetsAtSplitPlace
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.TSetFinLoc

open GlobalTheory.TSetFin

theorem finite_image_tSet_loc : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (s : SplitPlace L)
    (ϖ : s.v.adicCompletion (maximalRealSubfield L)), IsUnif L s.v ϖ → ∀ J : Subgroup (GAf L n),
    (∀ κ, TrivOutside {s.v} κ → (κ ∈ J ↔ κ ∈ Umax L n)) → ∀ k : ℕ,
    ((fun x : GAf L n => (x : GAf L n ⧸ J)) '' tSet L n s ϖ k).Finite := by
  intro L _ _ _ n s ϖ hϖ J hJ k
  classical
  obtain ⟨c, hc⟩ := approx_class s.v
  haveI : Finite (𝓞 (maximalRealSubfield L) ⧸ s.v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ s.v.ne_bot
  let κ : GAf L n → (Fin n → Fin n → 𝓞 (maximalRealSubfield L) ⧸ s.v.asIdeal) := fun x =>
    if h : x ∈ tSet L n s ϖ k then
      fun i j => c (((h.2.choose : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) :
        Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) i j)
    else 0
  have key : ∀ x ∈ tSet L n s ϖ k, ∀ x' ∈ tSet L n s ϖ k, κ x = κ x' →
      (x : GAf L n ⧸ J) = x' := by
    intro x hx x' hx' hκ
    simp only [κ, dif_pos hx, dif_pos hx'] at hκ
    obtain ⟨ha, b, hb, hg⟩ := hx.2.choose_spec
    obtain ⟨ha', b', hb', hg'⟩ := hx'.2.choose_spec
    set a := hx.2.choose
    set a' := hx'.2.choose
    have ia := glint_int ha
    have ia' := glint_int ha'
    have ib := glint_int hb
    have ib' := glint_int hb'
    have hcl : ∀ i j, Valued.v ((a : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) i j -
        (a' : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) i j) < 1 := fun i j =>
      hc _ _ (ia.1 i j) (ia'.1 i j) (congrFun (congrFun hκ i) j)
    have hcl' : ∀ i j, Valued.v ((a' : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) i j -
        (a : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) i j) < 1 := fun i j => by
      rw [← Valuation.map_neg, neg_sub]; exact hcl i j
    have hunif : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hϖ
    have h1 := local_int s.v ϖ k hunif a a' b b' _ _ ia'.1 ia.2 ib.2 ib'.1 hcl hg hg'
    have h2 := local_int s.v ϖ k hunif a' a b' b _ _ ia.1 ia'.2 ib'.2 ib.1 hcl' hg' hg
    rw [QuotientGroup.eq]
    have htriv : TrivOutside {s.v} (x⁻¹ * x') := triv_mul (triv_inv hx.1) hx'.1
    refine (hJ _ htriv).2 ?_
    exact mem_Umax_of_loc s _ htriv (fun i j => by
      rw [map_mul, map_inv]; exact h1 i j) (fun i j => by
      rw [mul_inv_rev, inv_inv, map_mul, map_inv]; exact h2 i j)
  let g : GAf L n ⧸ J → (Fin n → Fin n → 𝓞 (maximalRealSubfield L) ⧸ s.v.asIdeal) := fun q =>
    if h : ∃ x ∈ tSet L n s ϖ k, (x : GAf L n ⧸ J) = q then κ h.choose else 0
  refine Set.Finite.of_finite_image (f := g) (Set.toFinite _) ?_
  rintro _ ⟨x, hx, rfl⟩ _ ⟨x', hx', rfl⟩ hgg
  have h : ∃ y ∈ tSet L n s ϖ k, (y : GAf L n ⧸ J) = x := ⟨x, hx, rfl⟩
  have h' : ∃ y ∈ tSet L n s ϖ k, (y : GAf L n ⧸ J) = x' := ⟨x', hx', rfl⟩
  simp only [g, dif_pos h, dif_pos h'] at hgg
  show (x : GAf L n ⧸ J) = x'
  rw [← h.choose_spec.2, ← h'.choose_spec.2]
  exact key _ h.choose_spec.1 _ h'.choose_spec.1 hgg

end GlobalTheory.TSetFinLoc

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FourMulRootLt
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top NumberField IsDedekindDomain

namespace GlobalTheory.Mem.Top.TamePow

theorem four_mul_root_lt {m k g : ℝ} (hm : 2 ≤ m) (hk : m + 3 ≤ k) (hg : k ^ 8 ≤ g) :
    4 * m * g ^ ((1 : ℝ) / 4) < g - 1 := by
  have hk5 : (5 : ℝ) ≤ k := by linarith
  have hg0 : 0 ≤ g := le_trans (by positivity) hg
  set t := g ^ ((1 : ℝ) / 4) with ht
  have ht4 : t ^ 4 = g := by
    rw [ht, ← Real.rpow_natCast, ← Real.rpow_mul hg0]
    norm_num
  have hkt : k ^ 2 ≤ t := by
    have h8 : (k ^ 8) ^ ((1 : ℝ) / 4) ≤ t := Real.rpow_le_rpow (by positivity) hg (by norm_num)
    have e : (k ^ 8) ^ ((1 : ℝ) / 4) = k ^ 2 := by
      rw [show (k ^ 8 : ℝ) = (k ^ 2) ^ (4 : ℕ) by ring, ← Real.rpow_natCast,
        ← Real.rpow_mul (by positivity)]
      norm_num
    linarith
  have ht25 : 25 ≤ t := by nlinarith
  have h1 : 4 * m * t < k ^ 2 * t := by
    have : 4 * m < k ^ 2 := by nlinarith
    exact mul_lt_mul_of_pos_right this (by linarith)
  have h2 : k ^ 2 * t ≤ t * t := mul_le_mul_of_nonneg_right hkt (by linarith)
  have hs : 625 ≤ t * t := by nlinarith
  have h3 : t * t + 1 < t ^ 4 := by
    have e4 : t ^ 4 = t * t * (t * t) := by ring
    have := mul_le_mul_of_nonneg_right hs (by positivity : (0 : ℝ) ≤ t * t)
    nlinarith
  linarith

theorem bound_of_over (K : Ctx) (B : Pre) (h : K.Over B) (i : Fin 2) :
    4 * (B.R.m : ℝ) * (B.host.g i : ℝ) ^ ((1 : ℝ) / 4) < (B.host.g i : ℝ) - 1 := by
  obtain ⟨sp, hT, hY, hA, hV, hz, rfl, -⟩ := h
  show 4 * (K.P.R.m : ℝ) * (K.P.H.g i : ℝ) ^ ((1 : ℝ) / 4) < (K.P.H.g i : ℝ) - 1
  have hr : RankVal K.s K.P.R := K.ok.rank
  unfold RankVal at hr
  obtain ⟨-, ⟨-, hm⟩, ⟨hk, -⟩, -⟩ := hr
  have hv : HostVal K.s K.C.P.Cpde K.P.H := K.ok.val
  unfold HostVal at hv
  obtain ⟨-, -, -, -, hg, -⟩ := hv
  have hx1 : 1 < K.s.x := K.s.one_lt_alt
  have he0 : 0 < K.s.eps := K.s.eps_pos
  have hx0 : (0 : ℝ) ≤ K.s.x := by linarith
  have hd1 : K.s.delta1 ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1.le (by linarith)
  have hd0 : 0 ≤ K.s.delta1 := Real.rpow_nonneg hx0 _
  set y := Real.sqrt K.s.x with hy
  have hy2 : y ^ 2 = K.s.x := Real.sq_sqrt hx0
  have hy1 : 1 ≤ y := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hx1.le
  have hmy : (K.P.R.m : ℝ) ≤ 2 * y := by
    have : Real.sqrt (K.s.x * K.s.delta1) ≤ y := Real.sqrt_le_sqrt (by nlinarith)
    linarith
  have hk4 : K.s.x ^ (4 : ℕ) ≤ (K.P.R.k : ℝ) := by
    have h1 : K.s.x ^ (4 : ℝ) ≤ K.s.x ^ ((9 : ℝ) / 2 + 10 * K.s.eps) :=
      Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith)
    have h2 : K.s.x ^ (4 : ℝ) = K.s.x ^ (4 : ℕ) := by exact_mod_cast Real.rpow_natCast K.s.x 4
    exact le_trans (le_trans h2.symm.le h1) hk
  have hk8 : y ^ 8 ≤ (K.P.R.k : ℝ) := by
    have : y ^ 8 = K.s.x ^ (4 : ℕ) := by rw [← hy2]; ring
    linarith
  have hk2 : (2 : ℝ) ≤ K.P.R.k := by
    have h1 : (1 : ℝ) < K.P.R.k := lt_of_lt_of_le (one_lt_pow₀ hx1 (by norm_num)) hk4
    have h2 : 1 < K.P.R.k := by exact_mod_cast h1
    exact_mod_cast h2
  have hb : (2.718 : ℝ) ≤ K.s.b := by
    have hL : 1 ≤ K.s.L := Real.one_le_rpow hx1.le he0.le
    have h1 : Real.exp 1 ≤ K.s.b := Real.exp_le_exp.2 hL
    have h2 := Real.exp_one_gt_d9
    linarith
  have hkb1 : (5 : ℝ) ≤ (K.P.R.k : ℝ) * K.s.b := by nlinarith
  have hkb2 : 2 * y + 3 ≤ (K.P.R.k : ℝ) * K.s.b := by
    have hkb : 2.718 * (K.P.R.k : ℝ) ≤ (K.P.R.k : ℝ) * K.s.b := by nlinarith
    by_cases h5 : (5 : ℝ) ≤ (K.P.R.k : ℝ)
    · have : y ≤ y ^ 8 := le_self_pow₀ hy1 (by norm_num)
      linarith
    · push_neg at h5
      have hk4' : (K.P.R.k : ℝ) ≤ 4 := by
        have : K.P.R.k < 5 := by exact_mod_cast h5
        have : K.P.R.k ≤ 4 := by omega
        exact_mod_cast this
      have hy12 : y ≤ 1.2 := by
        by_contra hc
        push_neg at hc
        have : (1.2 : ℝ) ^ 8 < y ^ 8 := pow_lt_pow_left₀ hc (by norm_num) (by norm_num)
        norm_num at this
        linarith
      linarith
  have hM : max 2 (K.P.R.m : ℝ) + 3 ≤ (K.P.R.k : ℝ) * K.s.b := by
    have : max 2 (K.P.R.m : ℝ) ≤ (K.P.R.k : ℝ) * K.s.b - 3 := max_le (by linarith) (by linarith)
    linarith
  have hmain := four_mul_root_lt (le_max_left 2 (K.P.R.m : ℝ)) hM (hg i).1
  have ht : (0 : ℝ) ≤ (K.P.H.g i : ℝ) ^ ((1 : ℝ) / 4) := Real.rpow_nonneg (by positivity) _
  have hle : 4 * (K.P.R.m : ℝ) * (K.P.H.g i : ℝ) ^ ((1 : ℝ) / 4) ≤
      4 * max 2 (K.P.R.m : ℝ) * (K.P.H.g i : ℝ) ^ ((1 : ℝ) / 4) := by
    have : (K.P.R.m : ℝ) ≤ max 2 (K.P.R.m : ℝ) := le_max_right _ _
    nlinarith
  linarith

theorem tame_of_pow : Ev fun K => ∀ X : Stages, K.Over X.B.toPre → (∀ (k : Fin 2) (v : X.N.nd.PlG k), ∃ w : (ZMod (X.B.host.g k))ˣ, orderOf w = X.B.host.g k - 1 ∧ ∀ j : Fin X.B.R.m, X.N.nd.chiT k v j = w ^ (2 * (j.1 + 1))) → ∀ (k : Fin 2) (v : X.toD7.nd.PlG k), haveI : Fact (X.toD7.host.g k).Prime := ⟨X.toD7.host.g_prime k⟩; DC.TameDistinct X.toD7.R.r (X.toD7.host.g k) (X.toD7.nd.chiT k v) := by
  have key : ∀ K : Ctx, ∀ X : Stages, K.Over X.B.toPre → (∀ (k : Fin 2) (v : X.N.nd.PlG k),
      ∃ w : (ZMod (X.B.host.g k))ˣ, orderOf w = X.B.host.g k - 1 ∧
        ∀ j : Fin X.B.R.m, X.N.nd.chiT k v j = w ^ (2 * (j.1 + 1))) →
      ∀ (k : Fin 2) (v : X.toD7.nd.PlG k), haveI : Fact (X.toD7.host.g k).Prime := ⟨X.toD7.host.g_prime k⟩;
        DC.TameDistinct X.toD7.R.r (X.toD7.host.g k) (X.toD7.nd.chiT k v) := by
    intro K X hO hpow k v
    obtain ⟨w, hw, hchi⟩ := hpow k v
    have hb := bound_of_over K X.B.toPre hO k
    have hr : 1 ≤ X.toD7.R.r := by
      have h2 := X.toD7.R.two_le_m
      first
      | (show 1 ≤ X.toD7.R.k + X.toD7.R.m - 1; omega)
      | omega
      | (simp only [Formalism.MainNotions.Ranks.r]; omega)
      | (unfold Formalism.MainNotions.Ranks.r; omega)
    have e : X.toD7.nd.chiT k v = fun j : Fin X.B.R.m => w ^ (2 * (j.1 + 1)) := funext hchi
    haveI : Fact (X.toD7.host.g k).Prime := ⟨X.toD7.host.g_prime k⟩
    have h := GlobalTheory.EX.DC.TameGen.tameDistinct_gen X.toD7.R.r (X.toD7.host.g k) X.B.R.m w hw hb hr
    rw [e]
    exact h
  unfold Ev
  refine ⟨1, one_pos, ?_⟩
  intro eps C8 _ _ _ _
  refine ⟨?k0, fun C _ _ _ => ⟨0, fun cD _ => ⟨0, fun ch _ => ⟨0, fun K => ?_⟩⟩⟩⟩
  case k0 => first | exact ⟨0, 0, 0, 0⟩ | exact default | exact Classical.arbitrary _
  first
  | exact key K
  | exact fun _ => key K
  | exact fun _ _ => key K
  | exact fun _ _ _ => key K
  | exact fun _ _ _ _ => key K
  | exact fun _ _ _ _ _ => key K
  | exact fun _ _ _ _ _ _ => key K
  | exact fun _ _ _ _ _ _ _ => key K
  | exact fun _ _ _ _ _ _ _ _ => key K

end GlobalTheory.Mem.Top.TamePow
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GenericCharacterProjectorOnTwistFormsFix
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.HeightCounting.FormsStep

theorem piKop_fix : ∀ (D : D7) (T : TwR D.LL0 D.nd) (S : RatDat D.ntw) (In : RatIn D S) (i : T.Tw) (j : ℕ) (b : Bool),
    ∀ y ∈ Fm0T D T S In.rho In.chi In.θ i j b, piKop D T S In i j b y = y := by
  intro D T S In i j b y hy
  classical
  haveI : Fintype (Formalism.IndefR.NX.U D.nd) := Fintype.ofFinite _
  have hu : ∀ u : Formalism.IndefR.NX.U D.nd, (actGT D T S In.rho In.chi i j b (u : G0g D.nd)) y =
      ((psiUT D T In.θ i b u : (FractionRing (T.O i))ˣ) : FractionRing (T.O i)) • y := by
    intro u
    have h := (Submodule.mem_iInf _).1 hy u
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at h
    simpa using h
  unfold piKop
  rw [finsum_eq_sum_of_fintype, LinearMap.sum_apply]
  have hterm : ∀ u : Formalism.IndefR.NX.U D.nd,
      (readT D T i b (piCoef D In.θ u) • (actGT D T S In.rho In.chi i j b (u : G0g D.nd)).toLinearMap) y =
        readT D T i b ((Nat.card (Formalism.IndefR.NX.U D.nd) : ↥D.LL0)⁻¹) • y := by
    intro u
    rw [LinearMap.smul_apply, LinearEquiv.coe_toLinearMap, hu, smul_smul]
    congr 1
    unfold piCoef psiUT
    simp only [MonoidHom.coe_comp, Function.comp_apply, Units.coe_map, RingHom.toMonoidHom_eq_coe,
      MonoidHom.coe_coe, ← map_mul, mul_assoc, Units.inv_mul, mul_one]
  rw [Finset.sum_congr rfl (fun u _ => hterm u), Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card]
  rw [← Nat.cast_smul_eq_nsmul (FractionRing (T.O i)), smul_smul]
  have hne : (Nat.card (Formalism.IndefR.NX.U D.nd) : ↥D.LL0) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have : ((Nat.card (Formalism.IndefR.NX.U D.nd) : ℕ) : FractionRing (T.O i)) *
      readT D T i b ((Nat.card (Formalism.IndefR.NX.U D.nd) : ↥D.LL0)⁻¹) = 1 := by
    rw [← map_natCast (readT D T i b), ← map_mul, mul_inv_cancel₀ hne, map_one]
  rw [this, one_smul]

end GlobalTheory.HeightCounting.FormsStep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeEigenspaceNeBotEveryLocalisationPointStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeEigenspace_ne_bot_every_localisation_point : ∀ {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (B : LocBase0 H what₂) (hs : HeckeStd0 B) (hd : FinDimV B) (hL : MtLoc B (partCompl_of hs hd)) (hAct : ActEx B (partCompl_of hs hd)), ActHK B hs hd hL hAct → ∀ (i : LocT B) (x : XOf B i), heckeEig (TOf B i) (actC B (partCompl_of hs hd) hAct i) x ≠ ⊥ := by
  first | exact @GlobalTheory.EigOcc.heckeEig_ne_bot | exact GlobalTheory.EigOcc.heckeEig_ne_bot | (intros; apply GlobalTheory.EigOcc.heckeEig_ne_bot <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeGeneratorPlacesOutsideLevelOfStable
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN

namespace GlobalTheory.GenHypOut

theorem not_mem_bad (D : D7) (cf : Formalism.L2.Host.CharFrame D) (C : NChoice D) (tp : TupTied D cf C) (hQ : QOver C)
    (w : D.what₂.places.Pl) (j : Fin D.R.m) (v : PlE D.host) (k : ℕ) (s : SplitPlace D.host.E)
    (hv : GenAt D (D.what₂.places.resChar w) (C.Q w) v k) (hc : IsConjPl D.host v s.w) :
    s.v ∉ gPl D ∪ qPl D (tp.tup (D.what₂.muTw w) j) := by
  have hov : NG.OverPl v s.v := GlobalTheory.LocLevel.overPl_of_isConjPl hc
  obtain ⟨_, hl, hS, hvQ, _, _⟩ := hv
  have hp : v ∉ placesOver D.host.E
      (if D.what₂.places.resChar w = D.host.pde then D.host.pde' else D.host.pde) :=
    fun h => hS ⟨Or.inr (Or.inr h), hl⟩
  rintro (⟨w', hov', kk, hk⟩ | hq)
  · apply hS
    refine ⟨?_, hl⟩
    have hvk := GlobalTheory.LocLevel.mem_placesOver_of_overPl' hov hov' hk
    fin_cases kk
    · exact Or.inl hvk
    · exact Or.inr (Or.inl hvk)
  · by_cases htw : D.what₂.muAt w ≠ D.what₂.mu0
    · obtain ⟨w', hov', hw'⟩ := GlobalTheory.FitHecke.qPl_sub tp w htw j hq
      rcases hw' with hQ' | hp'
      · exact hvQ (hQ w w' v hQ' ⟨s.v, hov', hov⟩)
      · exact hp (GlobalTheory.LocLevel.mem_placesOver_of_overPl' hov hov' hp')
    · rw [not_not] at htw
      obtain ⟨hg, w', hov', hu⟩ := hq
      apply hu
      unfold TupTied.tup
      rw [tp.xi_tw, tp.psi_un w htw]
      refine HChar.UnrAt.mul ((cf.isMu0 j).unr w' fun kk hk => hg ⟨w', hov', kk, hk⟩)
        (HChar.UnrAt.mul ?_ (((isPsi_one (D.what₂.places.resChar w)).ram w').2 (Finset.notMem_empty _)))
      have hnp : w' ∉ placesOver D.host.E
          (if D.what₂.places.resChar w = D.host.pde then D.host.pde' else D.host.pde) :=
        fun h => hp (GlobalTheory.LocLevel.mem_placesOver_of_overPl' hov hov' h)
      unfold Formalism.L2.Host.CharFrame.delAt
      split_ifs with h
      · exact cf.isDel'.unr w' fun h' => hnp (by rw [if_pos h]; exact h')
      · exact cf.isDel.unr w' fun h' => hnp (by rw [if_neg h]; exact h')

theorem genHyp : ∀ (D : D7) (cf : Formalism.L2.Host.CharFrame D) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C),
    MtInput D M tp.tup C.Q → QOver C → GenHyp M C.Q := by
  intro D cf M C tp hM hQ w j h1 h2
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  refine ⟨gPl D ∪ qPl D (tp.tup (D.what₂.muTw w) ⟨j', by omega⟩), hM.hyp w ⟨j', by omega⟩, ?_⟩
  intro v k s hv hc
  exact not_mem_bad D cf C tp hQ w _ v k s hv hc

end GlobalTheory.GenHypOut
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianColumnsGeneratorsBaseLatticesFunctionalStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianColumns_generators_baseLattices_functionals : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)) (A : ∀ u, Formalism.L2.Herm.AtT (I.rec7 l Z) u (H.vT u) (H.Fv u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → CarT H F A → (∀ u (w : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)) (h : ((((I.rec7 l Z).mem u).A.T : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∈ w.asIdeal) (a : intV (I.rec7 l Z).host.E w), (a : TensorProduct (I.rec7 l Z).host.F (I.rec7 l Z).host.E (w.adicCompletion (I.rec7 l Z).host.F)) = inclE (F := (I.rec7 l Z).host.F) (w.adicCompletion (I.rec7 l Z).host.F) ((A u).piU : (I.rec7 l Z).host.E) → ∀ m : (H.lev0 u).fM w h, a • m = 0) → Formalism.L2.Herm.SymmetricCofactorCompatibility (I.rec7 l Z) H A ∧ Formalism.L2.Herm.SymmetricBaseCompatibility (I.rec7 l Z) H A ∧ Nonempty (Formalism.L2.Herm.SymmetricResidueFieldLevels (I.rec7 l Z) H A) ∧ ∃ X0 : Formalism.L2.Herm.SymmetricLevelZeroData (I.rec7 l Z) H A, ∀ u, (X0 u).piG = X.piG := by
  first | exact @GlobalTheory.Mem.Col2.TC.herm_rest_tied | exact GlobalTheory.Mem.Col2.TC.herm_rest_tied | (intros; apply GlobalTheory.Mem.Col2.TC.herm_rest_tied <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NontrivialWeylCoefficientSpace
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CoeffSpace

theorem nontrivial_VV : ∀ (K : Type) [Field K] (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n), Nontrivial (Formalism.L2.DIV.VV K lam) := by
  intro K _ ι _ n lam
  have hanti : ∀ τ, Antitone (lam τ).natW := fun τ i j hij =>
    Int.toNat_le_toNat (by have := (lam τ).anti hij; omega)
  have hmem : (∏ τ, Formalism.GradedWeylDivisibility.blockEmb K τ (Formalism.BasicNotions.extremal K n (lam τ))) ∈ Formalism.L2.DIV.VV K lam :=
    Submodule.subset_span ⟨fun τ => Formalism.BasicNotions.extremal K n (lam τ),
      fun τ => Formalism.GradedWeylDivisibility.hwMem K n n le_rfl _ (hanti τ), rfl⟩
  refine ⟨⟨⟨_, hmem⟩, 0, fun h => ?_⟩⟩
  have h0 : (∏ τ, Formalism.GradedWeylDivisibility.blockEmb K τ (Formalism.BasicNotions.extremal K n (lam τ))) = 0 := congrArg Subtype.val h
  rw [Finset.prod_eq_zero_iff] at h0
  obtain ⟨τ, _, h⟩ := h0
  have hinj : Function.Injective (fun v : Fin n × Fin n => (τ, v)) := fun a b hab => (Prod.mk.inj hab).2
  exact Formalism.GradedWeylDivisibility.hwNe K n n le_rfl _ (MvPolynomial.rename_injective _ hinj (h.trans (map_zero _).symm))

end GlobalTheory.CoeffSpace
end
end

