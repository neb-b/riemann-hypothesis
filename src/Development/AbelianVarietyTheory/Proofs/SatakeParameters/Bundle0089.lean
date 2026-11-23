module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0088
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0057
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.IsOrthCo
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob
public import Development.AbelianVarietyTheory.Counterexamples.UpperHalfSurvey.NonemptyAlgebra
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0067
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.LocalToGlobal.Columns.HeckeSp
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0056
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0002
public import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AcrisMemBetaAdicClosureAinfAdjoinBeta
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial GlobalTheory.Pst GlobalTheory.MemLoc GlobalTheory.Pst.StLat GlobalTheory.Pst.NoLog
open scoped Formalism.Per

namespace GlobalTheory.Pst.StLat

theorem acris_mem_clos : ∀ (l : ℕ) [Fact l.Prime] (j : Per.Acris l →+* Per.BdRp l), IsCrisP j → ∀ (ϖ : Per.Fl l),
  (∀ a : Per.Acris0 l, (a : Per.AinfP l) ∈ Sa ϖ) → (∀ n : ℕ, Per.FilP l n = Ideal.span {betaD ϖ ^ n}) →
  ∀ x : Per.Acris l, j x ∈ Clos (Sg ϖ) (betaD ϖ) := by
  intro l _ j hj ϖ hS hF x n
  obtain ⟨N, hN⟩ := hj.bdd n
  obtain ⟨s, z, rfl⟩ := (acris_basic l).2.2.1 x N
  obtain ⟨a, ha⟩ := hN z
  refine ⟨algebraMap (Per.AinfP l) (Per.BdRp l) ((s : Per.AinfP l) + algebraMap (Per.Ainf l) (Per.AinfP l) a),
    ⟨_, add_mem (hS s) (Subalgebra.algebraMap_mem _ a), rfl⟩, ?_⟩
  rw [← Ideal.mem_span_singleton, ← hF, GlobalTheory.RingIface.mem_filtration_iff_mem_kerTheta_pow, map_sub, map_add (f := _), map_add (f := _), map_mul, map_pow,
    map_natCast, hj.on0, ev_algebraMap, ev_algebraMap]
  rw [ha, map_add (f := _)]
  ring

end GlobalTheory.Pst.StLat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdelicPointLatticeFgOfFull
section
open NumberField IsDedekindDomain Formalism.L2.PairingIndexBounds.F
open scoped TensorProduct

namespace GlobalTheory.LatAdFG

theorem latAd_eq_globLat {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}
    (x : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (Lb : Submodule (𝓞 E) (Fin N → E)) :
    latAd x Lb = Formalism.UG.CS.globLat x Lb := by
  unfold latAd
  exact Submodule.span_eq (Formalism.UG.CS.globLat x Lb)

theorem latAd_fg_of_full : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ} (Lb : Submodule (𝓞 E) (Fin N → E)), Module.Finite (𝓞 E) Lb → Submodule.span E (Lb : Set (Fin N → E)) = ⊤ → ∀ (x : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)), (latAd x Lb).FG := by
  intro F E _ _ _ _ _ N Lb hfin hspan x
  rw [latAd_eq_globLat]
  exact (Formalism.UG.P.global_lattice_isLattice_holds F E (Fin N) Lb hfin hspan x).fg

end GlobalTheory.LatAdFG
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AinfAdjoinBetaImageDivBetaPow
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial GlobalTheory.Pst GlobalTheory.MemLoc GlobalTheory.Pst.StLat GlobalTheory.Pst.NoLog
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.Pst.StLat.BetaDiv

variable {l : ℕ} [Fact l.Prime]

theorem Sa_decomp (ϖ : Per.Fl l) (x : Per.AinfP l) (hx : x ∈ Sa ϖ) :
    ∃ a : Per.Ainf l, ∃ y ∈ Sa ϖ, x = algebraMap (Per.Ainf l) (Per.AinfP l) a + beta ϖ * y := by
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff] at hx
    exact ⟨0, 1, one_mem _, by rw [hx, map_zero, zero_add, mul_one]⟩
  | algebraMap r => exact ⟨r, 0, zero_mem _, by rw [mul_zero, add_zero]⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, u, hu, rfl⟩ := hx
    obtain ⟨b, v, hv, rfl⟩ := hy
    exact ⟨a + b, u + v, add_mem hu hv, by rw [map_add (f := _)]; ring⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a, u, hu, rfl⟩ := hx
    obtain ⟨b, v, hv, rfl⟩ := hy
    have hb : beta ϖ ∈ Sa ϖ := Algebra.subset_adjoin (Set.mem_singleton _)
    refine ⟨a * b, algebraMap (Per.Ainf l) (Per.AinfP l) a * v + u * algebraMap (Per.Ainf l) (Per.AinfP l) b
      + beta ϖ * u * v, ?_, by rw [map_mul]; ring⟩
    exact add_mem (add_mem (mul_mem (Subalgebra.algebraMap_mem _ _) hv)
      (mul_mem hu (Subalgebra.algebraMap_mem _ _))) (mul_mem (mul_mem hb hu) hv)

theorem Sa_cancel_beta (ϖ : Per.Fl l) (hϖ : ϖ.untilt = ((l : ℕ) : Per.OC l))
    (hk : Per.kerP l = Ideal.span {beta ϖ}) (c : Per.AinfP l) (hc : beta ϖ * c ∈ Sa ϖ) : c ∈ Sa ϖ := by
  obtain ⟨i1, i2, -, -, hK, -⟩ := GlobalTheory.AinfChecks.padicComplex l
  obtain ⟨hsurj, hker, hA, -, hdom, hinj, -⟩ := thetaP_facts l
  obtain ⟨hK1, hK2, -⟩ := hK ϖ hϖ
  obtain ⟨a, y, hy, hxy⟩ := Sa_decomp ϖ _ hc

  have ha : algebraMap (Per.Ainf l) (Per.AinfP l) a ∈ Per.kerP l := by
    rw [hk, Ideal.mem_span_singleton']
    exact ⟨c - y, by linear_combination hxy⟩
  have hθ : Per.θ l a = 0 := by
    rw [← hker, RingHom.mem_ker, hA] at ha
    exact Subtype.ext (by simpa using ha)
  have hmem : a ∈ RingHom.ker (Per.θ l) := hθ
  have hK1' : RingHom.ker (Per.θ l) = Ideal.span {((l : ℕ) : Per.Ainf l) - Per.tm ϖ} := hK1
  rw [hK1', Ideal.mem_span_singleton'] at hmem
  obtain ⟨d, hd⟩ := hmem

  have hne : ((l : ℕ) : Per.Ainf l) - Per.tm ϖ ≠ 0 := nonZeroDivisors.ne_zero hK2
  have hβ : beta ϖ ≠ 0 := by
    intro h0
    apply hne
    apply hinj
    have := l_mul_beta ϖ
    rw [h0, mul_zero] at this
    rw [map_sub, map_natCast, map_zero]
    linear_combination this
  have hlb := l_mul_beta ϖ
  have e : beta ϖ * c = beta ϖ * (y - ((l : ℕ) : Per.AinfP l) * algebraMap (Per.Ainf l) (Per.AinfP l) d) := by
    rw [hxy, ← hd, map_mul, map_sub, map_natCast]
    linear_combination (algebraMap (Per.Ainf l) (Per.AinfP l) d) * hlb
  rw [mul_left_cancel₀ hβ e]
  exact sub_mem hy (mul_mem (natCast_mem _ _) (Subalgebra.algebraMap_mem _ _))

theorem Sa_cancel_beta_pow (ϖ : Per.Fl l) (hϖ : ϖ.untilt = ((l : ℕ) : Per.OC l))
    (hk : Per.kerP l = Ideal.span {beta ϖ}) (i : ℕ) : ∀ c : Per.AinfP l, beta ϖ ^ i * c ∈ Sa ϖ → c ∈ Sa ϖ := by
  induction i with
  | zero => intro c hc; simpa using hc
  | succ i ih =>
    intro c hc
    refine Sa_cancel_beta ϖ hϖ hk c (ih _ ?_)
    rwa [← mul_assoc, ← pow_succ]

theorem Sg_div_betaD_pow : ∀ (l : ℕ) [Fact l.Prime] (ϖ : Per.Fl l), ϖ.untilt = ((l : ℕ) : Per.OC l) → Per.kerP l = Ideal.span {beta ϖ} →
  (∀ n : ℕ, Per.FilP l n = Ideal.span {betaD ϖ ^ n}) →
  ∀ s ∈ Sg ϖ, ∀ i : ℕ, betaD ϖ ^ i ∣ s → ∃ s' ∈ Sg ϖ, s = betaD ϖ ^ i * s' := by
  intro l _ ϖ hϖ hk hF s hs i hd
  obtain ⟨s₀, hs₀, rfl⟩ := Subring.mem_map.1 hs
  have hβ : beta ϖ ∈ Per.kerP l := by rw [hk]; exact Ideal.mem_span_singleton_self _
  have h2 : s₀ ∈ Per.kerP l ^ i := by
    obtain ⟨z, hz⟩ := hd
    have hb : betaD ϖ ^ i = algebraMap (Per.AinfP l) (Per.BdRp l) (beta ϖ ^ i) := by rw [map_pow, betaD]
    have h1 := congrArg (Per.ev l i) hz
    rw [hb, map_mul, GlobalTheory.MemLoc.ev_algebraMap, GlobalTheory.MemLoc.ev_algebraMap,
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.pow_mem_pow hβ i), zero_mul] at h1
    exact Ideal.Quotient.eq_zero_iff_mem.1 h1
  rw [hk, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at h2
  obtain ⟨c, hc⟩ := h2
  have hcS : c ∈ Sa ϖ := Sa_cancel_beta_pow ϖ hϖ hk i c (by rw [mul_comm, hc]; exact hs₀)
  refine ⟨algebraMap (Per.AinfP l) (Per.BdRp l) c, Subring.mem_map.2 ⟨c, hcS, rfl⟩, ?_⟩
  rw [← hc, map_mul, map_pow, mul_comm, betaD]

end GlobalTheory.Pst.StLat.BetaDiv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AntitoneZeroOneEqOfSumEq
section
open IsDedekindDomain NumberField

namespace GlobalTheory

theorem antitone_zero_one_eq_of_sum_eq {n : ℕ} (d e : Fin n → ℤ) (hd : Antitone d) (he : Antitone e)
    (hd0 : ∀ i, 0 ≤ d i) (hd1 : ∀ i, d i ≤ 1) (he0 : ∀ i, 0 ≤ e i) (he1 : ∀ i, e i ≤ 1)
    (hs : ∑ i, d i = ∑ i, e i) : d = e := by
  have key : (∀ i, d i ≤ e i) ∨ (∀ i, e i ≤ d i) := by
    by_contra h
    push Not at h
    obtain ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ := h
    have := hd0 j; have := hd1 i; have := he0 i; have := he1 j
    rcases le_total i j with hij | hij
    · have := he hij; omega
    · have := hd hij; omega
  rcases key with h | h
  · funext i
    exact (Finset.sum_eq_sum_iff_of_le (fun i _ => h i)).1 hs i (Finset.mem_univ i)
  · funext i
    exact ((Finset.sum_eq_sum_iff_of_le (fun i _ => h i)).1 hs.symm i (Finset.mem_univ i)).symm

section

variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)} {n : ℕ}

theorem glint_entry_mem_Ov {k : GL (Fin n) (v.adicCompletion F)}
    (hk : k ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.Ov F v)) (i j : Fin n) :
    (k : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j ∈ Formalism.UG.Ov F v := by
  obtain ⟨g, rfl⟩ := hk
  have : ((Formalism.UG.bc (n := Fin n) (Formalism.UG.Ov F v).subtype g : GL (Fin n) (v.adicCompletion F)) :
      Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j
      = (((g : Matrix (Fin n) (Fin n) (Formalism.UG.Ov F v)) i j : Formalism.UG.Ov F v) : v.adicCompletion F) := by
    simp [Formalism.UG.bc, Units.coe_map]
  rw [this]
  exact Subtype.property _

theorem mul_mul_entry_mem_Ov {A B C : Matrix (Fin n) (Fin n) (v.adicCompletion F)}
    (hA : ∀ i j, A i j ∈ Formalism.UG.Ov F v) (hB : ∀ i j, B i j ∈ Formalism.UG.Ov F v)
    (hC : ∀ i j, C i j ∈ Formalism.UG.Ov F v) (i j : Fin n) : (A * B * C) i j ∈ Formalism.UG.Ov F v := by
  simp only [Matrix.mul_apply]
  exact Subring.sum_mem _ fun l _ => Subring.mul_mem _
    (Subring.sum_mem _ fun m _ => Subring.mul_mem _ (hA _ _) (hB _ _)) (hC _ _)

theorem valued_det_le_one_of_entries {A : Matrix (Fin n) (Fin n) (v.adicCompletion F)}
    (hA : ∀ i j, A i j ∈ Formalism.UG.Ov F v) : Valued.v A.det ≤ 1 := by
  have : A.det ∈ Formalism.UG.Ov F v := by
    rw [Matrix.det_apply']
    exact Subring.sum_mem _ fun σ _ => Subring.mul_mem _ (intCast_mem _ _)
      (Subring.prod_mem _ fun i _ => hA _ _)
  exact this

theorem valued_det_eq_one_of_glint {k : GL (Fin n) (v.adicCompletion F)}
    (hk : k ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.Ov F v)) :
    Valued.v (k : Matrix (Fin n) (Fin n) (v.adicCompletion F)).det = 1 := by
  have h1 := valued_det_le_one_of_entries (glint_entry_mem_Ov hk)
  have h2 := valued_det_le_one_of_entries (glint_entry_mem_Ov (Subgroup.inv_mem _ hk))
  have h3 : Valued.v (k : Matrix (Fin n) (Fin n) (v.adicCompletion F)).det *
      Valued.v ((k⁻¹ : GL (Fin n) (v.adicCompletion F)) :
        Matrix (Fin n) (Fin n) (v.adicCompletion F)).det = 1 := by
    rw [← map_mul, ← Matrix.det_mul, Units.mul_inv, Matrix.det_one, map_one]
  refine le_antisymm h1 ?_
  calc (1 : WithZero (Multiplicative ℤ)) = _ := h3.symm
    _ ≤ _ * 1 := mul_le_mul_right h2 _
    _ = _ := mul_one _

theorem cartan_minuscule (k : ℕ) (ϖ ϖ' : v.adicCompletion F)
    (hϖ : Formalism.UG.IsUnifV F v ϖ) (hϖ' : Formalism.UG.IsUnifV F v ϖ') (a : GL (Fin n) (v.adicCompletion F))
    (h1 : ∀ i j, (a : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j ∈ Formalism.UG.Ov F v)
    (h2 : ∀ i j, ϖ' * ((a⁻¹ : GL (Fin n) (v.adicCompletion F)) :
      Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j ∈ Formalism.UG.Ov F v)
    (h3 : Valued.v (a : Matrix (Fin n) (Fin n) (v.adicCompletion F)).det = Valued.v ϖ' ^ k) :
    ∃ d : Fin n → ℤ, Antitone d ∧ (∀ i, 0 ≤ d i) ∧ (∀ i, d i ≤ 1) ∧ ∑ i, d i = k ∧
      ∃ k₁ ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.Ov F v), ∃ k₂ ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.Ov F v),
        ((k₁⁻¹ * a * k₂⁻¹ : GL (Fin n) (v.adicCompletion F)) :
          Matrix (Fin n) (Fin n) (v.adicCompletion F)) = Formalism.UG.diagPow F v ϖ d := by
  have hv : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hϖ
  have hv' : Valued.v ϖ' = WithZero.exp (-1 : ℤ) := hϖ'
  have hϖO : ϖ ∈ Formalism.UG.Ov F v := by
    show Valued.v ϖ ≤ 1
    rw [hv]
    exact (WithZero.exp_le_exp.mpr (by norm_num : (-1:ℤ) ≤ 0)).trans (le_of_eq WithZero.exp_zero)
  have hϖ0 : ϖ ≠ 0 := by
    rintro rfl
    rw [map_zero] at hv
    exact WithZero.exp_ne_zero hv.symm
  have hpow : ∀ m : ℤ, Valued.v (ϖ ^ m) = WithZero.exp (-m) := by
    intro m
    rw [map_zpow₀, hv, ← WithZero.exp_zsmul]
    simp
  have hsum : ∀ d : Fin n → ℤ, ∏ i, ϖ ^ d i = ϖ ^ ∑ i, d i := by
    intro d
    induction (Finset.univ : Finset (Fin n)) using Finset.induction_on with
    | empty => simp
    | insert x s hx ih => rw [Finset.prod_insert hx, Finset.sum_insert hx, ih, zpow_add₀ hϖ0]
  obtain ⟨d, hd, k₁, hk₁, k₂, hk₂, e⟩ := Formalism.UG.Final.CartanDecomp F v n ϖ hϖO hϖ a
  have hD : ((k₁⁻¹ * a * k₂⁻¹ : GL (Fin n) (v.adicCompletion F)) :
      Matrix (Fin n) (Fin n) (v.adicCompletion F)) = Formalism.UG.diagPow F v ϖ d := by
    simp only [Units.val_mul, e, mul_assoc, Units.inv_mul_cancel_left, Units.mul_inv, mul_one]
  have hDinv : ((k₂ * a⁻¹ * k₁ : GL (Fin n) (v.adicCompletion F)) :
      Matrix (Fin n) (Fin n) (v.adicCompletion F)) = Formalism.UG.diagPow F v ϖ (-d) := by
    have e1 : (k₂ * a⁻¹ * k₁ : GL (Fin n) (v.adicCompletion F)) = (k₁⁻¹ * a * k₂⁻¹)⁻¹ := by group
    rw [e1, Matrix.coe_units_inv, hD]
    apply Matrix.inv_eq_left_inv
    unfold Formalism.UG.diagPow
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    rw [← zpow_add₀ hϖ0]
    simp
  refine ⟨d, hd, fun i => ?_, fun i => ?_, ?_, k₁, hk₁, k₂, hk₂, hD⟩
  · have := mul_mul_entry_mem_Ov (glint_entry_mem_Ov (Subgroup.inv_mem _ hk₁)) h1
      (glint_entry_mem_Ov (Subgroup.inv_mem _ hk₂)) i i
    rw [← Units.val_mul, ← Units.val_mul, hD] at this
    have h : Valued.v (Formalism.UG.diagPow F v ϖ d i i) ≤ 1 := this
    rw [Formalism.UG.diagPow, Matrix.diagonal_apply_eq, hpow, ← WithZero.exp_zero,
      WithZero.exp_le_exp] at h
    omega
  · have := mul_mul_entry_mem_Ov (B := ϖ' • ((a⁻¹ : GL (Fin n) (v.adicCompletion F)) :
      Matrix (Fin n) (Fin n) (v.adicCompletion F))) (glint_entry_mem_Ov hk₂) h2
      (glint_entry_mem_Ov hk₁) i i
    rw [Matrix.mul_smul, Matrix.smul_mul, ← Units.val_mul, ← Units.val_mul, hDinv] at this
    have h : Valued.v (ϖ' * Formalism.UG.diagPow F v ϖ (-d) i i) ≤ 1 := this
    rw [Formalism.UG.diagPow, Matrix.diagonal_apply_eq, map_mul, hpow, hv', ← WithZero.exp_add,
      ← WithZero.exp_zero, WithZero.exp_le_exp] at h
    simp only [Pi.neg_apply] at h
    omega
  · rw [e, Matrix.det_mul, Matrix.det_mul, map_mul, map_mul, valued_det_eq_one_of_glint hk₁,
      valued_det_eq_one_of_glint hk₂, one_mul, mul_one, Formalism.UG.diagPow, Matrix.det_diagonal,
      hsum, hpow, hv', ← WithZero.exp_nsmul, WithZero.exp_inj] at h3
    simp only [nsmul_eq_mul] at h3
    omega

end

theorem glint_doubleCoset_of_minuscule : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (n k : ℕ) (ϖ ϖ' : v.adicCompletion F), Formalism.UG.IsUnifV F v ϖ → Formalism.UG.IsUnifV F v ϖ' → ∀ a a' : GL (Fin n) (v.adicCompletion F), (∀ i j, (a : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j ∈ Formalism.UG.Ov F v) → (∀ i j, ϖ * ((a⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j ∈ Formalism.UG.Ov F v) → Valued.v (a : Matrix (Fin n) (Fin n) (v.adicCompletion F)).det = Valued.v ϖ ^ k → (∀ i j, (a' : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j ∈ Formalism.UG.Ov F v) → (∀ i j, ϖ' * ((a'⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j ∈ Formalism.UG.Ov F v) → Valued.v (a' : Matrix (Fin n) (Fin n) (v.adicCompletion F)).det = Valued.v ϖ' ^ k → ∃ x ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.Ov F v), ∃ y ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.Ov F v), a' = x * a * y := by
  intro F _ _ v n k ϖ ϖ' hϖ hϖ' a a' h1 h2 h3 h1' h2' h3'
  obtain ⟨d, hd, hd0, hd1, hs, k₁, hk₁, k₂, hk₂, hD⟩ := cartan_minuscule k ϖ ϖ hϖ hϖ a h1 h2 h3
  obtain ⟨e, he, he0, he1, ht, l₁, hl₁, l₂, hl₂, hE⟩ :=
    cartan_minuscule k ϖ ϖ' hϖ hϖ' a' h1' h2' h3'
  obtain rfl : d = e := antitone_zero_one_eq_of_sum_eq d e hd he hd0 hd1 he0 he1 (hs.trans ht.symm)
  have h : k₁⁻¹ * a * k₂⁻¹ = l₁⁻¹ * a' * l₂⁻¹ := Units.ext (hD.trans hE.symm)
  refine ⟨l₁ * k₁⁻¹, Subgroup.mul_mem _ hl₁ (Subgroup.inv_mem _ hk₁), k₂⁻¹ * l₂,
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hk₂) hl₂, ?_⟩
  calc a' = l₁ * (l₁⁻¹ * a' * l₂⁻¹) * l₂ := by group
    _ = l₁ * (k₁⁻¹ * a * k₂⁻¹) * l₂ := by rw [h]
    _ = _ := by group

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.BetaImageDeRhamPlusDvdOfLAdicResidues
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial GlobalTheory.Pst GlobalTheory.MemLoc GlobalTheory.Pst.StLat GlobalTheory.Pst.NoLog
open scoped Formalism.Per

namespace GlobalTheory.Pst.StLat

theorem betaD_dvd_of_res : ∀ (l : ℕ) [Fact l.Prime] (ϖ : Per.Fl l), Per.kerP l = Ideal.span {beta ϖ} →
  (∀ n : ℕ, Per.FilP l n = Ideal.span {betaD ϖ ^ n}) →
  ∀ y : Per.BdRp l, (∀ k : ℕ, ∃ s ∈ Sg ϖ, betaD ϖ ∣ y - ((l : ℕ) : Per.BdRp l) ^ k * s) → betaD ϖ ∣ y := by
  intro l _ ϖ hk hF y hy
  obtain ⟨-, hker, hA, hD, -⟩ := GlobalTheory.MemLoc.thetaP_facts l
  have hb0 : Per.θP l (beta ϖ) = 0 := by
    rw [← RingHom.mem_ker, hker, hk]; exact Ideal.mem_span_singleton_self _
  have hb : Per.θD l (betaD ϖ) = 0 := by rw [betaD, hD, hb0]
  have hS : ∀ a ∈ Sa ϖ, Per.θP l a ∈ 𝓞_ℂ_[l] := by
    intro a ha
    change a ∈ Algebra.adjoin _ _ at ha
    induction ha using Algebra.adjoin_induction with
    | mem x hx => rw [Set.mem_singleton_iff.1 hx, hb0]; exact zero_mem _
    | algebraMap r => rw [hA]; exact (Per.θ l r).2
    | add x z _ _ hx hz => rw [map_add (Per.θP l)]; exact add_mem hx hz
    | mul x z _ _ hx hz => rw [map_mul]; exact mul_mem hx hz
  have hs : ∀ s ∈ Sg ϖ, ‖Per.θD l s‖ ≤ 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [hD]
    exact (GlobalTheory.RingBasics.mem_OC _).1 (hS a ha)
  have h0 : Per.θD l y = 0 := by
    have hle : ∀ k : ℕ, ‖Per.θD l y‖ ≤ ‖((l : ℕ) : ℂ_[l])‖ ^ k := by
      intro k
      obtain ⟨s, hsS, c, hc⟩ := hy k
      have h1 := congrArg (Per.θD l) hc
      rw [map_sub, map_mul, map_mul, hb, zero_mul, sub_eq_zero, map_pow, map_natCast] at h1
      rw [h1, norm_mul, norm_pow]
      exact mul_le_of_le_one_right (pow_nonneg (norm_nonneg _) _) (hs s hsS)
    exact norm_le_zero_iff.1 (ge_of_tendsto' (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _)
      (GlobalTheory.RingBasics.norm_p_lt (p := l))) hle)
  have hmem : y ∈ Per.FilP l 1 := ((_root_.GlobalTheory.MemLoc.thetaD_props l).2.1 y).1 h0
  rw [hF 1, pow_one] at hmem
  exact Ideal.mem_span_singleton.1 hmem

end GlobalTheory.Pst.StLat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ClosEqZeroOfMulMem
section
open GlobalTheory.Pst.StLat

namespace GlobalTheory.Pst.StLat

theorem clos_eq_zero_of_mul_mem {R : Type} [CommRing R] [IsDomain R] (p : ℕ) (hp : p.Prime)
    (hpu : IsUnit ((p : ℕ) : R)) (π : R) (hπ : π ≠ 0)
    (hsep : ∀ x : R, (∀ n : ℕ, π ^ n ∣ x) → x = 0) (S : Subring R)
    (hdiv : ∀ s ∈ S, ∀ i : ℕ, π ^ i ∣ s → ∃ s' ∈ S, s = π ^ i * s')
    (hres : ∀ y : R, (∀ k : ℕ, ∃ s ∈ S, π ∣ y - ((p : ℕ) : R) ^ k * s) → π ∣ y)
    (u : R) (hlog : ∀ m : ℕ, 1 ≤ m → ∃ s ∈ S, ∃ e : R, (e = 1 ∨ e = -1) ∧
      π ^ (2 * p ^ m) ∣ ((p : ℕ) : R) * (((p : ℕ) : R) ^ (m - 1) * u - s) - e * π ^ (p ^ m))
    (a : R) (r : ℕ) (ha : a ∈ Clos S π) (hau : ((p : ℕ) : R) ^ r * a * u ∈ Clos S π) : a = 0 := by
  obtain ⟨q, hPq⟩ : ∃ q : R, ((p : ℕ) : R) * q = 1 := ⟨((hpu.unit⁻¹ : Rˣ) : R), hpu.mul_val_inv⟩
  have hSC : ∀ s ∈ S, s ∈ Clos S π := fun s hs n => ⟨s, hs, by simp⟩
  have hPC : ((p : ℕ) : R) ∈ Clos S π := natCast_mem _ _

  have stepD : ∀ b ∈ Clos S π, ∀ r' : ℕ, ((p : ℕ) : R) ^ r' * b * u ∈ Clos S π →
      ∃ b' ∈ Clos S π, ((p : ℕ) : R) * b' = b := by
    intro b hb r' hbu
    refine ⟨q * b, ?_, by rw [← mul_assoc, hPq, one_mul]⟩
    intro n
    obtain ⟨s, hs, e, he, w, hw⟩ := hlog (r' + n + 1) (by omega)
    have hm : r' + n + 1 - 1 = r' + n := by omega
    rw [hm] at hw
    set M := p ^ (r' + n + 1) with hMdef
    have hnM : n ≤ M := by
      have h1 : r' + n + 1 < p ^ (r' + n + 1) := Nat.lt_pow_self hp.one_lt
      omega
    have h2M : π ^ (2 * M) = π ^ M * π ^ M := by rw [two_mul, pow_add]
    rw [h2M] at hw
    have hx : b * (((p : ℕ) : R) ^ (r' + n) * u - s) ∈ Clos S π := by
      have : b * (((p : ℕ) : R) ^ (r' + n) * u - s) =
          ((p : ℕ) : R) ^ n * (((p : ℕ) : R) ^ r' * b * u) - b * s := by ring
      rw [this]
      exact sub_mem (mul_mem (pow_mem hPC _) hbu) (mul_mem hb (hSC s hs))
    obtain ⟨s₁, hs₁, c, hc⟩ := hx (2 * M)
    rw [h2M] at hc
    have hs1eq : s₁ = π ^ M * (q * b * e + π ^ M * (q * b * w - c)) := by
      linear_combination (-1 : R) * hc + (q * b) * hw - (b * (((p : ℕ) : R) ^ (r' + n) * u - s)) * hPq
    obtain ⟨s₂, hs₂S, hs₂⟩ := hdiv s₁ hs₁ M ⟨_, hs1eq⟩
    have hcan : q * b * e - s₂ = π ^ M * (c - q * b * w) := by
      apply mul_left_cancel₀ (pow_ne_zero M hπ)
      linear_combination hs₂ - hs1eq
    have he2 : e * e = 1 := by rcases he with rfl | rfl <;> ring
    have heS : e * s₂ ∈ S := by
      rcases he with rfl | rfl
      · simpa using hs₂S
      · simpa using neg_mem hs₂S
    refine ⟨e * s₂, heS, dvd_trans (pow_dvd_pow π hnM) ⟨e * (c - q * b * w), ?_⟩⟩
    linear_combination e * hcan - (q * b) * he2

  have iter : ∀ k : ℕ, ∃ b ∈ Clos S π, ((p : ℕ) : R) ^ k * b = a ∧
      ((p : ℕ) : R) ^ (r + k) * b * u ∈ Clos S π := by
    intro k
    induction k with
    | zero => exact ⟨a, ha, by simp, by simpa using hau⟩
    | succ k ih =>
      obtain ⟨b, hb, hbk, hbu⟩ := ih
      obtain ⟨b', hb', hPb'⟩ := stepD b hb (r + k) hbu
      refine ⟨b', hb', ?_, ?_⟩
      · rw [pow_succ, mul_assoc, hPb', hbk]
      · have : ((p : ℕ) : R) ^ (r + (k + 1)) * b' * u =
            ((p : ℕ) : R) ^ (r + k) * (((p : ℕ) : R) * b') * u := by ring
        rw [this, hPb']
        exact hbu

  by_contra ha0
  classical
  have hex : ∃ n : ℕ, ¬ π ^ n ∣ a := by
    by_contra h
    push_neg at h
    exact ha0 (hsep a h)
  have hn0 : Nat.find hex ≠ 0 := by
    intro h0
    have := Nat.find_spec hex
    rw [h0, pow_zero] at this
    exact this (one_dvd a)
  set i := Nat.find hex - 1 with hidef
  have hi1 : i + 1 = Nat.find hex := by omega
  have hia : π ^ i ∣ a := by
    have := Nat.find_min hex (show i < Nat.find hex by omega)
    simpa using this
  obtain ⟨a₁, ha₁⟩ := hia
  have hna₁ : ¬ π ∣ a₁ := by
    rintro ⟨t, ht⟩
    apply Nat.find_spec hex
    rw [← hi1]
    exact ⟨t, by rw [ha₁, ht, pow_succ]; ring⟩
  apply hna₁
  apply hres a₁
  intro k
  obtain ⟨b, hb, hbk, -⟩ := iter k
  obtain ⟨s, hs, hbs⟩ := hb (i + 1)
  have hib : π ^ i ∣ b := ⟨q ^ k * a₁, by
    have : b = q ^ k * (((p : ℕ) : R) ^ k * b) := by
      rw [← mul_assoc, ← mul_pow, mul_comm q, hPq, one_pow, one_mul]
    rw [this, hbk, ha₁]; ring⟩
  have his : π ^ i ∣ s := by
    have h1 : π ^ i ∣ b - s := dvd_trans (pow_dvd_pow π (Nat.le_succ i)) hbs
    have := dvd_sub hib h1
    simpa using this
  obtain ⟨s', hs'S, hs'⟩ := hdiv s hs i his
  refine ⟨s', hs'S, ?_⟩
  rw [← mul_dvd_mul_iff_left (pow_ne_zero i hπ), ← pow_succ]
  have : π ^ i * (a₁ - ((p : ℕ) : R) ^ k * s') = ((p : ℕ) : R) ^ k * (b - s) := by
    rw [mul_sub, ← ha₁, ← hbk, hs']; ring
  rw [this]
  exact dvd_mul_of_dvd_right hbs _

end GlobalTheory.Pst.StLat
end

