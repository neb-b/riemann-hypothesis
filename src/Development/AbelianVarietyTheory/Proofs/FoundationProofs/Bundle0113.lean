module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0095
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0063
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0092
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0104
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0073
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0081
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0070
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0083
public import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
public import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0009
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0100
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0102
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0094
public import Development.AbelianVarietyTheory.Definitions.Foundations.CyclotomicDvdExpandOfCoprime

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.AlgebraMapZpInjective
section
noncomputable section

open GlobalTheory.K5 GlobalTheory.Glue

namespace GlobalTheory.GeoFix

variable {p : ℕ} [hp : Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

def InR (ψ : O0 p →+* Ω) (y : Ω) : Prop :=
  ∃ (d : ℕ) (e : Fin d → Ω) (b : Fin d → O0 p),
    (∀ t, IsInt (p := p) (e t) ∧ IsAlgZp (p := p) (e t)) ∧
    y = ∑ t, e t * ψ (b t)

variable (p Ω) in
abbrev zpAlg : Algebra ℤ_[p] Ω := ((algebraMap (O0 p) Ω).comp (algebraMap ℤ_[p] (O0 p))).toAlgebra

theorem isAlgZp_iff (x : Ω) : IsAlgZp (p := p) x ↔ @IsAlgebraic ℤ_[p] Ω _ _ (zpAlg p Ω) x := by
  letI := zpAlg p Ω
  haveI : IsScalarTower ℤ_[p] (O0 p) Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  unfold IsAlgZp IsAlgebraic
  simp only [Polynomial.aeval_map_algebraMap]

theorem isAlgZp_mul {x y : Ω} (hx : IsAlgZp (p := p) x) (hy : IsAlgZp (p := p) y) :
    IsAlgZp (p := p) (x * y) := by
  letI := zpAlg p Ω
  rw [isAlgZp_iff] at hx hy ⊢
  exact hx.mul hy

theorem isAlgZp_one : IsAlgZp (p := p) (1 : Ω) := by
  letI := zpAlg p Ω
  rw [isAlgZp_iff]
  exact isAlgebraic_one

theorem isInt_psi {T : Tower p Ω} {n : ℕ} {ψ : O0 p →+* Ω} (h : IsReb T n ψ) (b : O0 p) :
    IsInt (p := p) (ψ b) := by
  have hq : IsIntegral (O0 p) (T.qq n) := by
    refine ⟨Polynomial.X ^ (p ^ n) - Polynomial.C (qO p),
      Polynomial.monic_X_pow_sub_C _ (pow_ne_zero _ hp.out.ne_zero), ?_⟩
    rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, Basic.qq_pow, sub_self]
  have hb : ψ b ∈ ψ.range := ⟨b, rfl⟩
  rw [h.rng] at hb
  exact adjoin_le_integralClosure hq hb

theorem inR_zero (ψ : O0 p →+* Ω) : InR ψ 0 :=
  ⟨0, Fin.elim0, Fin.elim0, fun t => t.elim0, by simp⟩

theorem inR_psi (ψ : O0 p →+* Ω) (b : O0 p) : InR ψ (ψ b) :=
  ⟨1, fun _ => 1, fun _ => b, fun _ => ⟨isIntegral_one, isAlgZp_one⟩, by simp⟩

theorem inR_add {ψ : O0 p →+* Ω} {x y : Ω} (hx : InR ψ x) (hy : InR ψ y) : InR ψ (x + y) := by
  obtain ⟨d, e, b, he, rfl⟩ := hx
  obtain ⟨d', e', b', he', rfl⟩ := hy
  refine ⟨d + d', Fin.append e e', Fin.append b b', fun t => ?_, ?_⟩
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) t
    · simpa using he i
    · simpa using he' i
  · rw [Fin.sum_univ_add]
    simp

theorem inR_sum {ψ : O0 p →+* Ω} {ι : Type*} (s : Finset ι) (f : ι → Ω) (hf : ∀ i ∈ s, InR ψ (f i)) :
    InR ψ (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using inR_zero ψ
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact inR_add (hf a (Finset.mem_insert_self a s)) (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

theorem inR_mul {ψ : O0 p →+* Ω} {x y : Ω} (hx : InR ψ x) (hy : InR ψ y) : InR ψ (x * y) := by
  obtain ⟨d, e, b, he, rfl⟩ := hx
  obtain ⟨d', e', b', he', rfl⟩ := hy
  rw [Finset.sum_mul_sum]
  refine inR_sum _ _ fun i _ => inR_sum _ _ fun j _ => ?_
  refine ⟨1, fun _ => e i * e' j, fun _ => b i * b' j,
    fun _ => ⟨IsIntegral.mul (he i).1 (he' j).1, isAlgZp_mul (he i).2 (he' j).2⟩, ?_⟩
  simp only [Finset.univ_unique, Finset.sum_singleton, map_mul]
  ring

theorem inR_neg {ψ : O0 p →+* Ω} {x : Ω} (hx : InR ψ x) : InR ψ (-x) := by
  have := inR_mul (inR_psi ψ (-1)) hx
  simpa using this

theorem InR.isInt {T : Tower p Ω} {n : ℕ} {ψ : O0 p →+* Ω} (h : IsReb T n ψ) {x : Ω} (hx : InR ψ x) :
    IsInt (p := p) x := by
  obtain ⟨d, e, b, he, rfl⟩ := hx
  exact IsIntegral.sum _ fun t _ => IsIntegral.mul (he t).1 (isInt_psi h (b t))

theorem algebraMap_zp_injective : Function.Injective (algebraMap ℤ_[p] (O0 p)) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro m hm
  by_contra h0
  rw [PadicInt.unitCoeff_spec h0, map_mul, map_pow, map_natCast] at hm
  have hu : algebraMap ℤ_[p] (O0 p) ((PadicInt.unitCoeff h0 : ℤ_[p])) ≠ 0 :=
    ((Units.isUnit (PadicInt.unitCoeff h0)).map (algebraMap ℤ_[p] (O0 p))).ne_zero
  have hp0 : (p : O0 p) ^ m.valuation ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hp.out.ne_zero)
  exact mul_ne_zero hu hp0 hm

theorem exists_inR_of_isAlgZp (hc : IsClo p Ω) {T : Tower p Ω} {n : ℕ} {ψ : O0 p →+* Ω} (h : IsReb T n ψ) {x : Ω}
    (hx : IsAlgZp (p := p) x) : ∃ D : O0 p, D ≠ 0 ∧ InR ψ (x * ψ D) := by
  letI := zpAlg p Ω
  haveI : IsScalarTower ℤ_[p] (O0 p) Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hx' := (isAlgZp_iff x).1 hx
  obtain ⟨y, hy0, hyi⟩ := hx'.exists_integral_multiple
  set c : O0 p := algebraMap ℤ_[p] (O0 p) y with hcdef
  have hmem : algebraMap (O0 p) Ω c ∈ ψ.range := by
    rw [h.rng]
    exact Subalgebra.algebraMap_mem _ c
  obtain ⟨D, hD⟩ := hmem
  have hc0 : c ≠ 0 := fun h0 => hy0 (algebraMap_zp_injective (by rw [← hcdef, h0, map_zero]))
  refine ⟨D, ?_, 1, fun _ => y • x, fun _ => 1, fun _ => ⟨?_, ?_⟩, ?_⟩
  · rintro rfl
    rw [map_zero] at hD
    exact hc0 (hc.inj (by rw [← hD, map_zero]))
  · exact hyi.tower_top
  · rw [isAlgZp_iff, Algebra.smul_def]
    exact (isAlgebraic_algebraMap y).mul hx'
  · simp only [Finset.univ_unique, Finset.sum_singleton, map_one, mul_one]
    rw [hD, Algebra.smul_def, IsScalarTower.algebraMap_apply ℤ_[p] (O0 p) Ω, mul_comm]

theorem algebraMap_zp_eq (m : ℤ_[p]) :
    algebraMap ℤ_[p] (O0 p) m = algebraMap (Lau p) (O0 p) (HahnSeries.C m) := by
  have hH := (o0_isAdicComplete_span_p p).toIsHausdorff
  refine sub_eq_zero.1 (hH.haus' _ fun K => ?_)
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  have hs := PadicInt.appr_spec K m
  rw [Ideal.mem_span_singleton] at hs
  obtain ⟨u, hu⟩ := hs
  have hm : m = (m.appr K : ℤ_[p]) + (p : ℤ_[p]) ^ K * u := by rw [← hu]; ring
  refine ⟨algebraMap ℤ_[p] (O0 p) u - algebraMap (Lau p) (O0 p) (HahnSeries.C u), ?_⟩
  conv_lhs => rw [hm]
  simp only [map_add (f := _), map_mul, map_pow, map_natCast]
  ring

theorem isAlgZp_zp (m : ℤ_[p]) : IsAlgZp (p := p) (zp Ω m) := by
  refine ⟨Polynomial.X - Polynomial.C m, Polynomial.X_sub_C_ne_zero m, ?_⟩
  rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, map_sub, Polynomial.aeval_X, Polynomial.aeval_C,
    zp, algebraMap_zp_eq, HahnSeries.C_apply, sub_self]

theorem isAlgZp_add {x y : Ω} (hx : IsAlgZp (p := p) x) (hy : IsAlgZp (p := p) y) :
    IsAlgZp (p := p) (x + y) := by
  letI := zpAlg p Ω
  rw [isAlgZp_iff] at hx hy ⊢
  exact hx.add hy

end GlobalTheory.GeoFix
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.AlgebraicTowerKhatPadicSmulTorsionFreeStatement
section
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraicTowerKhat_padic_smul_torsionFree : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime], [IsAlgClosed Ω] → ∀ (c : ℤ_[l]) (x : X.Khat l), c ≠ 0 → c • x = 0 → x = 0 := by
  first | exact @GlobalTheory.KZ.H3.khat_torsionFree | exact GlobalTheory.KZ.H3.khat_torsionFree | (intros; apply GlobalTheory.KZ.H3.khat_torsionFree <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.AlmostPurityMovesIntegersOfNeOne
section
open GlobalTheory.AlmostEt
open scoped NNReal

namespace GlobalTheory.AlmostEt

theorem moves_of_ne_one : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (p : ℕ), p.Prime → 0 < v (p : L) → v (p : L) < 1 → ∀ (G : Type) [Group G] [MulSemiringAction G L] [Finite G] [FaithfulSMul G L], (∀ (g : G) (x : L), v (g • x) = v x) → ∀ ζ : L, IsPrimitiveRoot ζ p → (∀ g : G, g • ζ = ζ) → ApproxRoot p v (Fix L (⊤ : Subgroup G)) → ∀ σ : G, σ ≠ 1 → Moves v ⊤ σ := by
  intro L _ v p hp hp0 hp1 G _ _ _ _ hinv ζ hζ hζfix hroot σ hσ
  obtain ⟨N, hNn, hNmem, i, hi, hNi⟩ := _root_.GlobalTheory.AlmostEt.exists_normal_not_moves_uniform L v G hinv
  by_contra hmov
  have hσN : σ ∈ N := (hNmem σ).2 hmov
  have hfixN : ∀ τ ∈ N, ∀ x ∈ Fix L N, τ • x = x := fun τ hτ x hx => hx ⟨τ, hτ⟩
  have hdesc : ∀ τ : G, τ ∉ N → Moves v (Fix L N) τ := fun τ hτ =>
    _root_.GlobalTheory.AlmostEt.moves_fix_of_moves L v G hinv N i hi hNi τ (by_contra fun h => hτ ((hNmem τ).2 h))
  have hsep : AlmostSep v N := _root_.GlobalTheory.AlmostEt.almostSep_of_moves L v G hinv N hNn inferInstance hdesc
  have hF : ApproxRoot p v (Fix L N) := _root_.GlobalTheory.AlmostEt.approxRoot_fix_of_almostSep L v p hp hp0 hp1 G hinv N inferInstance hsep hroot
  have hpg : IsPGroup p N := by
    intro τ
    set n := orderOf (τ : G) with hn
    have hn0 : n ≠ 0 := (orderOf_pos (τ : G)).ne'
    set k := n.factorization p
    refine ⟨k, ?_⟩
    have hcop : Nat.Coprime (n / p ^ k) p := (Nat.coprime_ordCompl hp hn0).symm
    have hτ' : ((τ : G) ^ (p ^ k)) ∈ N := N.pow_mem τ.2 _
    by_contra hne
    have hne' : (τ : G) ^ (p ^ k) ≠ 1 := by
      intro h; apply hne; ext; simpa using h
    have hl : ((τ : G) ^ (p ^ k)) ^ (n / p ^ k) = 1 := by
      rw [← pow_mul, Nat.mul_div_cancel' (Nat.ordProj_dvd n p), hn, pow_orderOf_eq_one]
    obtain ⟨y, hy⟩ : ∃ y : L, ((τ : G) ^ (p ^ k)) • y ≠ y := by
      by_contra h
      push_neg at h
      exact hne' (eq_of_smul_eq_smul (α := L) (fun y => by rw [h y, one_smul]))
    exact (hNmem _).1 hτ' (_root_.GlobalTheory.AlmostEt.moves_top_of_coprime_order L v p hp (Fix L N) hF hp0 hp1 G hinv _ (hfixN _ hτ') _ hcop hl ⟨y, hy⟩)
  haveI : Nontrivial N := ⟨⟨⟨σ, hσN⟩, 1, fun h => hσ (congrArg Subtype.val h)⟩⟩
  haveI : FaithfulSMul N L := ⟨fun {a b} h => Subtype.ext (eq_of_smul_eq_smul (α := L) h)⟩
  obtain ⟨σ₀, α, hα0, hσα, hαp⟩ := _root_.GlobalTheory.AlmostEt.exists_lagrange_resolvent L p hp N hpg ζ hζ (fun g => hζfix g)
  have hαF : α ^ p ∈ Fix L N := fun g => hαp g
  exact (hNmem _).1 σ₀.2 (_root_.GlobalTheory.AlmostEt.kummer_moves L v p hp (Fix L N) hF hp0 hp1 G (σ₀ : G) (hfixN _ σ₀.2) ζ α hζ hα0 hαF hσα)

end GlobalTheory.AlmostEt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ApproxPthRootFixedFieldCyclotomicTower
section
open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal

namespace GlobalTheory.K5.TopRoots

theorem approxRoot_fix_tower : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω],
    p ≠ 2 → IsClo p Ω → ∀ (T : Tower p Ω) (v : Valuation Ω ℝ≥0),
    (∀ x : Ω, v x ≤ 1 ↔ IsInt (p := p) x) →
    0 < v (p : Ω) → v (p : Ω) < 1 → ApproxRoot p v (Fix Ω (⨅ n, Gn T n)) := by
  intro p _ Ω _ _ hp2 hclo T v hv _ hp1
  classical
  have hpp : p.Prime := Fact.out
  let S : Set Ω := Set.range T.ζ ∪ Set.range T.qq
  let B := Algebra.adjoin (O0 p) S
  let F := Fix Ω (⨅ n, Gn T n)

  have hBle : B ≤ integralClosure (O0 p) Ω := by
    rw [Algebra.adjoin_le_iff]
    rintro y (⟨n, rfl⟩ | ⟨n, rfl⟩)
    · refine IsIntegral.of_pow (pow_pos hpp.pos n) ?_
      rw [(T.prim n).pow_eq_one]; exact isIntegral_one
    · refine IsIntegral.of_pow (pow_pos hpp.pos n) ?_
      rw [Basic.qq_pow]; exact isIntegral_algebraMap
  have hBint : ∀ x ∈ B, v x ≤ 1 := fun x hx => (hv x).2 (hBle hx)

  have hBF : ∀ x ∈ B, x ∈ F := by
    intro x hx g
    have hg : (g : Gal p Ω) ∈ ⨅ n, Gn T n := g.2
    rw [Subgroup.mem_iInf] at hg
    have hle : B ≤ AlgHom.equalizer (g : Gal p Ω).toAlgHom (AlgHom.id (O0 p) Ω) := by
      rw [Algebra.adjoin_le_iff]
      rintro y (⟨n, rfl⟩ | ⟨n, rfl⟩)
      · exact ((Basic.mem_gn T n _).1 (hg n)).1
      · exact ((Basic.mem_gn T n _).1 (hg n)).2
    have := hle hx
    rw [AlgHom.mem_equalizer] at this
    exact this

  set θ := v (T.ζ 1 - 1) with hθ
  have hz1 := GlobalTheory.T.valuation_tower_zeta_sub_one p Ω hp2 T v hp1 1 le_rfl
  have hθ1 : θ < 1 := hz1.1
  let good : Ω → Prop := fun x => ∃ w ∈ F, v (x - w ^ p) ≤ θ * v x

  have hgoodB : ∀ x ∈ B, v (p : Ω) ≤ θ * v x → good x := by
    intro x hx hvx
    obtain ⟨y, hy, z, hz, e⟩ := _root_.GlobalTheory.K5.frob_surj_adjoin_tower p Ω T x hx
    refine ⟨y, hBF y hy, ?_⟩
    have : x - y ^ p = (p : Ω) * z := by rw [e]; ring
    rw [this, map_mul]
    calc v (p : Ω) * v z ≤ v (p : Ω) * 1 := mul_le_mul_of_nonneg_left (hBint z hz) zero_le
      _ = v (p : Ω) := mul_one _
      _ ≤ θ * v x := hvx

  have hunit : ∀ u ∈ B, ∀ u' ∈ B, u * u' = 1 → good u := by
    intro u hu u' hu' e
    have hvu : v u = 1 := by
      have h1 := hBint u hu
      have h2 := hBint u' hu'
      have h3 : v u * v u' = 1 := by rw [← map_mul, e, map_one]
      by_contra hne
      have hlt : v u < 1 := lt_of_le_of_ne h1 hne
      have : v u * v u' < 1 := by
        calc v u * v u' ≤ v u * 1 := mul_le_mul_of_nonneg_left h2 zero_le
          _ = v u := mul_one _
          _ < 1 := hlt
      exact absurd h3 (ne_of_lt this)
    refine hgoodB u hu ?_
    rw [hvu, mul_one]
    calc v (p : Ω) ≤ θ * v (T.ζ 1 - 1) := hz1.2
      _ ≤ θ * 1 := mul_le_mul_of_nonneg_left hθ1.le zero_le
      _ = θ := mul_one _

  have hzeta : ∀ n, 1 ≤ n → good (T.ζ n - 1) := by
    intro n hn
    have hmem : T.ζ n - 1 ∈ B :=
      Subalgebra.sub_mem _ (Algebra.subset_adjoin (Or.inl ⟨n, rfl⟩)) (Subalgebra.one_mem _)
    exact hgoodB _ hmem (GlobalTheory.T.valuation_tower_zeta_sub_one p Ω hp2 T v hp1 n hn).2

  have hB : ∀ b ∈ B, good b := by
    intro b hb
    by_cases hb0 : b = 0
    · refine ⟨0, F.zero_mem, ?_⟩
      rw [hb0, zero_pow hpp.ne_zero, sub_zero, map_zero]; exact zero_le
    obtain ⟨n, k, hn, u, hu, u', hu', e, rfl⟩ := _root_.GlobalTheory.K5.UnitPow.eq_unit_mul_pow p Ω hclo T b hb hb0
    have h1 := hunit u hu u' hu' e
    have h2 := (_root_.GlobalTheory.AlmostEt.approxRoot_closed Ω v p F θ hθ1 _ _ (hzeta n hn) (hzeta n hn)).2.2 k
    exact (_root_.GlobalTheory.AlmostEt.approxRoot_closed Ω v p F θ hθ1 _ _ h1 h2).1

  refine ⟨θ, hθ1, fun x hx => ?_⟩
  haveI : CharZero Ω := Basic.charZero_of_isClo hclo
  haveI : IsAlgClosed Ω := hclo.clo
  haveI : Algebra.IsAlgebraic (O0 p) Ω := hclo.alg
  have hfix : ∀ g : Ω ≃ₐ[O0 p] Ω, (∀ s ∈ S, g s = s) → g x = x := by
    intro g hg
    have hgm : g ∈ ⨅ n, Gn T n := by
      rw [Subgroup.mem_iInf]
      intro n
      exact (Basic.mem_gn T n g).2
        ⟨hg _ (Or.inl ⟨n, rfl⟩), hg _ (Or.inr ⟨n, rfl⟩)⟩
    exact hx ⟨g, hgm⟩
  obtain ⟨b, hb, c, hc, hc0, rfl⟩ := _root_.GlobalTheory.mem_adjoin_div_of_fixed (O0 p) Ω hclo.inj S x hfix
  exact (_root_.GlobalTheory.AlmostEt.approxRoot_closed Ω v p F θ hθ1 _ _ (hB b hb) (hB c hc)).2.1 hc0

end GlobalTheory.K5.TopRoots
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.BettiKummerRelationPadicSmulStatement
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.BettiB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bettiKummerRelationPadic_smul : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (N l : ℕ) [Fact l.Prime] (r : ℤ_[l]) (b : X.Fn l) (c : Gam N l → MvPolynomial (Fin 2) ℤ_[l]), BtZ X N l b c → BtZ X N l (r • b) (r • c) := by
  first | exact @GlobalTheory.KZ.BettiB.btZ_smul | exact GlobalTheory.KZ.BettiB.btZ_smul | (intros; apply GlobalTheory.KZ.BettiB.btZ_smul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmpProps
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem cmp_props :
    (∀ f : ℍ → ℂ, GlobalTheory.FN.cmp 1 f = f) ∧ (∀ (g h : GQ) (f : ℍ → ℂ), GlobalTheory.FN.cmp (g * h) f = GlobalTheory.FN.cmp h (GlobalTheory.FN.cmp g f)) ∧
      (∀ (γ : SL(2, ℤ)) (f : ℍ → ℂ), GlobalTheory.FN.cmp (ofSL γ) f = fun τ => f (γ • τ)) ∧
        ∀ (g : GQ) (f : ℍ → ℂ), ∀ z ∈ Hs, up (GlobalTheory.FN.cmp g f) z = up f (mob g z) := by
  obtain ⟨hH, hmul, hone, hsl, -, -⟩ := _root_.GlobalTheory.FN.mob_props
  have hup : ∀ (f : ℍ → ℂ) (z : ℂ) (hz : 0 < z.im), up f z = f ⟨z, hz⟩ := by
    intro f z hz
    simp only [up, UpperHalfPlane.ofComplex_apply_of_im_pos hz]
  have hupH : ∀ (f : ℍ → ℂ) (τ : ℍ), up f τ = f τ := by
    intro f τ
    simp only [up, UpperHalfPlane.ofComplex_apply]
  have h4 : ∀ (g : GQ) (f : ℍ → ℂ), ∀ z ∈ Hs, up (GlobalTheory.FN.cmp g f) z = up f (mob g z) := by
    intro g f z hz
    rw [hup _ z hz]
    rfl
  refine ⟨?_, ?_, ?_, h4⟩
  · intro f
    funext τ
    simp only [cmp, hone, hupH]
  · intro g h f
    funext τ
    have hτ : (τ : ℂ) ∈ Hs := τ.im_pos
    show up f (mob (g * h) τ) = up (cmp g f) (mob h τ)
    rw [h4 g f _ (hH h _ hτ), hmul g h _ hτ]
  · intro γ f
    funext τ
    simp only [cmp, hsl, hupH]

end GlobalTheory.FN
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoeffMemRangeOfIsRoot
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.PsRoot

theorem mem_of_isAlgebraic_of_isAlgClosed (E : Subfield ℂ) [IsAlgClosed E] {x : ℂ}
    (hx : IsAlgebraic E x) : x ∈ E := by
  have hi : IsIntegral E x := hx.isIntegral
  have h1 : (minpoly E x).natDegree = 1 := by
    have := IsAlgClosed.degree_eq_one_of_irreducible E (minpoly.irreducible hi)
    exact Polynomial.natDegree_eq_of_degree_eq_some this
  obtain ⟨y, hy⟩ := (minpoly.natDegree_eq_one_iff).1 h1
  rw [← hy]
  exact y.2

theorem coeff_mem_range_of_isRoot : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ)
    (b : PowerSeries ℂ) (Q : Polynomial (PowerSeries ℂ)), Q ≠ 0 →
    (∀ i k, PowerSeries.coeff k (Q.coeff i) ∈ ε.range) → Q.eval b = 0 →
    ∀ k, PowerSeries.coeff k b ∈ ε.range := by
  intro Ω _ _ ε b Q hQ hcoef hb k
  let E : Subfield ℂ := ε.fieldRange
  haveI : IsAlgClosed E := IsAlgClosed.of_ringEquiv Ω E ε.rangeRestrictFieldEquiv
  have hE : ∀ z : ℂ, z ∈ ε.range → z ∈ E := fun z hz => by
    obtain ⟨y, rfl⟩ := hz
    exact ⟨y, rfl⟩

  have hroot : ∀ g : ℂ ≃ₐ[E] ℂ, Q.IsRoot (PowerSeries.map (g : ℂ →+* ℂ) b) := by
    intro g
    have hfix : Q.map (PowerSeries.map (g : ℂ →+* ℂ)) = Q := by
      ext i j
      rw [Polynomial.coeff_map, PowerSeries.coeff_map]
      obtain ⟨y, hy⟩ := hE _ (hcoef i j)
      rw [← hy]
      exact g.commutes ⟨_, ⟨y, rfl⟩⟩
    have h2 := Polynomial.eval_map_apply (PowerSeries.map (g : ℂ →+* ℂ)) (p := Q) b
    show Q.eval _ = 0
    rw [hfix, hb, map_zero] at h2
    exact h2
  have hfin : (Set.range fun g : ℂ ≃ₐ[E] ℂ => g (PowerSeries.coeff k b)).Finite := by
    refine ((Polynomial.finite_setOf_isRoot hQ).image (PowerSeries.coeff k)).subset ?_
    rintro _ ⟨g, rfl⟩
    refine ⟨PowerSeries.map (g : ℂ →+* ℂ) b, hroot g, ?_⟩
    simp [PowerSeries.coeff_map]
  obtain ⟨y, hy⟩ := mem_of_isAlgebraic_of_isAlgClosed E (_root_.GlobalTheory.FinOrbit.isAlgebraic_of_finite_orbit E _ hfin)
  exact ⟨y, hy⟩

end GlobalTheory.PsRoot
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EvNormOpEqNrmStatement
section
open GlobalTheory.Col PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ev_normOp_eq_nrm_ev_succ : ∀ (R : Type) [CommRing R] (p m : ℕ) [hp : Fact p.Prime] (hm : 1 ≤ m), IsAdicComplete (Ideal.span {(p : R)}) R → ∀ h : PowerSeries R, ev R p m (normOp p h) = nrm p m hm (ev R p (m + 1) h) := by
  first | exact @GlobalTheory.Col.ev_normOp_eq_nrm | exact GlobalTheory.Col.ev_normOp_eq_nrm | (intros; apply GlobalTheory.Col.ev_normOp_eq_nrm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EvalSeriesAndDerivUniqueOfCoefficientsStatement
section
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.evalSeriesAndDeriv_unique_of_coefficients : ∀ (p : ℕ) [Fact p.Prime], ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : GlobalTheory.K5.Tower p Ω) (n : ℕ), ∀ (ψ : O0 p →+* Ω), IsReb T n ψ → ∀ (c : ℤ → Ω) (x x' y y' : Ω), Ev ψ c x x' → Ev ψ c y y' → x = y ∧ x' = y' := by
  first | exact @GlobalTheory.EvUniq.ev_unique | exact GlobalTheory.EvUniq.ev_unique | (intros; apply GlobalTheory.EvUniq.ev_unique <;> assumption)
end

