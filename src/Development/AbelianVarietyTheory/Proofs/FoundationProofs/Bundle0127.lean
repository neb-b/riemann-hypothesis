module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
public import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0009
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0307
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0115
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0108
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0105
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0122
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0113
public import Formalism.GaloisCohomology.LocalTateDualityK

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralOverJInvariantOfHasSomeLevelOver
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

noncomputable section
namespace GlobalTheory.FN

theorem gact_one_bij (N : ℕ) : ActBij (gact N 1) := by
  intro γ
  simp only [gact, one_mul, inv_one, mul_one]
  exact (Group.mulRight_bijective _)

theorem redGL_one (N : ℕ) : redGL N 1 = 1 := by
  ext i j; simp [redGL]

theorem rel_div (w n : ℕ) (D x J : ℂ) (hD : D ≠ 0) (s : Fin n → ℂ) (P : Fin n → Polynomial ℂ)
    (hs : ∀ j : Fin n, s j = D ^ (w * (n - j)) * (P j).eval J)
    (h : (D ^ w * x) ^ n + ∑ j, s j * (D ^ w * x) ^ (j : ℕ) = 0) :
    x ^ n + ∑ j, (P j).eval J * x ^ (j : ℕ) = 0 := by
  have hD' : D ^ (w * n) ≠ 0 := pow_ne_zero _ hD
  refine (mul_eq_zero.mp ?_).resolve_left hD'
  rw [← h, mul_add, Finset.mul_sum]
  congr 1
  · rw [mul_pow, pow_mul]
  · refine Finset.sum_congr rfl fun j _ => ?_
    have hj : (j : ℕ) ≤ n := j.2.le
    have e : w * n = w * (n - j) + w * j := by rw [← mul_add, Nat.sub_add_cancel hj]
    rw [hs, e, mul_pow, pow_add, ← pow_mul]
    ring

theorem integral_over_jT : ∀ (E : Subring ℂ) (f : ℍ → ℂ), InR E f → ∃ (n : ℕ) (c : Fin n → Polynomial ℂ), (∀ i k, (c i).coeff k ∈ E) ∧ ∀ τ, f τ ^ n + ∑ i, (c i).eval (jT τ) * f τ ^ (i : ℕ) = 0 := by
  intro E f ⟨N, w, hN, hinv, hq⟩
  haveI : NeZero N := ⟨hN.ne'⟩
  have hslash : ∀ γ : SL(2, ℤ), (fun τ => DD τ ^ w * f τ) ∣[((12 * w : ℕ) : ℤ)] γ = fun τ => DD τ ^ w * f (γ • τ) :=
    fun γ => _root_.GlobalTheory.disc_pow_mul_slash w f γ
  have hΓ : ∀ γ ∈ CongruenceSubgroup.Gamma N, (fun τ => DD τ ^ w * f τ) ∣[((12 * w : ℕ) : ℤ)] γ = (fun τ => DD τ ^ w * f τ) := by
    intro γ hγ
    rw [hslash]; funext τ; rw [hinv γ hγ τ]
  obtain ⟨F, hFam, hFγ, hF0⟩ := GlobalTheory.T.exists_slTwoPermutedModularFamily_of_level N ((12 * w : ℕ) : ℤ) _ hΓ
  have hQ : ∀ α, QAll (· ∈ E) N (F α) := by
    intro α
    rcases hF0 α with ⟨γ, rfl⟩ | h0
    · rw [hFγ, hslash]; exact hq γ
    · rw [h0]
      refine ⟨fun _ => 0, fun τ => ?_, fun _ => E.zero_mem⟩
      simpa using (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℂ)) 0)
  have h1 : F 1 = fun τ => DD τ ^ w * f τ := by
    rw [← redGL_one N, hFγ]; exact SlashAction.slash_one _ _
  obtain ⟨s, hs, hpoly⟩ := _root_.GlobalTheory.QFam.minpoly_coeff_invariant (GL (Fin 2) (ZMod N)) (gact N 1) (12 * w) N F E hN
    (gact_one_bij N) hFam hQ
  have key := hpoly 1
  rw [h1] at key
  clear hpoly hFam hF0 hFγ hQ h1 hslash hΓ
  revert s
  generalize Fintype.card (GL (Fin 2) (ZMod N)) = n
  intro s hs key
  have hP : ∀ j : Fin n, ∃ P : Polynomial ℂ, (∀ i, P.coeff i ∈ E) ∧
      ∀ τ, s j τ = DD τ ^ (w * (n - j)) * P.eval (jT τ) := by
    intro j
    refine GlobalTheory.QFam.exists_eq_DD_pow_mul_eval_jT E N (w * (n - j)) (s j) hN (fun γ => ?_) (hs j).2
    have := (hs j).1 γ
    convert this using 3
    push_cast; ring
  choose P hPc hPe using hP
  exact ⟨n, P, hPc, fun τ => rel_div w n (DD τ) (f τ) (jT τ) (ReciprocityTheory.ChartRestriction.L1.DD_ne_zero τ)
    (fun j => s j τ) P (fun j => hPe j τ) (key τ)⟩

end GlobalTheory.FN
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsIntegralModularTowerJCompGlTwoPosRat
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

noncomputable section

namespace GlobalTheory.KZ.JInt

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

lemma det_pos (g : GQ) : 0 < ent g 0 0 * ent g 1 1 - ent g 0 1 * ent g 1 0 := by
  have h := g.2
  rw [Matrix.mem_glpos] at h
  simpa [ent, Matrix.det_fin_two] using h

lemma den_ne (g : GQ) {z : ℂ} (hz : z ∈ Hs) : (ent g 1 0 : ℂ) * z + (ent g 1 1 : ℂ) ≠ 0 := by
  intro h
  have him := congrArg Complex.im h
  have hre := congrArg Complex.re h
  have hz' : 0 < z.im := hz
  simp at him hre
  have hc : ent g 1 0 = 0 := by
    rcases him with h1 | h1
    · exact h1
    · exact absurd h1 hz'.ne'
  rw [hc] at hre
  simp at hre
  have := det_pos g
  rw [hc, hre] at this
  simp at this

lemma mob_im (g : GQ) {z : ℂ} (hz : z ∈ Hs) : mob g z ∈ Hs := by
  have hd := den_ne g hz
  have hz' : 0 < z.im := hz
  have hn : 0 < Complex.normSq ((ent g 1 0 : ℂ) * z + (ent g 1 1 : ℂ)) := Complex.normSq_pos.2 hd
  have key : (mob g z).im = ((ent g 0 0 * ent g 1 1 - ent g 0 1 * ent g 1 0 : ℚ) : ℝ) * z.im /
      Complex.normSq ((ent g 1 0 : ℂ) * z + (ent g 1 1 : ℂ)) := by
    simp only [mob]
    rw [Complex.div_im]
    simp
    field_simp
    ring
  show 0 < (mob g z).im
  rw [key]
  have := det_pos g
  have : (0 : ℝ) < ((ent g 0 0 * ent g 1 1 - ent g 0 1 * ent g 1 0 : ℚ) : ℝ) := by exact_mod_cast this
  positivity

lemma mob_diff (g : GQ) : DifferentiableOn ℂ (mob g) Hs := by
  intro z hz
  apply DifferentiableAt.differentiableWithinAt
  show DifferentiableAt ℂ (fun z => ((ent g 0 0 : ℂ) * z + (ent g 0 1 : ℂ)) / ((ent g 1 0 : ℂ) * z + (ent g 1 1 : ℂ))) z
  exact ((differentiableAt_id.const_mul _).add_const _).div
    ((differentiableAt_id.const_mul _).add_const _) (den_ne g hz)

def holR (X : Tower Ω ε) : Subring X.K where
  carrier := {h | ∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an h = (φ : Mero)}
  mul_mem' := by
    rintro a b ⟨φ, hφ, ha⟩ ⟨ψ, hψ, hb⟩
    exact ⟨φ * ψ, hφ.mul hψ, by rw [map_mul, ha, hb]; rfl⟩
  one_mem' := ⟨fun _ => 1, differentiableOn_const 1, by rw [map_one]; rfl⟩
  add_mem' := by
    rintro a b ⟨φ, hφ, ha⟩ ⟨ψ, hψ, hb⟩
    exact ⟨φ + ψ, hφ.add hψ, by rw [map_add (f := _), ha, hb]; rfl⟩
  zero_mem' := ⟨fun _ => 0, differentiableOn_const 0, by rw [map_zero]; rfl⟩
  neg_mem' := by
    rintro a ⟨φ, hφ, ha⟩
    exact ⟨-φ, hφ.neg, by rw [map_neg, ha]; rfl⟩

end GlobalTheory.KZ.JInt

namespace GlobalTheory.KZ.JInt


open Polynomial in
theorem jK_sl_isIntegral : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε),
    Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) →
    ∀ g : GQ, IsIntegral (Algebra.adjoin Ω {X.jK}) (X.sl g X.jK) := by
  intro Ω _ _ _ ε Tw hε hj g
  set f := Tw.sl g Tw.jK with hf
  obtain ⟨M, hM, hlev⟩ := Tw.level f
  haveI : NeZero M := ⟨hM.ne'⟩
  let red : SL(2, ℤ) →* SL(2, ZMod M) := Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M))

  have hred : ∀ γ γ' : SL(2, ℤ), red γ = red γ' → Tw.sl (ofSL γ) f = Tw.sl (ofSL γ') f := by
    intro γ γ' h
    have hmem : γ' * γ⁻¹ ∈ CongruenceSubgroup.Gamma M := by
      rw [CongruenceSubgroup.Gamma_mem']
      show red (γ' * γ⁻¹) = 1
      rw [map_mul, map_inv, h, mul_inv_cancel]
    have e : γ' = (γ' * γ⁻¹) * γ := by group
    rw [e, map_mul, Tw.sl_mul, hlev _ hmem]
  let S : Set Tw.K := Set.range fun γ : SL(2, ℤ) => Tw.sl (ofSL γ) f
  have hSfin : S.Finite := by
    classical
    let F : SL(2, ZMod M) → Tw.K := fun γb => if h : ∃ γ, red γ = γb then Tw.sl (ofSL h.choose) f else 0
    apply (Set.finite_range F).subset
    rintro _ ⟨γ, rfl⟩
    refine ⟨red γ, ?_⟩
    have h : ∃ γ', red γ' = red γ := ⟨γ, rfl⟩
    simp only [F, dif_pos h]
    exact hred _ _ h.choose_spec
  let T := hSfin.toFinset
  have hT : ∀ y, y ∈ T ↔ y ∈ S := fun y => Set.Finite.mem_toFinset hSfin
  let P : Tw.K[X] := ∏ y ∈ T, (X - C y)
  have hPmon : P.Monic := monic_prod_of_monic _ _ fun y _ => monic_X_sub_C y
  have hfT : f ∈ T := by
    rw [hT]; exact ⟨1, by simp [Tw.sl_one]⟩
  have hPf : P.eval f = 0 := by
    rw [eval_prod]
    exact Finset.prod_eq_zero hfT (by simp)

  have hinv : ∀ (δ : SL(2, ℤ)) (n : ℕ), Tw.sl (ofSL δ) (P.coeff n) = P.coeff n := by
    intro δ n
    have hmap : P.map ((Tw.sl (ofSL δ) : Tw.K ≃ₐ[Ω] Tw.K) : Tw.K →+* Tw.K) = P := by
      simp only [P, Polynomial.map_prod, Polynomial.map_sub, map_X, map_C]
      refine Finset.prod_nbij' (fun y => Tw.sl (ofSL δ) y) (fun y => Tw.sl (ofSL δ⁻¹) y) ?_ ?_ ?_ ?_ ?_
      · intro y hy
        rw [hT] at hy ⊢
        obtain ⟨γ, rfl⟩ := hy
        exact ⟨γ * δ, by simp only [map_mul, Tw.sl_mul]⟩
      · intro y hy
        rw [hT] at hy ⊢
        obtain ⟨γ, rfl⟩ := hy
        exact ⟨γ * δ⁻¹, by simp only [map_mul, Tw.sl_mul]⟩
      · intro y _
        rw [← Tw.sl_mul, ← map_mul, mul_inv_cancel, map_one, Tw.sl_one]
      · intro y _
        rw [← Tw.sl_mul, ← map_mul, inv_mul_cancel, map_one, Tw.sl_one]
      · intro y _
        rfl
    have := congrArg (fun p => p.coeff n) hmap
    simpa [coeff_map] using this

  obtain ⟨φ, hφ, hjφ⟩ := hj
  have hmemS : ∀ y ∈ T, y ∈ holR Tw := by
    intro y hy
    rw [hT] at hy
    obtain ⟨γ, rfl⟩ := hy
    have e : Tw.sl (ofSL γ) f = Tw.sl (g * ofSL γ) Tw.jK := by rw [Tw.sl_mul]
    show Tw.sl (ofSL γ) f ∈ holR Tw
    rw [e]
    exact ⟨fun z => φ (mob (g * ofSL γ) z),
      hφ.comp (mob_diff _) (fun z hz => mob_im _ hz), Tw.an_sl _ _ _ hjφ⟩
  let Q : (holR Tw)[X] := ∏ y ∈ T.attach, (X - C ⟨y.1, hmemS y.1 y.2⟩)
  have hQ : Q.map (holR Tw).subtype = P := by
    simp only [Q, P, Polynomial.map_prod, Polynomial.map_sub, map_X, map_C, Subring.subtype_apply]
    exact Finset.prod_attach T (fun y => X - C y)
  have hhol : ∀ n, P.coeff n ∈ holR Tw := by
    intro n
    rw [← hQ, coeff_map]
    exact (Q.coeff n).2

  have hA : ∀ n, P.coeff n ∈ Algebra.adjoin Ω {Tw.jK} := fun n =>
    _root_.GlobalTheory.KZ.LevelOne.mem_adjoin_j ε Tw hε ⟨φ, hφ, hjφ⟩ (P.coeff n) (fun δ => hinv δ n) (hhol n)
  have hlift : P ∈ lifts (algebraMap (Algebra.adjoin Ω {Tw.jK}) Tw.K) := by
    rw [lifts_iff_coeff_lifts]
    intro n
    exact ⟨⟨_, hA n⟩, rfl⟩
  obtain ⟨q, hqmap, -, hqmon⟩ := lifts_and_natDegree_eq_and_monic hlift hPmon
  exact ⟨q, hqmon, by rw [eval₂_eq_eval_map, hqmap, hPf]⟩

end GlobalTheory.KZ.JInt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsLogDerivQExpansionFinsetProdZpow
section
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

namespace GlobalTheory

theorem isDl_finset_prod_zpow : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : GlobalTheory.KZ.Tower Ω ε), (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) →
  ∀ (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω), ((l : ℕ) : Ω) ∈ A.nonunits → ∀ (n : ℕ) (s : ℚ) (ι : Type) (I : Finset ι) (f : ι → X.K) (φ : ι → HahnSeries ℚ Ω) (m : ι → ℤ), (∀ i ∈ I, IsDl X A l n s (f i) (φ i)) → IsDl X A l n s (∏ i ∈ I, f i ^ m i) (∑ i ∈ I, m i • φ i) := by
  intro Ω _ _ _ ε X hj l _ A hl n s ι I f φ m h
  classical
  have C := fun (a b : X.K) (u v : HahnSeries ℚ Ω) => _root_.GlobalTheory.Glue.isDl_calc ε X hj l A hl n s a b u v
  have one : IsDl X A l n s (1 : X.K) 0 := by
    have := (C 1 1 0 0).2.2.2.1 1 one_ne_zero
    simpa using this
  have npow : ∀ (g : X.K) (u : HahnSeries ℚ Ω), IsDl X A l n s g u → ∀ k : ℕ, IsDl X A l n s (g ^ k) (k • u) := by
    intro g u hg k
    induction k with
    | zero => simpa using one
    | succ k ih =>
      rw [pow_succ, succ_nsmul]
      exact (C (g ^ k) g (k • u) u).1 ih hg
  have zp : ∀ (g : X.K) (u : HahnSeries ℚ Ω), IsDl X A l n s g u → ∀ k : ℤ, IsDl X A l n s (g ^ k) (k • u) := by
    intro g u hg k
    cases k with
    | ofNat k =>
      rw [Int.ofNat_eq_coe, zpow_natCast, natCast_zsmul]
      exact npow g u hg k
    | negSucc k =>
      rw [zpow_negSucc, negSucc_zsmul]
      exact (C (g ^ (k + 1)) 1 ((k + 1) • u) 0).2.1 (npow g u hg (k + 1))
  induction I using Finset.induction_on with
  | empty => simpa using one
  | insert a I ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact (C _ _ _ _).1 (zp _ _ (h a (Finset.mem_insert_self a I)) (m a))
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemSubfieldOfFixedByGeometricTowerGalois
section
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois GlobalTheory.GeoFix

namespace GlobalTheory.GeoFix

theorem isAlgZp_tower_zeta {p : ℕ} [hp : Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]
    (T : Tower p Ω) (n : ℕ) : IsAlgZp (p := p) (T.ζ n) := by
  refine ⟨Polynomial.X ^ (p ^ n) - 1, ?_, ?_⟩
  · exact (Polynomial.monic_X_pow_sub_C (1 : ℤ_[p]) (pow_ne_zero _ hp.out.ne_zero)).ne_zero
  · simp [(T.prim n).pow_eq_one]

theorem mem_of_fixed_ggeo_gn : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
    ∀ (T : Tower p Ω) (n : ℕ) (F : Subfield Ω), (∀ c : O0 p, algebraMap (O0 p) Ω c ∈ F) →
    (∀ x : Ω, IsAlgZp (p := p) x → x ∈ F) → T.qq n ∈ F →
    ∀ o : Ω, (∀ g ∈ Ggeo (p := p) Ω ⊓ Gn T n, g o = o) → o ∈ F := by
  intro p _ Ω _ _ hc T n F hO hA hq o ho
  haveI : CharZero Ω := GlobalTheory.K5.Basic.charZero_of_isClo hc
  haveI : IsAlgClosed Ω := hc.clo
  let f : O0 p →+* F := (algebraMap (O0 p) Ω).codRestrict F hO
  letI : Algebra (O0 p) F := f.toAlgebra
  haveI : IsScalarTower (O0 p) F Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hf : Function.Injective (algebraMap (O0 p) F) := fun a b h => hc.inj (congrArg Subtype.val h)
  haveI : Algebra.IsAlgebraic (O0 p) Ω := hc.alg
  haveI : Algebra.IsAlgebraic F Ω := Algebra.IsAlgebraic.extendScalars (R := O0 p) hf
  haveI : IsAlgClosure F Ω := ⟨hc.clo, inferInstance⟩
  haveI : IsGalois F Ω := IsAlgClosure.isGalois F Ω
  have key := (InfiniteGalois.mem_range_algebraMap_iff_fixed (k := F) o).2 fun σ => by
    let g : Gal p Ω := AlgEquiv.ofRingEquiv (f := σ.toRingEquiv) fun c => σ.commutes (f c)
    have hg : g ∈ Ggeo (p := p) Ω ⊓ Gn T n := by
      refine ⟨fun x hx => σ.commutes ⟨x, hA x hx⟩, ?_, ?_⟩
      · show g • T.ζ n = T.ζ n
        exact σ.commutes ⟨T.ζ n, hA _ (isAlgZp_tower_zeta T n)⟩
      · show g • T.qq n = T.qq n
        exact σ.commutes ⟨T.qq n, hq⟩
    exact ho g hg
  obtain ⟨x, rfl⟩ := key
  exact x.2

end GlobalTheory.GeoFix
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NatCardCokerKerPadicModPow
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology

namespace GlobalTheory

open NumberField IsDedekindDomain in
private lemma natCard_quotient_ker_of_surjective {G H : Type*} [AddGroup G] [AddGroup H]
    (φ : G →+ H) (hφ : Function.Surjective φ) : Nat.card (G ⧸ φ.ker) = Nat.card H :=
  Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective φ hφ).toEquiv


open NumberField IsDedekindDomain in
theorem _root_.GlobalTheory.natCard_coker_ker_mod_pow : ∀ (l : ℕ) [Fact l.Prime] (r : ℕ) (X P : Type) [AddCommGroup X] [Module ℤ_[l] X] [AddCommGroup P] [Module ℤ_[l] P] (f : X →ₗ[ℤ_[l]] P) (R : Type) [CommRing R] (X' P' : Type) [AddCommGroup X'] [Module R X'] [AddCommGroup P'] [Module R P'] (f' : X' →ₗ[R] P') (πX : X →+ X') (πP : P →+ P'), Function.Surjective πX → Function.Surjective πP → (∀ x, πX x = 0 ↔ ∃ y, (l : ℤ_[l]) ^ r • y = x) → (∀ x, πP x = 0 ↔ ∃ y, (l : ℤ_[l]) ^ r • y = x) → (∀ x, πP (f x) = f' (πX x)) → Nat.card ((P ⧸ LinearMap.range f) ⧸ LinearMap.range (LinearMap.lsmul ℤ_[l] (P ⧸ LinearMap.range f) ((l : ℤ_[l]) ^ r))) = Nat.card (P' ⧸ LinearMap.range f') ∧ ((∀ x p, f x = (l : ℤ_[l]) ^ r • p → ∃ x', f x = (l : ℤ_[l]) ^ r • f x') → Nat.card (LinearMap.ker f ⧸ (LinearMap.range (LinearMap.lsmul ℤ_[l] X ((l : ℤ_[l]) ^ r))).comap (LinearMap.ker f).subtype) = Nat.card (LinearMap.ker f')) := by
  intro l _ r X P _ _ _ _ f R _ X' P' _ _ _ _ f' πX πP hX hP hkX hkP hcomm
  set c : ℤ_[l] := (l : ℤ_[l]) ^ r with hc
  have hrange : ∀ p : P, πP p ∈ LinearMap.range f' ↔ ∃ x y, p = f x + c • y := by
    intro p
    constructor
    · rintro ⟨x', hx'⟩
      obtain ⟨x, rfl⟩ := hX x'
      have h0 : πP (p - f x) = 0 := by rw [map_sub, hcomm, hx', sub_self]
      obtain ⟨y, hy⟩ := (hkP _).1 h0
      exact ⟨x, y, by rw [hy]; abel⟩
    · rintro ⟨x, y, rfl⟩
      refine ⟨πX x, ?_⟩
      rw [← hcomm, map_add (f := _), (hkP (c • y)).2 ⟨y, rfl⟩, add_zero]
  constructor
  · let φ₁ : P →+ (P ⧸ LinearMap.range f) ⧸
        LinearMap.range (LinearMap.lsmul ℤ_[l] (P ⧸ LinearMap.range f) c) :=
      ((LinearMap.range (LinearMap.lsmul ℤ_[l] (P ⧸ LinearMap.range f) c)).mkQ.comp
        (LinearMap.range f).mkQ).toAddMonoidHom
    let φ₂ : P →+ P' ⧸ LinearMap.range f' := (LinearMap.range f').mkQ.toAddMonoidHom.comp πP
    have hφ₁ : Function.Surjective φ₁ :=
      (Submodule.mkQ_surjective _).comp (Submodule.mkQ_surjective _)
    have hφ₂ : Function.Surjective φ₂ := (Submodule.mkQ_surjective _).comp hP
    have hker : φ₁.ker = φ₂.ker := by
      ext p
      rw [AddMonoidHom.mem_ker, AddMonoidHom.mem_ker]
      change Submodule.Quotient.mk (Submodule.Quotient.mk p) = 0 ↔
        Submodule.Quotient.mk (πP p) = 0
      rw [Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_eq_zero, hrange]
      constructor
      · rintro ⟨q, hq⟩
        obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q
        rw [LinearMap.lsmul_apply, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq] at hq
        obtain ⟨x, hx⟩ := hq
        exact ⟨-x, y, by rw [map_neg, hx]; abel⟩
      · rintro ⟨x, y, rfl⟩
        refine ⟨Submodule.Quotient.mk y, ?_⟩
        rw [LinearMap.lsmul_apply, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq]
        exact ⟨-x, by rw [map_neg]; abel⟩
    rw [← natCard_quotient_ker_of_surjective φ₁ hφ₁, ← natCard_quotient_ker_of_surjective φ₂ hφ₂,
      hker]
  · intro hdiv
    let ψ : LinearMap.ker f →+ LinearMap.ker f' :=
      { toFun := fun x => ⟨πX x, by
          rw [LinearMap.mem_ker, ← hcomm, LinearMap.mem_ker.1 x.2, map_zero]⟩
        map_zero' := by ext; simp
        map_add' := fun x y => by ext; simp }
    have hψ : Function.Surjective ψ := by
      rintro ⟨x', hx'⟩
      obtain ⟨x, rfl⟩ := hX x'
      have h0 : πP (f x) = 0 := by rw [hcomm]; exact hx'
      obtain ⟨p, hp⟩ := (hkP _).1 h0
      obtain ⟨x₁, hx₁⟩ := hdiv x p hp.symm
      refine ⟨⟨x - c • x₁, by rw [LinearMap.mem_ker, map_sub, map_smul, ← hx₁, sub_self]⟩, ?_⟩
      ext
      change πX (x - c • x₁) = πX x
      rw [map_sub, (hkX (c • x₁)).2 ⟨x₁, rfl⟩, sub_zero]
    have hker : ψ.ker = ((LinearMap.range (LinearMap.lsmul ℤ_[l] X c)).comap
        (LinearMap.ker f).subtype).toAddSubgroup := by
      ext x
      rw [AddMonoidHom.mem_ker, Submodule.mem_toAddSubgroup, Submodule.mem_comap,
        LinearMap.mem_range]
      change (⟨πX x, _⟩ : LinearMap.ker f') = 0 ↔ _
      rw [Subtype.ext_iff, ZeroMemClass.coe_zero, hkX]
      simp [LinearMap.lsmul_apply]
    have h := natCard_quotient_ker_of_surjective ψ hψ
    rw [hker] at h
    exact h

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIntTwoCocycleEqPowSmulOfReductionCoboundary
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology

namespace GlobalTheory

theorem padicInt_two_cocycle_eq_pow_smul_of_reduction_coboundary :
    ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [ContinuousMul Γ] (ρ : Representation ℤ_[l] Γ ℤ_[l]), ContAction ρ → ∀ (r : ℕ) (ρr : Representation (ZMod (l ^ r)) Γ (ZMod (l ^ r))), (∀ g x, PadicInt.toZModPow r (ρ g x) = ρr g (PadicInt.toZModPow r x)) → ∀ z ∈ Z2 ρ, (fun p => PadicInt.toZModPow r (z p)) ∈ B2 ρr → ∃ w ∈ Z2 ρ, z - (l : ℤ_[l]) ^ r • w ∈ B2 ρ := by
  intro l _ Γ _ _ _ ρ hρ r ρr hc z hz hB
  obtain ⟨c, hcc, hcd⟩ := (separated_dvr_second_cohomology_mem _ _).1 hB
  have hsurj : Function.Surjective (PadicInt.toZModPow (p := l) r) := ZMod.ringHom_surjective _
  choose s hs using hsurj
  have hsc : Continuous s := continuous_of_discreteTopology
  have hb : d1 ρ (s ∘ c) ∈ B2 ρ := (separated_dvr_second_cohomology_mem _ _).2 ⟨s ∘ c, hsc.comp hcc, rfl⟩
  have hy : z - d1 ρ (s ∘ c) ∈ Z2 ρ := (Z2 ρ).sub_mem hz (coboundaries2_le_cocycles2 ρ hρ hb)
  have hdiv : ∀ p, ∃ a : ℤ_[l], (l : ℤ_[l]) ^ r * a = (z - d1 ρ (s ∘ c)) p := by
    rintro ⟨g, h⟩
    have h1 : (z - d1 ρ (s ∘ c)) (g, h) ∈ RingHom.ker (PadicInt.toZModPow (p := l) r) := by
      have h2 := congrFun hcd (g, h)
      rw [d1_apply] at h2
      rw [RingHom.mem_ker, Pi.sub_apply, d1_apply, map_sub, map_add (f := _), map_sub, hc]
      simp only [Function.comp_apply, hs]
      rw [h2, sub_self]
    rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at h1
    obtain ⟨a, ha⟩ := h1
    exact ⟨a, ha.symm⟩
  choose w hw using hdiv
  have hne : (l : ℤ_[l]) ^ r ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  have hemb : Topology.IsClosedEmbedding (fun x : ℤ_[l] => (l : ℤ_[l]) ^ r * x) :=
    Continuous.isClosedEmbedding (continuous_const.mul continuous_id)
      (mul_right_injective₀ hne)
  have hw' : (l : ℤ_[l]) ^ r • w = z - d1 ρ (s ∘ c) := funext hw
  refine ⟨w, (mem_cocycles2 _ _).2 ⟨?_, fun g h k => ?_⟩, ?_⟩
  · refine hemb.isInducing.continuous_iff.2 ?_
    have : (fun x : ℤ_[l] => (l : ℤ_[l]) ^ r * x) ∘ w = z - d1 ρ (s ∘ c) := funext hw
    rw [this]
    exact hy.1
  · have e := ((mem_cocycles2 _ _).1 hy).2 g h k
    rw [← hw'] at e
    simp only [Pi.smul_apply, map_smul] at e
    rw [← smul_sub, ← smul_add, ← smul_sub, smul_eq_mul] at e
    exact (mul_eq_zero.1 e).resolve_left hne
  · rw [hw', sub_sub_cancel]
    exact hb

end GlobalTheory
end

