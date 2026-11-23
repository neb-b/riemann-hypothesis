module

public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0038
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0030
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0005
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0028
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0020
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0035
public import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0034
public import Formalism.LocalToGlobal.ProjectiveLattices.LiftLoc
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0039
public import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0025

@[expose] public section

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.FnDefB
section
noncomputable section

namespace Formalism.L2.Pj

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.T0 ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}


open Classical in
def toGoodR (c : Coeff l) (σ : c.F →+* ℂ) : ℂ →+* ℂ := if GoodEmb c σ then RingHom.id ℂ else starRingEnd ℂ

theorem toGoodR_apply (c : Coeff l) (σ : c.F →+* ℂ) (x : c.F) : toGoodR c σ (σ x) = goodOf c σ x := by
  unfold toGoodR goodOf
  split_ifs <;> rfl

def toGood (c : Coeff l) (σ : c.F →+* ℂ) : CAt σ →ₐ[c.F] CAt (goodOf c σ) :=
  { (toGoodR c σ : ℂ →+* ℂ) with commutes' := fun x => toGoodR_apply c σ x }

theorem isIdOrConj_toGood (c : Coeff l) (σ : c.F →+* ℂ) : IsIdOrConj (toGood c σ) := by
  by_cases h : GoodEmb c σ
  · left; intro z
    show toGoodR c σ (toC z) = toC z
    unfold toGoodR; rw [if_pos h]; rfl
  · right; intro z
    show toGoodR c σ (toC z) = _
    unfold toGoodR; rw [if_neg h]

theorem rdEx_of (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ)) (hA : AllTest Xo c)
    (hB : ∀ σ, GoodEmb c σ → BCEx Xo c σ) (σ : c.F →+* ℂ) (y : FrPt Xo c (CAt σ)) : ∃ q, RdAt U σ y q := by
  have : IsReduced (CAt σ) := inferInstanceAs (IsReduced ℂ)
  obtain ⟨p, ψ, y0, hy0⟩ := hA (CAt σ) y
  have hg := goodEmb_goodOf c σ
  obtain ⟨z, hz⟩ := hB _ hg p y0 ((toGood c σ).comp ψ)
  have hm : FrMap (toGood c σ) y z := frMap_cancel _ _ _ ψ (toGood c σ) y0 y z hy0 hz
  obtain ⟨k, x, t, ht⟩ := (hU _ hg).2.2.1 z
  exact ⟨⟨k, x, t⟩, z, toGood c σ, isIdOrConj_toGood c σ, hm, ht⟩


end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.GenValInjPf
section
noncomputable section

namespace Formalism.L2.Pj

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor

section Gen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}


theorem evR_of_frMap (hW : EvalWD (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z))
    {f : Rul Xo c} (hf : IsNatural (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) f)
    {S : Type} [CommRing S] [Algebra c.F S] {p : TRing c.F} {φ : p.R →ₐ[c.F] S} {y : FrPt Xo c p.R}
    {w : FrPt Xo c S} (hy : FrMap φ y w) : evR Xo c f w = φ (f p y) := by
  have hT : FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) w := ⟨p, φ, y, hy⟩
  unfold evR evalAt
  rw [dite_eq_left hT]
  exact hW f hf S _ _ _ _ _ _ w hT.choose_spec.choose_spec.choose_spec hy

end Gen

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps

variable {D : D7} {T : Top D}

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.IsAlgebraicOfTrdegEq
section
noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps ReciprocityTheory.ChartRestriction.G.Geo.Tor

section Alg

variable {K L : Type*} [Field K] [Field L] [Algebra K L] {N : ℕ}


variable (K) in
def HomQ (x : Fin N → L) (f : L) : Prop :=
  ∃ (e : ℕ) (A B : MvPolynomial (Fin N) K), A.IsHomogeneous e ∧ B.IsHomogeneous e ∧
    MvPolynomial.aeval x B ≠ 0 ∧ f = MvPolynomial.aeval x A / MvPolynomial.aeval x B

theorem homQ_mul {x : Fin N → L} {f g : L} (hf : HomQ K x f) (hg : HomQ K x g) : HomQ K x (f * g) := by
  obtain ⟨e, A, B, hA, hB, hBx, rfl⟩ := hf
  obtain ⟨e', A', B', hA', hB', hBx', rfl⟩ := hg
  exact ⟨e + e', A * A', B * B', hA.mul hA', hB.mul hB', by rw [map_mul]; exact mul_ne_zero hBx hBx',
    by rw [map_mul, map_mul, div_mul_div_comm]⟩

theorem homQ_add {x : Fin N → L} {f g : L} (hf : HomQ K x f) (hg : HomQ K x g) : HomQ K x (f + g) := by
  obtain ⟨e, A, B, hA, hB, hBx, rfl⟩ := hf
  obtain ⟨e', A', B', hA', hB', hBx', rfl⟩ := hg
  exact ⟨e + e', A * B' + B * A', B * B', (hA.mul hB').add (hB.mul hA'), hB.mul hB',
    by rw [map_mul]; exact mul_ne_zero hBx hBx',
    by rw [map_add (f := _), map_mul, map_mul, map_mul, div_add_div _ _ hBx hBx']⟩

theorem homQ_inv {x : Fin N → L} {f : L} (hf : HomQ K x f) : HomQ K x f⁻¹ := by
  obtain ⟨e, A, B, hA, hB, hBx, rfl⟩ := hf
  by_cases hAx : MvPolynomial.aeval x A = 0
  · rw [hAx, zero_div, inv_zero]
    exact ⟨0, 0, 1, MvPolynomial.isHomogeneous_zero _ _ _, MvPolynomial.isHomogeneous_one _ _, by simp, by simp⟩
  · exact ⟨e, B, A, hB, hA, hAx, by rw [inv_div]⟩

theorem homQ_algebraMap (x : Fin N → L) (c : K) : HomQ K x (algebraMap K L c) :=
  ⟨0, MvPolynomial.C c, 1, MvPolynomial.isHomogeneous_C _ _, MvPolynomial.isHomogeneous_one _ _, by simp, by simp⟩

theorem homQ_ratio (x : Fin N → L) (m k₀ : Fin N) (hx : x k₀ ≠ 0) : HomQ K x (x m / x k₀) :=
  ⟨1, MvPolynomial.X m, MvPolynomial.X k₀, MvPolynomial.isHomogeneous_X _ _, MvPolynomial.isHomogeneous_X _ _,
    by simpa using hx, by simp⟩


variable (K) in
def homQField (x : Fin N → L) : IntermediateField K L where
  carrier := {f | HomQ K x f}
  mul_mem' := fun ha hb => homQ_mul ha hb
  add_mem' := fun ha hb => homQ_add ha hb
  algebraMap_mem' := homQ_algebraMap x
  inv_mem' := fun _ hf => homQ_inv hf

theorem homQ_of_mem_adjoin (x : Fin N → L) (k₀ : Fin N) (hx : x k₀ ≠ 0) {f : L}
    (hf : f ∈ IntermediateField.adjoin K (Set.range fun m => x m / x k₀)) : HomQ K x f := by
  have hle : IntermediateField.adjoin K (Set.range fun m => x m / x k₀) ≤ homQField K x := by
    rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨m, rfl⟩
    exact homQ_ratio x m k₀ hx
  exact hle hf

theorem isAlgebraic_of_trdeg_eq (F : IntermediateField K L) (d : ℕ) (hF : Algebra.trdeg K F = d)
    (hL : Algebra.trdeg K L = d) : Algebra.IsAlgebraic F L := by
  have hs := trdeg_add_eq K F (A := L)
  rw [hF, hL] at hs
  have h0 : Algebra.trdeg F L = 0 := by
    rcases Cardinal.add_eq_left_iff.1 hs with h | h
    · exact absurd ((le_max_left _ _).trans h) (not_le.2 ((Cardinal.natCast_lt_aleph0 (n := d))))
    · exact h
  exact trdeg_eq_zero_iff.1 h0

theorem exists_homInt (x : Fin N → L) (k₀ : Fin N) (hx : x k₀ ≠ 0)
    (halg : Algebra.IsAlgebraic (IntermediateField.adjoin K (Set.range fun m => x m / x k₀)) L) (a : L) :
    ∃ (k n : ℕ) (P : MvPolynomial (Fin N) K) (cf : ℕ → MvPolynomial (Fin N) K), 0 < k ∧ P.IsHomogeneous k ∧
      MvPolynomial.aeval x P ≠ 0 ∧ (∀ i < n, (cf i).IsHomogeneous ((n - i) * k)) ∧
      (MvPolynomial.aeval x P * a) ^ n + ∑ i ∈ Finset.range n,
        MvPolynomial.aeval x (cf i) * (MvPolynomial.aeval x P * a) ^ i = 0 := by
  set F := IntermediateField.adjoin K (Set.range fun m => x m / x k₀) with hFdef
  obtain ⟨p, hpm, hp⟩ := ((halg.isAlgebraic a).isIntegral : IsIntegral F a)
  have hq : ∀ i, HomQ K x ((p.coeff i : F) : L) := fun i => homQ_of_mem_adjoin x k₀ hx (p.coeff i).2
  choose e A B hA hB hBx hf using hq
  obtain ⟨n, hn⟩ : ∃ n, p.natDegree = n := ⟨_, rfl⟩
  set P : MvPolynomial (Fin N) K := MvPolynomial.X k₀ * ∏ i ∈ Finset.range n, B i with hPdef
  have hPh : P.IsHomogeneous (1 + ∑ i ∈ Finset.range n, e i) :=
    (MvPolynomial.isHomogeneous_X K k₀).mul (MvPolynomial.IsHomogeneous.prod _ _ _ fun i _ => hB i)
  have hPx : MvPolynomial.aeval x P = x k₀ * ∏ i ∈ Finset.range n, MvPolynomial.aeval x (B i) := by
    rw [hPdef, map_mul, MvPolynomial.aeval_X, map_prod]
  have hPx0 : MvPolynomial.aeval x P ≠ 0 := by
    rw [hPx]; exact mul_ne_zero hx (Finset.prod_ne_zero_iff.2 fun i _ => hBx i)
  refine ⟨1 + ∑ i ∈ Finset.range n, e i, n, P,
    fun i => P ^ (n - i - 1) * (MvPolynomial.X k₀ * ∏ j ∈ (Finset.range n).erase i, B j) * A i,
    by omega, hPh, hPx0, ?_, ?_⟩
  · intro i hi
    have hS : ∑ j ∈ Finset.range n, e j = e i + ∑ j ∈ (Finset.range n).erase i, e j :=
      (Finset.add_sum_erase _ _ (Finset.mem_range.2 hi)).symm
    have h1 := ((hPh.pow (n - i - 1)).mul ((MvPolynomial.isHomogeneous_X K k₀).mul
      (MvPolynomial.IsHomogeneous.prod ((Finset.range n).erase i) B e fun j _ => hB j))).mul (hA i)
    convert h1 using 1
    obtain ⟨t, ht⟩ : ∃ t, n - i = t + 1 := ⟨n - i - 1, by omega⟩
    rw [ht, Nat.add_sub_cancel, hS]
    ring
  · beta_reduce
    have hp' : Polynomial.aeval a p = 0 := by rw [Polynomial.aeval_def]; exact hp
    rw [Polynomial.aeval_eq_sum_range, Finset.sum_range_succ, hpm.coeff_natDegree, one_smul, hn] at hp'
    have key : ∀ i ∈ Finset.range n,
        MvPolynomial.aeval x (P ^ (n - i - 1) * (MvPolynomial.X k₀ * ∏ j ∈ (Finset.range n).erase i, B j) * A i) *
          (MvPolynomial.aeval x P * a) ^ i = MvPolynomial.aeval x P ^ n * (p.coeff i • a ^ i) := by
      intro i hi
      have hi' := Finset.mem_range.1 hi
      have hPi : MvPolynomial.aeval x P = x k₀ * (MvPolynomial.aeval x (B i) *
          ∏ j ∈ (Finset.range n).erase i, MvPolynomial.aeval x (B j)) := by
        rw [hPx, ← Finset.mul_prod_erase _ _ hi]
      have hsm : p.coeff i • a ^ i = MvPolynomial.aeval x (A i) / MvPolynomial.aeval x (B i) * a ^ i := by
        rw [Algebra.smul_def, IntermediateField.algebraMap_apply, hf i]
      obtain ⟨t, ht⟩ : ∃ t, n - i = t + 1 := ⟨n - i - 1, by omega⟩
      have hpow : MvPolynomial.aeval x P ^ n =
          MvPolynomial.aeval x P ^ t * MvPolynomial.aeval x P * MvPolynomial.aeval x P ^ i := by
        rw [← pow_succ, ← pow_add]; congr 1; omega
      rw [hsm, hpow]
      simp only [map_mul, map_pow, MvPolynomial.aeval_X, map_prod]
      rw [ht, Nat.add_sub_cancel, hPi]
      field_simp [hBx i]
      ring
    rw [Finset.sum_congr rfl key, ← Finset.mul_sum, mul_pow, ← mul_add, add_comm, hp', mul_zero]

end Alg

variable {D : D7} {T : Top D} (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c)

def IntFormSt {wL : WeightFamilies.Wt D j} {N : ℕ} (w : Fin N → (recB h.toLawsCore).Cusp j wL) : Prop :=
  ∀ (Z : Comp (T.Q.Xo j) T.Q.c) (k n : ℕ) (cf : ℕ → MvPolynomial (Fin N) T.Q.c.F) (b : Om Z), 0 < k →
    (∀ i < n, (cf i).IsHomogeneous ((n - i) * k)) →
    b ^ n + ∑ i ∈ Finset.range n,
        MvPolynomial.aeval (fun m => evC hG Z ((w m : (recB h.toLawsCore).Cusp j wL) : T.R j)) (cf i) * b ^ i = 0 →
    ∃ g : (recB h.toLawsCore).Cusp j (wsmul k wL),
      evC hG Z ((g : (recB h.toLawsCore).Cusp j (wsmul k wL)) : T.R j) = b

theorem birSt_of (htr : FnTrdeg (T.Q.Xo j) T.Q.c (WeightFamilies.dimY D j)) {ka wL wF : WeightFamilies.Wt D j}
    (G : GlobalFamilyData (recPlus h j hj) ka wL wF)
    (hB2 : ∀ Z : Comp (T.Q.Xo j) T.Q.c, ∃ k₀, evC hG Z ((G.w k₀ : (recB h.toLawsCore).Cusp j wL) : T.R j) ≠ 0 ∧
      Algebra.trdeg T.Q.c.F (IntermediateField.adjoin T.Q.c.F (Set.range fun k =>
        evC hG Z ((G.w k : (recB h.toLawsCore).Cusp j wL) : T.R j) /
          evC hG Z ((G.w k₀ : (recB h.toLawsCore).Cusp j wL) : T.R j))) = WeightFamilies.dimY D j)
    (hint : IntFormSt h j hG G.w) : BIRSt h j hj hG G := by
  intro Z a
  obtain ⟨k₀, hx0, htrF⟩ := hB2 Z
  have halg := isAlgebraic_of_trdeg_eq _ _ htrF (htr Z)
  obtain ⟨k, n, P, cf, hk, hP, hP0, hcf, heq⟩ := exists_homInt (K := T.Q.c.F) _ k₀ hx0 halg a
  obtain ⟨g, hg⟩ := hint Z k n cf _ hk hcf heq
  exact ⟨k, g, P, hP, hP0, by rw [hg, mul_comm]⟩

theorem birSt_of_big (htr : FnTrdeg (T.Q.Xo j) T.Q.c (WeightFamilies.dimY D j)) {ka wL wF : WeightFamilies.Wt D j}
    (G : GlobalFamilyData (recPlus h j hj) ka wL wF) (hBig : BigAt h j hj hG G) (hint : IntFormSt h j hG G.w) :
    BIRSt h j hj hG G :=
  birSt_of h j hj hG htr G hBig.2 hint

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.LocRingPf
section
noncomputable section

namespace Formalism.L2.Pj

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Gaps.EtaleWeightGaps NumberField IsDedekindDomain

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {E : PtExt X} {hM : IntAtExt X E}
  {ka wL wF : WeightFamilies.Wt D j}

def ESecSt (G : GlobalFamilyData (xplus X E hM) ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) : Prop :=
  ∀ (y : PtsG G la → E.Pt' la) (hw : ∀ ζ, FromW ζ (y ζ)) (g0 : B.Cusp j wF),
    Nonempty (CurveModel G la g0) →
    (∀ ζ, (hw ζ).ev (emb (xplus X E hM) la G.N (X.inc wF g0)) ≠ 0) →
    ∃ (k : ℕ) (p q : Rp (xplus X E hM) la G.N),
      p ∈ Vw (xplus X E hM) la G.N (addL (wt0 D j) wL k) ∧ q ∈ Vw (xplus X E hM) la G.N (addL (wt0 D j) wL k) ∧
      (∀ β, β ≠ 0 → hasseRp (xplus X E hM) la G.N β p = 0) ∧
      (∀ β, β ≠ 0 → hasseRp (xplus X E hM) la G.N β q = 0) ∧
      ∀ ζ, (hw ζ).ev p ≠ 0 ∧ (hw ζ).ev q ≠ 0 ∧
        vV (hw ζ).T.V ((hw ζ).ev p) + vV (hw ζ).T.V ((hw ζ).ev (emb (xplus X E hM) la G.N (X.inc wF g0))) =
          vV (hw ζ).T.V ((hw ζ).ev q)

def LocStructSt (G : GlobalFamilyData (xplus X E hM) ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) : Prop :=
  ∀ (y : PtsG G la → E.Pt' la) (hw : ∀ ζ, FromW ζ (y ζ)) (g0 : B.Cusp j wF),
    Nonempty (CurveModel G la g0) →
    (∀ ζ, (hw ζ).ev (emb (xplus X E hM) la G.N (X.inc wF g0)) ≠ 0) →
    ∀ g : ↥(Frac0 (xplus X E hM) la G.w),
      (∀ ζ, 0 ≤ nval (hw ζ).T.V 1 ((hw ζ).toSecPt.lift (g : Lw (xplus X E hM) la G.w))) →
      ∃ (f d : ↥(Frac0 (xplus X E hM) la G.w)) (hd : ∀ ζ, (hw ζ).toSecPt.lift (d : Lw (xplus X E hM) la G.w) ≠ 0),
        toOsK (xplus X E hM) la G.w f = toOsK (xplus X E hM) la G.w d * toOsK (xplus X E hM) la G.w g ∧
        ∀ (l : List (Idx D j G.N →₀ ℕ)) (ζ : PtsG G la),
          0 ≤ nval (hw ζ).T.V 1 (evL (fun ζ => (hw ζ).toSecPt) ζ (hdList (fun ζ => (hw ζ).toSecPt) l
            (ιW (fun ζ => (hw ζ).toSecPt) (f : Lw (xplus X E hM) la G.w) *
              ↑(isUnit_of_lift_ne (fun ζ => (hw ζ).toSecPt) hd).unit⁻¹)))

theorem locRing_of {G : GlobalFamilyData (xplus X E hM) ka wL wF} {la : HeightOneSpectrum (𝓞 B.KO)}
    (h1 : ESecSt G la) (h2 : LocStructSt G la) : LocRingSt G la :=
  fun y hw g0 hC hg0 => ⟨h1 y hw g0 hC hg0, h2 y hw g0 hC hg0⟩

section Inst

variable {T : Top D} (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c)

def ValSepSt {ka wL wF : WeightFamilies.Wt D j} (G : GlobalFamilyData (recPlus h j hj) ka wL wF)
    (la : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO)) : Prop :=
  ∀ (y : PtsG G la → (extAll h j hj).Pt' la) (hw : ∀ ζ, FromW ζ (y ζ)),
    ∃ (Zc : PtsG G la → Comp (T.Q.Xo j) T.Q.c) (ι : ∀ ζ, Om (Zc ζ) →+* (hw ζ).T.Fr),
      (∀ ζ, ∃ a : Om (Zc ζ), vV (hw ζ).T.V (ι ζ a) = 1) ∧
      (∀ ζ (w : WeightFamilies.Wt D j) (F : (recB h.toLawsCore).Cusp j w),
        evC hG (Zc ζ) ((F : (recB h.toLawsCore).Cusp j w) : T.R j) = 0 →
          (hw ζ).ev (emb (recPlus h j hj) la G.N ((recPJ h j hj).inc w F)) = 0) ∧
      (∀ ζ (w : WeightFamilies.Wt D j) (F F' : (recB h.toLawsCore).Cusp j w),
        ι ζ (evC hG (Zc ζ) ((F : (recB h.toLawsCore).Cusp j w) : T.R j)) *
            (hw ζ).ev (emb (recPlus h j hj) la G.N ((recPJ h j hj).inc w F')) =
          ι ζ (evC hG (Zc ζ) ((F' : (recB h.toLawsCore).Cusp j w) : T.R j)) *
            (hw ζ).ev (emb (recPlus h j hj) la G.N ((recPJ h j hj).inc w F))) ∧
      ∀ ζ ζ', ζ ≠ ζ' → Zc ζ = Zc ζ' →
        ∃ (w : WeightFamilies.Wt D j) (F F' : (recB h.toLawsCore).Cusp j w),
          (hw ζ).ev (emb (recPlus h j hj) la G.N ((recPJ h j hj).inc w F')) ≠ 0 ∧
          (hw ζ').ev (emb (recPlus h j hj) la G.N ((recPJ h j hj).inc w F')) ≠ 0 ∧
          nval (hw ζ).T.V 1 ((hw ζ).ev (emb (recPlus h j hj) la G.N ((recPJ h j hj).inc w F'))) <
            nval (hw ζ).T.V 1 ((hw ζ).ev (emb (recPlus h j hj) la G.N ((recPJ h j hj).inc w F))) ∧
          nval (hw ζ').T.V 1 ((hw ζ').ev (emb (recPlus h j hj) la G.N ((recPJ h j hj).inc w F'))) <
            nval (hw ζ').T.V 1 ((hw ζ').ev (emb (recPlus h j hj) la G.N ((recPJ h j hj).inc w F)) -
              (hw ζ').ev (emb (recPlus h j hj) la G.N ((recPJ h j hj).inc w F')))

end Inst

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.RealPtMain
section
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {D : D7} {T : Top D}

theorem mul_ringHom_units_ratio {K : Type} [Field K] {W S R : K} (hW : W ≠ 0) (k : ℕ) :
    W ^ k * R * (W * S)⁻¹ ^ k = R / S ^ k := by
  have h1 : W ^ k * W⁻¹ ^ k = 1 := by rw [← mul_pow, mul_inv_cancel₀ hW, one_pow]
  rw [mul_inv, mul_pow, div_eq_mul_inv, ← inv_pow]
  linear_combination (R * S⁻¹ ^ k) * h1

set_option maxHeartbeats 4000000 in
theorem realPt_of (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c) {ka wL wF : WeightFamilies.Wt D j}
    (G : GlobalFamilyData (recPlus h j hj) ka wL wF) (la : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO))
    (hU : IsUnif (OsK (recPlus h j hj) la G.w) (unifO (recPlus h j hj) la G.N)) [∀ ζ : PtsG G la, IsDVRAt ζ]
    (hwL : 0 < wL.n) (hPt : PtOfSSt h j hj hG G la) (hT : GenFromTest (T.Q.Xo j) T.Q.c hG)
    (hIF : IntFramesSt (T.Q.Xo j) T.Q.c) (hWt : WtField (T.Q.Xo j) T.Q.c)
    (hMod : ModelAtSt (T.Q.Xo j) T.Q.c la) :
    RealPtNZSt h j hj hG G la hU := by
  have hWD := h.toLawsCore.evalWD j hj
  intro ζ
  haveI hD : IsDVRAt (show Pts (Op (xplus (recPJ h j hj) (extAll h j hj) (intAtExt_extAll h j hj)) la G.N)
      (OsK (xplus (recPJ h j hj) (extAll h j hj) (intAtExt_extAll h j hj)) la G.w) from ζ) :=
    ‹∀ ζ : PtsG G la, IsDVRAt ζ› ζ
  haveI : CharZero (Loc ζ) := loc_charZero hU ζ
  obtain ⟨Tc, ι, hloc, hunr⟩ := complSt_holds (Loc ζ)
  have hι : AddValPres ζ ι := addVal_map_of_unr ι hunr
  let kap : Kp (recPlus h j hj) la G.N →+* Tc.Fr :=
    kapA (X := recPJ h j hj) (E := extAll h j hj) (hM := intAtExt_extAll h j hj) hU ζ Tc ι hι
  letI instK : Algebra (Kp (recPlus h j hj) la G.N) Tc.Fr := kap.toAlgebra
  let φ : OsK (recPlus h j hj) la G.w →ₐ[Kp (recPlus h j hj) la G.N] Tc.Fr :=
    { toRingHom := phiAt ζ Tc.Fr ι hU hι, commutes' := fun _ => by rfl }
  obtain ⟨alg, y₀, ⟨Z, ψ, hψ⟩, halg, hs0, hrat⟩ := hPt hwL Tc.Fr φ
  have halg' : alg = kap.comp ((@algebraMap ((recPlus h j hj).Kl la) (Kp (recPlus h j hj) la G.N) _ _
      (Kp.algKl (recPlus h j hj) la G.N)).comp (algebraMap (recB h.toLawsCore).KO ((recPlus h j hj).Kl la))) :=
    RingHom.ext fun a => halg a
  have ho : OverLa la Tc.V alg (ep (unifO (recPlus h j hj) la G.N) ζ) := by
    rw [halg']
    exact overLa_kapA (X := recPJ h j hj) (E := extAll h j hj) (hM := intAtExt_extAll h j hj) hU ζ Tc ι hι
  obtain ⟨O, _, β, Y, -, hPI, hB⟩ := hMod
  obtain ⟨b, hb⟩ := hB Tc alg _ ho
  letI := alg.toAlgebra
  obtain ⟨y, t, hbor⟩ := intFr_of_model hIF Tc alg Y hPI b hb y₀
  obtain ⟨p, φ', y', hm⟩ := hT Z
  have hm2 : FrMap (ψ.comp φ') y' y₀ := frMap_trans _ _ _ φ' ψ y' (genFr hG Z) y₀ hm hψ
  have hy₀T : FromTest (K := T.Q.c.F) (fun S _ _ => FrPt (T.Q.Xo j) T.Q.c S) (fun φ y z => FrMap φ y z) y₀ :=
    ⟨p, ψ.comp φ', y', hm2⟩
  have hW : ∀ (w : WeightFamilies.Wt D j) (F : (recB h.toLawsCore).Cusp j w),
      evI y (F : T.R j) = wchar (ex (T.Q.Dw j) (wtA w) w.n) t * evR (T.Q.Xo j) T.Q.c (F : T.R j) y₀ := fun w F =>
    hWt (wtA w) w.n (F : T.R j) (cusp_le_sec _ _ _ _ _ (cutR_le T.C j w F.2)) Tc.Fr t y₀ y.1 hy₀T y.2.1 hbor
  let χ : (recPlus h j hj).Forms →+* Tc.Fr := chiI j y
  let ev : Rp (recPlus h j hj) la G.N →+* Tc.Fr := evRp la G.N kap χ (fun a f => by
    have e := chiI_smul j y a f
    rw [halg a] at e
    exact e)
  have hev_k : ∀ c : Kp (recPlus h j hj) la G.N, ev (algebraMap _ (Rp (recPlus h j hj) la G.N) c) = kap c :=
    evRp_alg la G.N kap χ _
  have hev_inc : ∀ (w : WeightFamilies.Wt D j) (F : (recB h.toLawsCore).Cusp j w),
      ev (emb (recPlus h j hj) la G.N ((recPlus h j hj).inc w F)) = evI y (F : T.R j) := by
    intro w F
    exact (evRp_emb la G.N kap χ _ ((recPlus h j hj).inc w F)).trans (chiI_inc j h y w F)
  have hev_sec : ev (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec (recPlus h j hj) la G.w 0) =
      ∑ k, kap (@algebraMap (Op (recPlus h j hj) la G.N) (Kp (recPlus h j hj) la G.N) _ _ _ (Tv (recPlus h j hj) la G.N (0, k))) *
        evI y ((G.w k : (recB h.toLawsCore).Cusp j wL) : T.R j) := by
    unfold Formalism.MainNotions.Gaps.EtaleWeightGaps.sec
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Algebra.smul_def, map_mul, hev_k, hev_inc]
  have hs0' : (∑ k, kap (@algebraMap (Op (recPlus h j hj) la G.N) (Kp (recPlus h j hj) la G.N) _ _ _ (Tv (recPlus h j hj) la G.N (0, k))) *
      evR (T.Q.Xo j) T.Q.c ((G.w k : (recB h.toLawsCore).Cusp j wL) : T.R j) y₀) ≠ 0 := hs0
  have hev_s0 : ev (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec (recPlus h j hj) la G.w 0) = wchar (ex (T.Q.Dw j) (wtA wL) wL.n) t *
      ∑ k, kap (@algebraMap (Op (recPlus h j hj) la G.N) (Kp (recPlus h j hj) la G.N) _ _ _ (Tv (recPlus h j hj) la G.N (0, k))) *
        evR (T.Q.Xo j) T.Q.c ((G.w k : (recB h.toLawsCore).Cusp j wL) : T.R j) y₀ := by
    rw [hev_sec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hW wL (G.w k)]
    ring
  have hu : IsUnit (ev (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec (recPlus h j hj) la G.w 0)) :=
    IsUnit.mk0 _ (by rw [hev_s0]; exact mul_ne_zero (wchar_ne_zero _ _) hs0')
  let yV : PtV (T.Q.Xo j) T.Q.c (trivialClassCondition (T.Q.Xo j) T.Q.c) Unit (fun _ _ _ _ => True) la := PtV.mk la ho y trivial () trivial
  let yP : (extAll h j hj).Pt' la := ⟨vAtV yV, yV, rfl⟩
  refine ⟨yP, Tc, ι, hloc, hunr, ev, hu, ?_, ?_, ?_⟩
  · intro w F
    rw [extAll_vAt_inc]
    show vAtV yV (F : T.R j) = _
    exact congrArg (nval Tc.V (ep (unifO (recPlus h j hj) la G.N) ζ)) (hev_inc w F).symm
  · intro x
    obtain ⟨k, ⟨g, hg⟩, rfl⟩ := exists_weightZero_fraction_eq _ _ _ x
    rw [coe_weightZeroFraction, liftEv_frac]
    have key : ∀ (g : Rp (recPlus h j hj) la G.N) (hg : g ∈ Vw (recPlus h j hj) la G.N (addL (wt0 D j) wL k))
        (hg' : g ∈ Vw (recPlus h j hj) la G.N (addL (wt0 D j) wL k)),
        ev g * (ev (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec (recPlus h j hj) la G.w 0))⁻¹ ^ k =
          phiAt ζ Tc.Fr ι hU (addVal_map_of_unr ι hunr)
            (toOsK (recPlus h j hj) la G.w (fr0 (recPlus h j hj) la G.w k ⟨g, hg'⟩)) := by
      intro g hg
      induction hg using Submodule.span_induction with
      | mem g hg0 =>
        intro hg'
        obtain ⟨F, rfl⟩ := hg0
        have hr := hrat k F
        have hr' : phiAt ζ Tc.Fr ι hU (addVal_map_of_unr ι hunr) (toOsK (recPlus h j hj) la G.w (fr0 (recPlus h j hj) la G.w k
            ⟨emb (recPlus h j hj) la G.N ((recPlus h j hj).inc _ F), hg'⟩)) =
            evR (T.Q.Xo j) T.Q.c ((F : T.R j)) y₀ /
              (∑ k', kap (@algebraMap (Op (recPlus h j hj) la G.N) (Kp (recPlus h j hj) la G.N) _ _ _ (Tv (recPlus h j hj) la G.N (0, k'))) *
                evR (T.Q.Xo j) T.Q.c ((G.w k' : (recB h.toLawsCore).Cusp j wL) : T.R j) y₀) ^ k := hr
        rw [hr', hev_inc, hW, ex_addL, wchar_nsmul, hev_s0]
        exact mul_ringHom_units_ratio (wchar_ne_zero (ex (T.Q.Dw j) (wtA wL) wL.n) t) k
      | zero =>
        intro hg'
        have e0 : fr0 (recPlus h j hj) la G.w k ⟨0, hg'⟩ = 0 := Subtype.ext (by rw [coe_weightZeroFraction]; exact map_zero _)
        rw [e0, map_zero, map_zero, map_zero, zero_mul]
      | add a b ha hb iha ihb =>
        intro hg'
        have e1 : fr0 (recPlus h j hj) la G.w k ⟨a + b, hg'⟩ =
            fr0 (recPlus h j hj) la G.w k ⟨a, ha⟩ + fr0 (recPlus h j hj) la G.w k ⟨b, hb⟩ :=
          Subtype.ext (by rw [coe_weightZeroFraction, Subalgebra.coe_add, coe_weightZeroFraction, coe_weightZeroFraction]; exact map_add _ _ _)
        rw [e1, map_add (toOsK (recPlus h j hj) la G.w), map_add (phiAt ζ Tc.Fr ι hU (addVal_map_of_unr ι hunr)),
          map_add ev, add_mul, iha ha, ihb hb]
      | smul c a ha iha =>
        intro hg'
        have e1 : fr0 (recPlus h j hj) la G.w k ⟨c • a, hg'⟩ = c • fr0 (recPlus h j hj) la G.w k ⟨a, ha⟩ :=
          Subtype.ext (by rw [coe_weightZeroFraction, Subalgebra.coe_smul, coe_weightZeroFraction]; exact map_smul _ _ _)
        rw [e1, map_smul (toOsK (recPlus h j hj) la G.w) c,
          Algebra.smul_def c (toOsK (recPlus h j hj) la G.w (fr0 (recPlus h j hj) la G.w k ⟨a, ha⟩)),
          map_mul, ← iha ha, Algebra.smul_def c a, map_mul, hev_k, mul_assoc]
        rfl
    exact key g hg hg
  · intro w F hNZ
    rw [show ev (emb (recPlus h j hj) la G.N ((recPJ h j hj).inc w F)) = evI y (F : T.R j) from hev_inc w F, hW w F]
    refine mul_ne_zero (wchar_ne_zero _ _) ?_
    have hnat := (cusp_le_sec _ _ _ _ _ (cutR_le T.C j w F.2)).1
    rw [evR_eq_of_map hWD hnat y₀ p (ψ.comp φ') y' hm2, AlgHom.comp_apply]
    have h2 : evC hG Z (F : T.R j) = φ' ((F : T.R j) p y') := evR_eq_of_map hWD hnat (genFr hG Z) p φ' y' hm
    rw [← h2]
    exact (map_ne_zero_iff _ ψ.toRingHom.injective).2 (hNZ Z)

end Formalism.L2.Pj
end
end

