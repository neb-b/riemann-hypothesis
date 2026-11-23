module

public import Mathlib
public import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
public import Formalism.LocalToGlobal.GlobalTheory.IsResidueClassZero
public import Formalism.SharpRestriction.GrowthBounds.SmallOrderPrimes
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ThinScalesIffHostBound
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MaxVSpanSingleton
public import Formalism.LocalToGlobal.KernelLattices.ThDistC
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0077
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.StandardRankOneLatticeOfLocal
public import Formalism.LocalToGlobal.Columns.MemLocPOfSmul
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
public import Formalism.LocalToGlobal.Columns.TiedValLatG
public import Formalism.LocalToGlobal.Columns.CoefModB
public import Formalism.LocalToGlobal.KernelLattices.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0071
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0081
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0082
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0072

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.BadCharacterBound
section
noncomputable section

namespace GlobalTheory.EX

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory NumberField


open Classical in
def BadOfBase (B : Arith.Base) (h : ℕ → B.H) (Cb : ℝ) : Prop :=
  let PR := (Finset.range ⌈B.sc.X'⌉₊).filter (fun p =>
    p.Prime ∧ B.IsResidueClassZero p ∧ B.sc.x ^ (B.sc.eps / 4) ≤ (addOrderOf (h p) : ℝ))
  ∑ p ∈ PR, Real.log p / p *
      ((B.TT.filter (fun t => ¬ Arith.Loc.Good B (h p) (Arith.bsH (Arith.Loc.stepP B (h p) p) t))).card : ℝ) ≤
    4 * (Cb * B.sc.x ^ (-2 : ℝ)) * B.sc.delta1 * B.R.n * ∑ p ∈ PR, Real.log p / p

theorem badOK_iff_badOfBase {R : Ranks} (s : Scale) (Cb : ℝ) (H : Host R) :
    BadOK s Cb H ↔ BadOfBase (baseOf s 0 0 H) (hPH H) Cb := Iff.rfl

theorem chBad_iff_badOfBase {D : D7} {L : SizeData₂ D} (X : G.Inst D L) (hX : ∀ h t, X.bs h t = Arith.bsH h t) (Cb : ℝ) :
    ChBad_at X Cb ↔ BadOfBase (baseOf L.sc 0 0 D.host) (G.hP D) Cb := by
  have hb : X.bs = fun h t => Arith.bsH h t := funext fun h => funext fun t => hX h t
  unfold ChBad_at badTops
  obtain ⟨bs, h1, h2, off, h3, h4, h5, kap, ep⟩ := X
  dsimp only at hb
  subst hb
  exact Iff.rfl

theorem badOfBase_of_host {R R' : Ranks} (hR : R' = R) (s : Scale) (H : Host R) (H' : Host R')
    (h : ℕ → R.A) (h' : ℕ → R'.A) (Cb : ℝ)
    (hT : H'.TT.image Formalism.HC.Frame.A.val = H.TT.image Formalism.HC.Frame.A.val) (hq : H'.q = H.q) (hd : H'.d = H.d)
    (hc : H'.cls = H.cls)
    (hh : ∀ l, (h' l).val = (h l).val) (hb : BadOfBase (baseOf s 0 0 H) h Cb) :
    BadOfBase (baseOf s 0 0 H') h' Cb := by
  subst hR
  have hT' : H'.TT = H.TT := Finset.image_injective (Formalism.HC.Frame.A.val_injective _) hT
  have hh' : h' = h := funext fun l => Formalism.HC.Frame.A.val_injective _ (hh l)
  subst hh'
  unfold baseOf at hb ⊢
  rw [hT', hq, hd, hc]
  exact hb

theorem chBad_of_from : ∀ (C : FC) (p : Pt C) (R : Ranks) (H : Host R) (a b : R.A → ℤ) (M : ℕ)
    (c : Fin M → Fin (R.k - 2) → Bool) (u0 : ℕ) (Cb : ℝ),
    p.From H a b c u0 → CanonInst p.ta.Gx → BadOK p.L.sc Cb H → ChBad_at p.ta.Gx Cb := by
  intro C p R H a b M c u0 Cb hF hC hB
  have hc := hF.cls_eq
  obtain ⟨hR, hT, -, hq, hd, -, -, -, -, -, hh, -⟩ := hF
  exact (chBad_iff_badOfBase _ hC.1 Cb).2
    (badOfBase_of_host hR p.L.sc H p.D.host (hPH H) (G.hP p.D) Cb hT hq hd hc hh ((badOK_iff_badOfBase _ _ _).1 hB))

end GlobalTheory.EX

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ConjPConjP
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions GlobalTheory.CharVal GlobalTheory.IndefiniteRowSideFullHecke.CharacterValuation
open nonZeroDivisors
noncomputable section
namespace GlobalTheory.CharVal.Vp
variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem conjP_conjP' (P : HeightOneSpectrum (𝓞 E)) : conjPrime₂ (conjPrime₂ P) = P := by
  ext x
  rw [mem_conjP, mem_conjP, cO_cO]

omit [StarRing E] in
theorem ne0 (P : HeightOneSpectrum (𝓞 E)) : (P.asIdeal : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 :=
  FractionalIdeal.coeIdeal_ne_zero.2 P.ne_bot

omit [StarRing E] in
theorem maxV_self (P : HeightOneSpectrum (𝓞 E)) :
    MaxV P ((P.asIdeal : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) E) (WithZero.exp (-1 : ℤ)) := by
  constructor
  · intro a ha
    obtain ⟨r, hr, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 ha
    rw [HeightOneSpectrum.valuation_of_algebraMap]
    have := (P.intValuation_le_pow_iff_mem r 1).2 (by simpa using hr)
    simpa using this
  · obtain ⟨r, hr⟩ := P.intValuation_exists_uniformizer
    refine ⟨algebraMap _ _ r, (FractionalIdeal.mem_coeIdeal _).2 ⟨r, ?_, rfl⟩, ?_⟩
    · have := (P.intValuation_le_pow_iff_mem r 1).1 (by simpa using hr.le)
      simpa using this
    · rw [HeightOneSpectrum.valuation_of_algebraMap, hr]

omit [StarRing E] in
theorem maxV_ne (Q P : HeightOneSpectrum (𝓞 E)) (h : Q ≠ P) :
    MaxV Q ((P.asIdeal : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) E) 1 := by
  constructor
  · intro a ha
    obtain ⟨r, hr, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 ha
    exact Q.valuation_le_one r
  · have : ¬ P.asIdeal ≤ Q.asIdeal := fun hle =>
      h (HeightOneSpectrum.ext (P.isMaximal.eq_of_le Q.isPrime.ne_top hle).symm)
    obtain ⟨r, hr, hr'⟩ := SetLike.not_le_iff_exists.1 this
    exact ⟨algebraMap _ _ r, (FractionalIdeal.mem_coeIdeal _).2 ⟨r, hr, rfl⟩,
      (HeightOneSpectrum.valuation_eq_one_iff_notMem Q).2 hr'⟩

omit [StarRing E] in
theorem maxV_inv {Q P : HeightOneSpectrum (𝓞 E)} {γ : WithZero (Multiplicative ℤ)} (h0 : γ ≠ 0)
    (h : MaxV Q ((P.asIdeal : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) E) γ) :
    MaxV Q (((P.asIdeal : FractionalIdeal (𝓞 E)⁰ E)⁻¹ : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) E) γ⁻¹ :=
  h.inv h0 (by rw [← FractionalIdeal.coe_mul, mul_inv_cancel₀ (ne0 P), FractionalIdeal.coe_one])

theorem mem_vp (P : HeightOneSpectrum (𝓞 E)) (x : E) :
    x ∈ vpIdeal P ↔ ∀ r ∈ (conjPrime₂ P).asIdeal, ∃ s ∈ P.asIdeal, algebraMap _ E s = x * algebraMap _ E r := by
  unfold vpIdeal
  rw [← div_eq_mul_inv, FractionalIdeal.mem_coe, FractionalIdeal.mem_div_iff_of_ne_zero (ne0 _)]
  constructor
  · intro h r hr
    exact (FractionalIdeal.mem_coeIdeal _).1 (h _ ((FractionalIdeal.mem_coeIdeal _).2 ⟨r, hr, rfl⟩))
  · intro h y hy
    obtain ⟨r, hr, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hy
    exact (FractionalIdeal.mem_coeIdeal _).2 (h r hr)

theorem star_mem_vp (P : HeightOneSpectrum (𝓞 E)) (x : E) (h : x ∈ vpIdeal P) : star x ∈ vpIdeal (conjPrime₂ P) := by
  rw [mem_vp] at h ⊢
  intro r hr
  rw [conjP_conjP'] at hr
  obtain ⟨s, hs, e⟩ := h (cO E r) (by rwa [mem_conjP, cO_cO])
  refine ⟨cO E s, by rwa [mem_conjP, cO_cO], ?_⟩
  have e1 : algebraMap _ E (cO E s) = star (algebraMap _ E s) := rfl
  have e2 : algebraMap _ E (cO E r) = star (algebraMap _ E r) := rfl
  rw [e1, e, e2, star_mul, star_star, mul_comm]

theorem detLat_vp (P : HeightOneSpectrum (𝓞 E)) : detLat (vpLat P) = vpIdeal P := by
  unfold detLat
  rw [← Submodule.span_eq (vpIdeal P)]
  congr 1
  ext x
  constructor
  · rintro ⟨A, hA, rfl⟩
    have := hA _ (single_mem_stdLat (E := E) (0 : Fin 1) 1)
    rw [Matrix.det_fin_one]
    simpa [vpLat, Matrix.mulVec_single] using this
  · intro hx
    refine ⟨Matrix.of fun _ _ => x, fun v hv => ?_, by simp⟩
    obtain ⟨r, hr⟩ := (mem_stdLat v).1 hv 0
    have : (Matrix.of fun _ _ => x : Matrix (Fin 1) (Fin 1) E).mulVec v 0 = r • x := by
      simp [Matrix.mulVec, dotProduct, ← hr, Algebra.smul_def, mul_comm]
    show (Matrix.of fun _ _ => x : Matrix (Fin 1) (Fin 1) E).mulVec v 0 ∈ vpIdeal P
    rw [this]
    exact (vpIdeal P).smul_mem r hx

theorem vp_main : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E)), P ≠ conjPrime₂ P → (∃ J : Submodule (𝓞 E) E, (∀ x, x ∈ J ↔ star x ∈ vpIdeal P) ∧ vpIdeal P * J = 1) ∧ MaxV P (vpIdeal P) (WithZero.exp (-1 : ℤ)) ∧ MaxV (conjPrime₂ P) (vpIdeal P) (WithZero.exp (1 : ℤ)) ∧ (∀ Q : HeightOneSpectrum (𝓞 E), Q ≠ P → Q ≠ conjPrime₂ P → MaxV Q (vpIdeal P) 1) ∧ detLat (vpLat P) = vpIdeal P := by
  intro E _ _ _ P hP
  refine ⟨⟨vpIdeal (conjPrime₂ P), fun x => ⟨fun h => ?_, fun h => ?_⟩, ?_⟩, ?_, ?_, fun Q h1 h2 => ?_, detLat_vp P⟩
  · have := star_mem_vp _ _ h
    rwa [conjP_conjP'] at this
  · simpa using star_mem_vp _ _ h
  · unfold vpIdeal
    rw [conjP_conjP', ← FractionalIdeal.coe_mul, mul_assoc, inv_mul_cancel_left₀ (ne0 _), mul_inv_cancel₀ (ne0 _),
      FractionalIdeal.coe_one]
  · have := (maxV_self P).mul (maxV_inv one_ne_zero (maxV_ne P _ hP))
    rw [inv_one, mul_one, ← FractionalIdeal.coe_mul] at this
    exact this
  · have := (maxV_ne _ P hP.symm).mul (maxV_inv WithZero.exp_ne_zero (maxV_self (conjPrime₂ P)))
    rw [one_mul, ← WithZero.exp_neg, neg_neg, ← FractionalIdeal.coe_mul] at this
    exact this
  · have := (maxV_ne Q P h1).mul (maxV_inv one_ne_zero (maxV_ne Q _ h2))
    rw [inv_one, mul_one, ← FractionalIdeal.coe_mul] at this
    exact this

end GlobalTheory.CharVal.Vp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DetIdNormOneMul
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions

noncomputable section

namespace GlobalTheory.RelDetIdeal

open GlobalTheory.CharValCompare GlobalTheory.Survey.StandardDeterminantUnits

section General

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

def relDet (L L' : Submodule (𝓞 E) (Sp E n)) : Submodule (𝓞 E) E :=
  Submodule.span (𝓞 E) {x | ∃ A : Matrix (Fin n) (Fin n) E, (∀ v ∈ L, A.mulVec v ∈ L') ∧ x = A.det}

omit [StarRing E] in
theorem val_pos {P : HeightOneSpectrum (𝓞 E)} {a : E} (h : a ≠ 0) : 0 < P.valuation E a :=
  zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 h)

omit [StarRing E] in
theorem gen_mul {P : HeightOneSpectrum (𝓞 E)} {I J : Submodule (𝓞 E) E} {a b : E} (ha : Gen P I a) (hb : Gen P J b) :
    Gen P (I * J) (a * b) := by
  refine gen_of (mul_ne_zero ha.1 hb.1) ?_ fun x hx => ?_
  · obtain ⟨s, hs, h1⟩ := (ha.2 a).2 le_rfl
    obtain ⟨t, ht, h2⟩ := (hb.2 b).2 le_rfl
    refine ⟨s * t, P.asIdeal.primeCompl.mul_mem hs ht, ?_⟩
    rw [← smul_mul_smul_comm]
    exact Submodule.mul_mem_mul h1 h2
  · refine Submodule.mul_induction_on hx (fun m hm k hk => ?_) (fun x y hx hy => Valuation.map_add_le _ hx hy)
    rw [map_mul, map_mul]
    exact mul_le_mul' ((ha.2 m).1 (ThetaMove.mem_localization_of_mem P hm)) ((hb.2 k).1 (ThetaMove.mem_localization_of_mem P hk))

omit [StarRing E] in
theorem eq_of_gen {I J : Submodule (𝓞 E) E} (a b : HeightOneSpectrum (𝓞 E) → E) (ha : ∀ P, Gen P I (a P)) (hb : ∀ P, Gen P J (b P))
    (h : ∀ P : HeightOneSpectrum (𝓞 E), P.valuation E (a P) = P.valuation E (b P)) : I = J := by
  apply le_antisymm
  · intro x hx
    exact ThetaMove.mem_of_locP fun P => ((hb P).2 x).2 (h P ▸ ((ha P).2 x).1 (ThetaMove.mem_localization_of_mem P hx))
  · intro x hx
    exact ThetaMove.mem_of_locP fun P => ((ha P).2 x).2 ((h P).symm ▸ ((hb P).2 x).1 (ThetaMove.mem_localization_of_mem P hx))

omit [StarRing E] in
theorem gen_one (P : HeightOneSpectrum (𝓞 E)) : Gen P (1 : Submodule (𝓞 E) E) 1 :=
  ⟨one_ne_zero, fun x => by rw [mem_localization_one, intAt_iff, map_one]⟩

theorem gen_bar {P : HeightOneSpectrum (𝓞 E)} {I : Submodule (𝓞 E) E} {a : E} (ha : Gen (conjPrime₂ P) I a) :
    Gen P (barI I) (star a) := by
  have h0 : star a ≠ 0 := star_ne_zero.2 ha.1
  refine gen_of h0 ?_ fun x hx => ?_
  · obtain ⟨s, hs, h1⟩ := (ha.2 a).2 le_rfl
    refine ⟨cO E s, hs, ?_⟩
    show star (cO E s • star a) ∈ I
    rwa [Algebra.smul_def, algebraMap_cO, star_mul', star_star, star_star, ← Algebra.smul_def]
  · have h2 := (ha.2 (star x)).1 (ThetaMove.mem_localization_of_mem _ hx)
    have h3 : IntAt (conjPrime₂ P) (star x / a) := by
      rw [intAt_iff, map_div₀]
      exact div_le_one_of_le₀ h2 zero_le
    have h4 := intAt_iff.1 (intAt_star h3)
    rwa [conjP_conjP, star_div₀, star_star, map_div₀, div_le_one₀ (val_pos h0)] at h4

theorem gen_relDet {P : HeightOneSpectrum (𝓞 E)} {L L' : Submodule (𝓞 E) (Sp E n)} (hL : L.FG) {f f' : Sp E n ≃ₗ[E] Sp E n}
    (hf : IsFr P L f) (hf' : IsFr P L' f') : Gen P (relDet L L') (dt f' / dt f) := by
  classical
  refine gen_of (div_ne_zero (dt_ne _) (dt_ne _)) ?_ ?_
  · let g : Sp E n →ₗ[E] Sp E n := (f' : Sp E n →ₗ[E] Sp E n) ∘ₗ (f.symm : Sp E n →ₗ[E] Sp E n)
    have hg : ∀ v ∈ L, g v ∈ localization₂ P.asIdeal L' := fun v hv =>
      (hf' _).2 ((hf _).1 (by simpa using ThetaMove.mem_localization_of_mem P hv))
    obtain ⟨S, rfl⟩ := hL
    have : ∀ i : S, ∃ s : 𝓞 E, s ∉ P.asIdeal ∧ s • g i ∈ L' := fun i => hg i (Submodule.subset_span i.2)
    choose s hs hs' using this
    have hp : ∏ i, s i ∉ P.asIdeal := fun hm => by
      obtain ⟨y, _, h⟩ := (Ideal.IsPrime.prod_mem_iff (hp := P.isPrime)).1 hm
      exact hs y h
    refine ⟨(∏ i, s i) ^ n, P.asIdeal.primeCompl.pow_mem hp n, Submodule.subset_span
      ⟨algebraMap (𝓞 E) E (∏ i, s i) • LinearMap.toMatrix' g, fun v hv => ?_, ?_⟩⟩
    · rw [Matrix.smul_mulVec, LinearMap.toMatrix'_mulVec, algebraMap_smul]
      induction hv using Submodule.span_induction with
      | mem y hy =>
        rw [← Finset.prod_erase_mul _ s (Finset.mem_univ ⟨y, hy⟩), mul_smul]
        exact L'.smul_mem _ (hs' ⟨y, hy⟩)
      | zero => simp
      | add a b _ _ ha hb => rw [map_add (f := _), smul_add]; exact add_mem ha hb
      | smul c a _ ha =>
        rw [← algebraMap_smul E c a, map_smul, algebraMap_smul, smul_comm]
        exact L'.smul_mem _ ha
    · have e : LinearMap.det g = dt f' / dt f := by
        rw [eq_div_iff (dt_ne _), LinearMap.det_comp, dt_eq, dt_eq, mul_assoc, LinearEquiv.det_symm_mul_det, mul_one]
      rw [Matrix.det_smul, LinearMap.det_toMatrix', e, Algebra.smul_def, map_pow, Fintype.card_fin]
  · intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨A, hA, rfl⟩ := hy
      have h1 := val_det_le_one (P := P)
        ((f'.symm : Sp E n →ₗ[E] Sp E n) ∘ₗ Matrix.toLin' A ∘ₗ (f : Sp E n →ₗ[E] Sp E n)) fun x hx => by
        rw [← hf']
        obtain ⟨s, hs, hx⟩ := (hf x).2 hx
        refine ⟨s, hs, ?_⟩
        have := hA _ hx
        rw [← algebraMap_smul E s (f x), Matrix.mulVec_smul, algebraMap_smul] at this
        simpa using this
      have h2 : A.det = dt f' / dt f *
          LinearMap.det ((f'.symm : Sp E n →ₗ[E] Sp E n) ∘ₗ Matrix.toLin' A ∘ₗ (f : Sp E n →ₗ[E] Sp E n)) := by
        have h3 := LinearEquiv.det_mul_det_symm f'
        have h4 := dt_ne f
        rw [LinearMap.det_comp, LinearMap.det_comp, LinearMap.det_toLin', ← dt_eq f]
        rw [← dt_eq f'] at h3
        field_simp
        linear_combination (-A.det) * h3
      rw [h2, map_mul]
      exact mul_le_of_le_one_right' h1
    | zero => simp
    | add a b _ _ ha hb => exact Valuation.map_add_le _ ha hb
    | smul c a _ ha =>
      rw [Algebra.smul_def, map_mul]
      exact le_trans (mul_le_of_le_one_left' (P.valuation_le_one (K := E) c)) ha

theorem relDet_mul {L L' L'' : Submodule (𝓞 E) (Sp E n)} (hL : Submodule.IsFullLattice E L)
    (hL' : Submodule.IsFullLattice E L') (hL'' : Submodule.IsFullLattice E L'') :
    relDet L L'' = relDet L L' * relDet L' L'' := by
  choose f hf using fun P => (DetChrL.frame_exists P hL : ∃ f, IsFr P L f)
  choose f' hf' using fun P => (DetChrL.frame_exists P hL' : ∃ f, IsFr P L' f)
  choose f'' hf'' using fun P => (DetChrL.frame_exists P hL'' : ∃ f, IsFr P L'' f)
  refine eq_of_gen _ _ (fun P => gen_relDet hL.fg (hf P) (hf'' P))
    (fun P => gen_mul (gen_relDet hL.fg (hf P) (hf' P)) (gen_relDet hL'.fg (hf' P) (hf'' P))) fun P => ?_
  congr 1
  have := dt_ne (f P)
  have := dt_ne (f' P)
  field_simp

theorem normOne_relDet {L L' : Submodule (𝓞 E) (Sp E n)} (hL : IsSdLat L) (hL' : IsSdLat L') : NormOne (relDet L L') := by
  refine ⟨barI (relDet L L'), fun _ => Iff.rfl, ?_⟩
  choose f hf using fun P => exists_isFr P hL
  choose f' hf' using fun P => exists_isFr P hL'
  have hg := fun P => gen_relDet hL.1.fg (hf P) (hf' P)
  refine eq_of_gen _ _ (fun P => gen_mul (hg P) (gen_bar (hg (conjPrime₂ P)))) gen_one fun P => ?_
  have h1 := val_dual hL (hf (conjPrime₂ P)) (f' := f P) (by rw [conjP_conjP]; exact hf P)
  have h2 := val_dual hL' (hf' (conjPrime₂ P)) (f' := f' P) (by rw [conjP_conjP]; exact hf' P)
  rw [conjP_conjP] at h1 h2
  rw [star_div₀, div_mul_div_comm, map_div₀, mul_comm (dt _), mul_comm (dt _), h1, h2, map_one, div_one]

theorem isSdLat_of {L : Submodule (𝓞 E) (Sp E n)} (h : IsSDLat E n L) : IsSdLat L := by
  refine ⟨Submodule.IsLattice.of_fg E h.1, ?_⟩
  ext x
  rw [mem_dual, h.2.2]
  refine forall₂_congr fun y _ => ?_
  rw [Submodule.mem_one]
  rfl

end General

theorem detId_normOne_mul (D : D7) (n : ℕ) (L L' L'' : Submodule (𝓞 D.host.E) (Fin n → D.host.E))
    (hL : StandardLatticesGL3.SD D L) (hL' : StandardLatticesGL3.SD D L') (hL'' : StandardLatticesGL3.SD D L'') :
    TaylorLogMetric.N1 D (TaylorLogMetric.detId D L L') ∧ TaylorLogMetric.detId D L L'' = TaylorLogMetric.detId D L L' * TaylorLogMetric.detId D L' L'' := by
  letI := D.host.cmStar
  have hs : ∀ x : D.host.E, star x = D.host.conj x := bridge_star_holds D.R D.host
  have hfull {N : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} (h : IsSDLat D.host.E n N) :
      Submodule.IsFullLattice D.host.E N :=
    { toIsLattice := Submodule.IsLattice.of_fg _ h.1
      span_eq_top := h.2.1 }
  refine ⟨?_, relDet_mul (hfull hL) (hfull hL') (hfull hL'')⟩
  obtain ⟨J, hJ, e⟩ := normOne_relDet (isSdLat_of hL) (isSdLat_of hL')
  exact ⟨J, fun x => by rw [hJ, hs]; rfl, e⟩

end GlobalTheory.RelDetIdeal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsLocalBasisSnocOfLocalBasis
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2 Matrix

noncomputable section

namespace GlobalTheory.LocBasisSnoc

variable {E : Type} [Field E] {n : ℕ}

def blk (A : Matrix (Fin n) (Fin n) E) (c : E) : Matrix (Fin (n + 1)) (Fin (n + 1)) E :=
  Matrix.of fun i j => Fin.lastCases (Fin.lastCases c (fun _ => 0) j)
    (fun i' => Fin.lastCases 0 (fun j' => A i' j') j) i

theorem blk_mulVec_castSucc (A : Matrix (Fin n) (Fin n) E) (c : E) (x : Fin (n + 1) → E) (i : Fin n) :
    (blk A c *ᵥ x) i.castSucc = (A *ᵥ Fin.init x) i := by
  simp [blk, Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, Fin.init]

theorem blk_mulVec_last (A : Matrix (Fin n) (Fin n) E) (c : E) (x : Fin (n + 1) → E) :
    (blk A c *ᵥ x) (Fin.last n) = c * x (Fin.last n) := by
  simp [blk, Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc]

theorem blk_mulVec_ext {P Q : Matrix (Fin (n + 1)) (Fin (n + 1)) E} (h : ∀ x, P *ᵥ x = Q *ᵥ x) : P = Q :=
  Matrix.ext_of_mulVec_single fun j => h _

theorem blk_mul (A A' : Matrix (Fin n) (Fin n) E) (c c' : E) :
    blk A c * blk A' c' = blk (A * A') (c * c') := by
  refine blk_mulVec_ext fun x => ?_
  rw [← Matrix.mulVec_mulVec]
  funext i
  refine Fin.lastCases ?_ (fun i => ?_) i
  · rw [blk_mulVec_last, blk_mulVec_last, blk_mulVec_last, mul_assoc]
  · rw [blk_mulVec_castSucc, blk_mulVec_castSucc, ← Matrix.mulVec_mulVec]
    congr 2
    funext k
    exact blk_mulVec_castSucc _ _ _ _

theorem blk_one : blk (1 : Matrix (Fin n) (Fin n) E) 1 = 1 := by
  refine blk_mulVec_ext fun x => ?_
  funext i
  refine Fin.lastCases ?_ (fun i => ?_) i
  · rw [blk_mulVec_last, one_mul, Matrix.one_mulVec]
  · rw [blk_mulVec_castSucc, Matrix.one_mulVec, Matrix.one_mulVec]
    rfl

end GlobalTheory.LocBasisSnoc


open GlobalTheory.LocBasisSnoc in
theorem GlobalTheory.isLocBasis_snoc : ∀ {E : Type} [Field E] [NumberField E] {N n : ℕ} (hN : N = n + 1) (t : E), t ≠ 0 → ∀ (L : Submodule (𝓞 E) (Fin N → E)) (L' : Submodule (𝓞 E) (Fin n → E)), (∀ x, x ∈ L ↔ iniH hN x ∈ L' ∧ t * x (Br.iL hN) ∈ (1 : Submodule (𝓞 E) E)) → ∀ (p : ℕ) (B' : GL (Fin n) E), p.Prime → IsLocBasis p (L' : Set (Fin n → E)) B' → ∃ B : GL (Fin N) E, (∀ x, iniH hN ((B : Matrix (Fin N) (Fin N) E) *ᵥ x) = (B' : Matrix (Fin n) (Fin n) E) *ᵥ iniH hN x) ∧ (∀ x, t * ((B : Matrix (Fin N) (Fin N) E) *ᵥ x) (Br.iL hN) = x (Br.iL hN)) ∧ IsLocBasis p (L : Set (Fin N → E)) B := by
  intro E _ _ N n hN t ht L L' hL p B' hp hB'
  subst hN
  let B : GL (Fin (n + 1)) E :=
    ⟨blk (B' : Matrix (Fin n) (Fin n) E) t⁻¹, blk ((B'⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) t,
      by rw [blk_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, inv_mul_cancel₀ ht, blk_one],
      by rw [blk_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_inv_cancel₀ ht, blk_one]⟩
  have hini : ∀ y : Fin (n + 1) → E, iniH rfl y = Fin.init y := fun y => rfl
  have hlast : (Br.iL (rfl : n + 1 = n + 1)) = Fin.last n := rfl
  refine ⟨B, fun x => ?_, fun x => ?_, ?_⟩
  · rw [hini, hini]
    funext i
    exact blk_mulVec_castSucc _ _ _ _
  · rw [hlast]
    show t * (blk _ t⁻¹ *ᵥ x) (Fin.last n) = _
    rw [blk_mulVec_last, ← mul_assoc, mul_inv_cancel₀ ht, one_mul]
  · intro x
    have hinv : ((B⁻¹ : GL (Fin (n + 1)) E) : Matrix _ _ E) = blk ((B'⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) t := rfl
    rw [hinv]
    set R := (algebraMap (𝓞 E) E).range
    have hR : ∀ (s : ℕ) {y : E}, y ∈ R → (s : E) * y ∈ R := fun s y hy => R.mul_mem (natCast_mem R s) hy
    have key : ∀ s : ℕ, (∀ a, (s : E) * (blk ((B'⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) t *ᵥ x) a ∈ R) ↔
        (∀ a, (s : E) * (((B'⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ Fin.init x) a ∈ R) ∧
          (s : E) * (t * x (Fin.last n)) ∈ R := by
      intro s
      constructor
      · intro h
        refine ⟨fun a => ?_, ?_⟩
        · have := h a.castSucc
          rwa [blk_mulVec_castSucc] at this
        · have := h (Fin.last n)
          rwa [blk_mulVec_last] at this
      · rintro ⟨h1, h2⟩ a
        refine Fin.lastCases ?_ (fun i => ?_) a
        · rw [blk_mulVec_last]; exact h2
        · rw [blk_mulVec_castSucc]; exact h1 i
    have memL : ∀ s : ℕ, (s : E) • x ∈ L ↔ (s : E) • Fin.init x ∈ L' ∧ (s : E) * (t * x (Fin.last n)) ∈ R := by
      intro s
      rw [hL, hini, hlast, Submodule.mem_one]
      have e : t * ((s : E) • x) (Fin.last n) = (s : E) * (t * x (Fin.last n)) := by
        rw [Pi.smul_apply, smul_eq_mul, mul_left_comm]
      rw [e]
      rfl
    have hnd : ∀ a b : ℕ, ¬ p ∣ a → ¬ p ∣ b → ¬ p ∣ a * b := fun a b ha hb h =>
      (hp.dvd_mul.mp h).elim ha hb
    have hB := hB' (Fin.init x)
    constructor
    · rintro ⟨s, hs, hx⟩
      obtain ⟨h1, h2⟩ := (memL s).mp hx
      obtain ⟨s', hs', h3⟩ := hB.mp ⟨s, hs, h1⟩
      refine ⟨s * s', hnd _ _ hs hs', (key _).mpr ⟨fun a => ?_, ?_⟩⟩
      · rw [Nat.cast_mul, mul_assoc]; exact hR s (h3 a)
      · rw [Nat.cast_mul, mul_comm (s : E), mul_assoc]; exact hR s' h2
    · rintro ⟨s, hs, h⟩
      obtain ⟨h1, h2⟩ := (key s).mp h
      obtain ⟨s', hs', h3⟩ := hB.mpr ⟨s, hs, h1⟩
      refine ⟨s * s', hnd _ _ hs hs', (memL _).mpr ⟨?_, ?_⟩⟩
      · rw [Nat.cast_mul, mul_smul, Nat.cast_smul_eq_nsmul]
        exact nsmul_mem h3 s
      · rw [Nat.cast_mul, mul_comm (s : E), mul_assoc]; exact hR s' h2
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExplicitChoiceSizeEta
section
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem szRow_sizeEta : SzRow (fun _ _ L => SizeEta L) := by
  refine SzRow.imp (SzRow.and szRow_eta_bounds (SzRow.and szRow_eta_le_w szRow_rbS)) ?_
  rintro C cD ch D L - - ⟨⟨h1, h2, h3, h4, h5⟩, ⟨h6, h7, h8, h9⟩, h10⟩
  exact ⟨h3, h1, h2, h4, h5, h6, h7, h8, h10⟩

end GlobalTheory.EX
end

