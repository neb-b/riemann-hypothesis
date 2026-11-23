module

public import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
public import GroundTheory.AutomorphicForms.GL2.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0595
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0099
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0037
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LevelLossDegreeBounds
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockDegreeGapBound
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0715
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOfBalanced
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0227

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonzeroSquaresSumEquivIcoModFour
section
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.SqSplit

theorem natCast_sub_eq_neg {p n : ℕ} (h : n ≤ p) : ((p - n : ℕ) : ZMod p) = -((n : ℕ) : ZMod p) := by
  rw [Nat.cast_sub h, ZMod.natCast_self, zero_sub]

theorem neg_one_not_isSquare {p : ℕ} [Fact p.Prime] (h3 : p % 4 = 3) : ¬ IsSquare (-1 : ZMod p) := by
  rw [ZMod.exists_sq_eq_neg_one_iff]; omega

theorem ringChar_ne_two {p : ℕ} [Fact p.Prime] (h3 : p % 4 = 3) : ringChar (ZMod p) ≠ 2 := by
  rw [ZMod.ringChar_zmod_n]; omega

theorem isSquare_neg_of_not {p : ℕ} [Fact p.Prime] (h3 : p % 4 = 3) {a : ZMod p} (ha : a ≠ 0)
    (hs : ¬ IsSquare a) : IsSquare (-a) := by
  have hc := ringChar_ne_two h3
  have h1 : quadraticChar (ZMod p) a = -1 := (quadraticChar_neg_one_iff_not_isSquare).2 hs
  have h2 : quadraticChar (ZMod p) (-1) = -1 :=
    (quadraticChar_neg_one_iff_not_isSquare).2 (neg_one_not_isSquare h3)
  have hna : -a ≠ 0 := neg_ne_zero.2 ha
  rw [← quadraticChar_one_iff_isSquare hna, neg_eq_neg_one_mul, map_mul, h1, h2]; norm_num

theorem not_both {p : ℕ} [Fact p.Prime] (h3 : p % 4 = 3) {a : ZMod p} (ha : a ≠ 0)
    (h1 : IsSquare a) (h2 : IsSquare (-a)) : False := by
  apply neg_one_not_isSquare h3
  have : (-1 : ZMod p) = -a * a⁻¹ := by rw [neg_mul, mul_inv_cancel₀ ha]
  rw [this]; exact h2.mul h1.inv

end GlobalTheory.SqSplit

open GlobalTheory.SqSplit in
theorem GlobalTheory.sq_sum_equiv_Ico : ∀ (p : ℕ), p.Prime → p % 4 = 3 → ∃ e : Sq p ⊕ Sq p ≃ (Finset.Ico 1 p : Finset ℕ), ∀ k : Sq p, ((e (Sum.inl k) : ℕ) = (k.1 : ℕ)) ∧ ((e (Sum.inr k) : ℕ) = p - (k.1 : ℕ)) := by
  intro p hp h3
  haveI : Fact p.Prime := ⟨hp⟩
  have pos : ∀ k : Sq p, 1 ≤ (k.1 : ℕ) := by
    intro k
    rcases Nat.eq_zero_or_pos (k.1 : ℕ) with h | h
    · exact absurd (by rw [h]; simp) k.2.1
    · exact h
  let f : Sq p ⊕ Sq p → (Finset.Ico 1 p : Finset ℕ) := Sum.elim
    (fun k => ⟨(k.1 : ℕ), Finset.mem_Ico.2 ⟨pos k, k.1.2⟩⟩)
    (fun k => ⟨p - (k.1 : ℕ), Finset.mem_Ico.2 ⟨by have := k.1.2; omega, by have := pos k; omega⟩⟩)
  have hf : Function.Bijective f := by
    constructor
    · rintro (a | a) (b | b) hab <;> simp only [f, Sum.elim_inl, Sum.elim_inr, Subtype.mk.injEq] at hab
      · exact congrArg Sum.inl (Subtype.ext (Fin.ext hab))
      · exfalso
        have hb := b.1.2
        have e1 : ((a.1 : ℕ) : ZMod p) = -((b.1 : ℕ) : ZMod p) := by
          rw [hab, natCast_sub_eq_neg hb.le]
        exact not_both h3 b.2.1 b.2.2 (e1 ▸ a.2.2)
      · exfalso
        have ha := a.1.2
        have e1 : ((b.1 : ℕ) : ZMod p) = -((a.1 : ℕ) : ZMod p) := by
          rw [← hab, natCast_sub_eq_neg ha.le]
        exact not_both h3 a.2.1 a.2.2 (e1 ▸ b.2.2)
      · have ha := a.1.2; have hb := b.1.2
        exact congrArg Sum.inr (Subtype.ext (Fin.ext (by omega)))
    · rintro ⟨n, hn⟩
      obtain ⟨h1, h2⟩ := Finset.mem_Ico.1 hn
      have hn0 : ((n : ℕ) : ZMod p) ≠ 0 := by
        rw [Ne, ZMod.natCast_eq_zero_iff]
        intro hd; exact absurd (Nat.le_of_dvd (by omega) hd) (by omega)
      by_cases hs : IsSquare ((n : ℕ) : ZMod p)
      · exact ⟨Sum.inl ⟨⟨n, h2⟩, hn0, hs⟩, rfl⟩
      · have hm : ((p - n : ℕ) : ZMod p) = -((n : ℕ) : ZMod p) := natCast_sub_eq_neg h2.le
        refine ⟨Sum.inr ⟨⟨p - n, by omega⟩, ?_, ?_⟩, ?_⟩
        · simp only; rw [hm]; exact neg_ne_zero.2 hn0
        · simp only; rw [hm]; exact isSquare_neg_of_not h3 hn0 hs
        · simp only [f, Sum.elim_inr]; apply Subtype.ext; simp only; omega
  exact ⟨Equiv.ofBijective f hf, fun k => ⟨rfl, rfl⟩⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormEqOfValuedEq
section
open NumberField IsDedekindDomain Matrix GroundTheory.Global GroundTheory.Automorphic.GJMatrix GlobalTheory.HenQ
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc)
open scoped nonZeroDivisors

noncomputable section
namespace GlobalTheory.HenQ
variable {K : Type} [Field K] [NumberField K]

theorem valued_det_of_KGL {w : HeightOneSpectrum (𝓞 K)} {n : ℕ} {g : GL (Fin n) (w.adicCompletion K)}
    (hg : g ∈ GlobalTheory.LFun.KGL w (n := n)) : Valued.v g.val.det = 1 := by
  obtain ⟨g0, rfl⟩ := hg
  set O := (w.adicCompletionIntegers K).toSubring
  have hd : ∀ h : GL (Fin n) O, ((Formalism.UG.bc O.subtype h).val.det) = ((h.val.det : O) : w.adicCompletion K) := by
    intro h
    exact (RingHom.map_det O.subtype h.val).symm
  have h1 : Valued.v ((g0.val.det : O) : w.adicCompletion K) ≤ 1 := (g0.val.det).2
  have h2 : Valued.v (((g0⁻¹).val.det : O) : w.adicCompletion K) ≤ 1 := ((g0⁻¹).val.det).2
  have h3 : ((g0.val.det : O) : w.adicCompletion K) * (((g0⁻¹).val.det : O) : w.adicCompletion K) = 1 := by
    rw [← Subring.coe_mul, ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
    rfl
  have h4 := congrArg Valued.v h3
  rw [map_mul, map_one] at h4
  rw [hd]
  refine le_antisymm h1 ?_
  calc (1 : WithZero (Multiplicative ℤ)) = _ := h4.symm
    _ ≤ Valued.v ((g0.val.det : O) : w.adicCompletion K) * 1 := mul_le_mul' le_rfl h2
    _ = _ := mul_one _

end GlobalTheory.HenQ
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalisedIsoPowerBundleRatioUnitEqOne
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniq

noncomputable section

namespace GlobalTheory.HomFixUnit

theorem ratio_unit_eq_one : ∀ (Rg : Type) [CommRing Rg] (A B : Over (Sp Rg)) [GrpObj A] [GrpObj B] (L : LB A.left) (M : LB B.left) (k : ℕ) (eA : LB.Gen (L.pull (eSec A))) (eB : LB.Gen (M.pull (eSec B))), IsAbelianScheme A → L.IsLB → M.IsLB → ∀ (R : Type) [CommRing R] (t : Sp R ⟶ Sp Rg) (A' B' : Over (Sp R)) [GrpObj A'] [GrpObj B'] (φA' : A'.left ⟶ A.left) (φB' : B'.left ⟶ B.left) (Φ' : A' ⟶ B') (ψA : A'.left ⟶ (topS Rg ⊗ A).left) (ψB : B'.left ⟶ (topS Rg ⊗ B).left) (α α₂ : LB.Gen (isoLB (L := L) (M := M) k Φ' ψA ψB)) (v : Γ(A'.left, ⊤)ˣ), IsTest A B L M t A' B' φA' φB' Φ' → ψA ≫ (snd (topS Rg) A).left = φA' → ψB ≫ (snd (topS Rg) B).left = φB' → (∀ p, α.s p = res (le_top : (isoLB (L := L) (M := M) k Φ' ψA ψB).U p ≤ ⊤) v * α₂.s p) → RigEq L M k eA eB t Φ' ψA ψB α → RigEq L M k eA eB t Φ' ψA ψB α₂ → v = 1 := by
  intro Rg _ A B _ _ L M k eA eB hA hL hM R _ t A' B' _ _ φA' φB' Φ' ψA ψB α α₂ v hT hψA hψB hv hα hα₂
  have hA' : IsAbelianScheme A' := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA hT.1
  refine Formalism.MainNotions.ModuliIntegralCharts.H1.ChartFrameTrA.unit_eq_one_of_eSec GlobalTheory.globalFns_holds A' hA' v ?_
  show (zeroPt A').appTop.hom v.val = 1
  let W : ((Fin 1 → M.ι) × (Fin 1 → L.ι)) → (Sp R).Opens := fun p =>
    (zeroPt A') ⁻¹ᵁ (isoLB (L := L) (M := M) k Φ' ψA ψB).U p ⊓
      t ⁻¹ᵁ LB.wchart L (fun _ : PUnit => eSec A) (fun _ => p.2 0) ⊓
      t ⁻¹ᵁ LB.wchart M (fun _ : PUnit => eSec B) (fun _ => p.1 0)
  have hloc : ∀ p, ((Sp R).presheaf.map (homOfLE (le_top : W p ≤ ⊤)).op).hom
      ((zeroPt A').appTop.hom v.val) = 1 := by
    intro p
    have h1 := hα p
    have h2 := hα₂ p
    rw [hv p, Units.val_mul, map_mul] at h1
    have hres : (Scheme.Hom.appLE (zeroPt A') ((isoLB (L := L) (M := M) k Φ' ψA ψB).U p) (W p)
        (inf_le_left.trans inf_le_left)).hom
          ((res (le_top : (isoLB (L := L) (M := M) k Φ' ψA ψB).U p ≤ ⊤) v : Γ(A'.left, (isoLB (L := L) (M := M) k Φ' ψA ψB).U p)ˣ) : Γ(A'.left, (isoLB (L := L) (M := M) k Φ' ψA ψB).U p)) =
        ((Sp R).presheaf.map (homOfLE (le_top : W p ≤ ⊤)).op).hom ((zeroPt A').appTop.hom v.val) := by
      show (A'.left.presheaf.map (homOfLE (le_top : (isoLB (L := L) (M := M) k Φ' ψA ψB).U p ≤ ⊤)).op ≫
        Scheme.Hom.appLE (zeroPt A') ((isoLB (L := L) (M := M) k Φ' ψA ψB).U p) (W p)
          (inf_le_left.trans inf_le_left)).hom v.val = _
      rw [Scheme.Hom.map_appLE]
      rfl
    rw [hres] at h1
    have key := h1.trans h2.symm
    rw [_root_.mul_assoc] at key
    exact (IsUnit.mul_left_inj (IsUnit.mul ((α₂.s p).isUnit.map _) (((eA.s _).isUnit.map _).pow k))).1
      (key.trans (_root_.one_mul _).symm)
  have hcov : (⊤ : (Sp R).Opens) ≤ iSup W := by
    rintro x -
    have hc : ∀ {X : Scheme.{0}} (N : LB X), N.IsLB → ∀ y : X, ∃ i, y ∈ N.U i := fun N hN y =>
      TopologicalSpace.Opens.mem_iSup.1 (by rw [hN.cover]; trivial)
    obtain ⟨iL, hiL⟩ := hc L hL ((eSec A) (t x))
    obtain ⟨iM, hiM⟩ := hc M hM ((eSec B) (t x))
    haveI := hT.2.2.1
    have eA' : zeroPt A' ≫ ψA ≫ (snd (topS Rg) A).left = t ≫ eSec A := by
      rw [hψA]; exact GlobalTheory.UU.eSec_comp_of_isGrpPullback hT.1
    have eB' : zeroPt A' ≫ (Φ'.left ≫ ψB) ≫ (snd (topS Rg) B).left = t ≫ eSec B := by
      have h0 : zeroPt A' ≫ Φ'.left = zeroPt B' := congrArg Over.Hom.left (IsMonHom.one_hom Φ')
      rw [Category.assoc, hψB, ← Category.assoc, h0]
      exact GlobalTheory.UU.eSec_comp_of_isGrpPullback hT.2.1
    refine TopologicalSpace.Opens.mem_iSup.2 ⟨(fun _ => iM, fun _ => iL), ?_⟩
    refine ⟨⟨⟨Set.mem_iInter.2 fun _ => ?_, Set.mem_iInter.2 fun _ => ?_⟩, Set.mem_iInter.2 fun _ => hiL⟩,
      Set.mem_iInter.2 fun _ => hiM⟩
    · show ((Φ'.left ≫ ψB) ≫ (snd (topS Rg) B).left) (zeroPt A' x) ∈ M.U iM
      rw [← Scheme.Hom.comp_apply, eB', Scheme.Hom.comp_apply]
      exact hiM
    · show (ψA ≫ (snd (topS Rg) A).left) (zeroPt A' x) ∈ L.U iL
      rw [← Scheme.Hom.comp_apply, eA', Scheme.Hom.comp_apply]
      exact hiL
  exact TopCat.Sheaf.eq_of_locally_eq' (Sp R).sheaf W ⊤ (fun p => homOfLE le_top) hcov _ 1
    (fun p => (hloc p).trans (map_one ((Sp R).presheaf.map (homOfLE le_top : W p ⟶ ⊤).op).hom).symm)

end GlobalTheory.HomFixUnit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NotDvdTrace
section
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.MainNotions.G NumberField GlobalTheory.IndefiniteRowSideFullHecke.LevelLossDegreeBounds

namespace GlobalTheory.LevelCoprime

open Formalism.FrobeniusOrbits

section Host

variable {R : Ranks} (H : Host R)

theorem phi_conj (φ : H.E →+* ℂ) (x : H.E) : φ (H.conj x) = starRingEnd ℂ (φ x) :=
  H.conjE_apply φ x

theorem conj_conj (x : H.E) : H.conj (H.conj x) = x := by
  apply H.φ₀.injective
  rw [phi_conj, phi_conj, Complex.conj_conj]

theorem sigma_conj (σ : H.E ≃ₐ[ℚ] H.E) (x : H.E) : σ (H.conj x) = H.conj (σ x) := by
  apply H.φ₀.injective
  have h1 := phi_conj H (H.φ₀.comp (σ : H.E →+* H.E)) x
  exact h1.trans (phi_conj H H.φ₀ (σ x)).symm

theorem b_sq : H.sqrtMinusD ^ 2 = -(H.d : H.E) := H.sqd_sq

theorem conj_b : H.conj H.sqrtMinusD = -H.sqrtMinusD := by
  apply H.φ₀.injective
  have h3 : H.φ₀ H.sqrtMinusD = Complex.I * (Real.sqrt H.d : ℂ) := H.φ₀_mem
  rw [phi_conj, map_neg, h3]
  simp

theorem agree_on_K (σ τ : H.E ≃ₐ[ℚ] H.E) (h : σ H.sqrtMinusD = τ H.sqrtMinusD) (x : H.E) (hx : x ∈ H.K) :
    σ x = τ x := by
  have hx' : x ∈ IntermediateField.adjoin ℚ {H.sqrtMinusD} := hx
  clear hx
  induction hx' using IntermediateField.adjoin_induction with
  | mem y hy => rw [Set.mem_singleton_iff.1 hy]; exact h
  | algebraMap r => simp
  | add a b _ _ ha hb => rw [map_add (f := _), map_add (f := _), ha, hb]
  | inv a _ ha => rw [map_inv₀, map_inv₀, ha]
  | mul a b _ _ ha hb => rw [map_mul, map_mul, ha, hb]

theorem trace_rat (x : H.E) (hx : x ∈ H.K) : ∃ r : ℚ, algebraMap ℚ H.E r = x + H.conj x := by
  haveI : IsGalois ℚ H.E := H.hostE_isGalois
  have hmem : x + H.conj x ∈ (⊥ : IntermediateField ℚ H.E) := by
    rw [← IsGalois.fixedField_top, IntermediateField.mem_fixedField_iff]
    intro σ _
    have hb : σ H.sqrtMinusD = H.sqrtMinusD ∨ σ H.sqrtMinusD = -H.sqrtMinusD := by
      apply sq_eq_sq_iff_eq_or_eq_neg.1
      rw [← map_pow, b_sq, map_neg, map_natCast]
    rw [map_add (f := _), sigma_conj]
    rcases hb with hb | hb
    · have := agree_on_K H σ 1 hb x hx
      rw [this]; rfl
    · have := agree_on_K H σ H.conj (hb.trans (conj_b H).symm) x hx
      rw [this, conj_conj, add_comm]
  exact IntermediateField.mem_bot.1 hmem

theorem trace_int (x : 𝓞 H.E) (hx : (x : H.E) ∈ H.K) : ∃ a : ℤ, (a : H.E) = x + H.conj x := by
  obtain ⟨r, hr⟩ := trace_rat H x hx
  have h1 : IsIntegral ℤ (H.conj (x : H.E)) :=
    IsIntegral.map (H.conj : H.E →+* H.E).toIntAlgHom x.isIntegral_coe
  have h2 : IsIntegral ℤ (algebraMap ℚ H.E r) := hr ▸ x.isIntegral_coe.add h1
  have h3 : IsIntegral ℤ r := (isIntegral_algebraMap_iff ).1 h2
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral h3
  refine ⟨a, ?_⟩
  rw [← hr, ← ha]
  simp

theorem trace_sq_le (x : H.E) (a : ℤ) (T : ℕ) (ha : (a : H.E) = x + H.conj x) (hT : x * H.conj x = T) :
    a ^ 2 ≤ 4 * T := by
  have h1 := congrArg H.φ₀ ha
  have h2 := congrArg H.φ₀ hT
  rw [map_add (f := _), phi_conj, map_intCast, Complex.add_conj] at h1
  rw [map_mul, phi_conj, map_natCast, Complex.mul_conj, Complex.normSq_apply] at h2
  have h3 : (a : ℝ) = 2 * (H.φ₀ x).re := by exact_mod_cast h1
  have h4 : (H.φ₀ x).re * (H.φ₀ x).re + (H.φ₀ x).im * (H.φ₀ x).im = (T : ℝ) := by exact_mod_cast h2
  have h5 : (a : ℝ) ^ 2 ≤ 4 * T := by
    rw [h3, ← h4]
    nlinarith [mul_self_nonneg (H.φ₀ x).im]
  exact_mod_cast h5

end Host

theorem four_dvd {E : Type} [Field E] [NumberField E] (n : ℤ) (y : E) (hy : IsIntegral ℤ y)
    (h : (n : E) = 4 * y) : (4 : ℤ) ∣ n := by
  have h1 : y = algebraMap ℚ E ((n : ℚ) / 4) := by
    rw [map_div₀, map_intCast, h]
    simp
  rw [h1] at hy
  have h3 := (isIntegral_algebraMap_iff ).1 hy
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral h3
  refine ⟨a, ?_⟩
  have h4 : (a : ℚ) = (n : ℚ) / 4 := by simpa using ha
  have h5 : (n : ℚ) = 4 * a := by rw [h4]; ring
  exact_mod_cast h5

theorem not_dvd_trace {D : D7} (X : ErrX D) (u : D.what₂.Word) (a : ℤ)
    (ha : (a : D.host.E) = X.piT u + D.host.conj (X.piT u)) : ¬ (((D.mem u).A.T : ℤ) ∣ a) := by
  intro hd
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.1 (X.piT_cong u)
  have hdiv : ∃ b : 𝓞 D.host.E, X.piT u = 1 + 4 * b := by
    have h4 : (4 : ℕ) ∣ D.host.QS :=
      (show (4 : ℕ) ∣ 2 ^ (D.R.e + 2) from ⟨2 ^ D.R.e, by ring⟩).trans D.host.tower_dvd
    obtain ⟨k, hk⟩ := h4
    refine ⟨(k * D.host.q * D.host.d * (D.host.g 0 * D.host.g 1) ^ 2 : ℕ) * c, ?_⟩
    rw [hk] at hc
    push_cast at hc ⊢
    linear_combination hc
  obtain ⟨b, hb⟩ := hdiv
  have hn := X.piT_norm u
  have hle := trace_sq_le D.host _ a _ ha hn
  have hb' : ((X.piT u : 𝓞 D.host.E) : D.host.E) = 1 + 4 * (b : D.host.E) := by
    rw [hb]; simp [map_ofNat]
  have hbi : IsIntegral ℤ (D.host.conj (b : D.host.E)) :=
    IsIntegral.map (D.host.conj : D.host.E →+* D.host.E).toIntAlgHom b.isIntegral_coe
  have hb0 := b.isIntegral_coe
  rw [hb'] at ha hn
  simp only [map_add (f := _), map_mul, map_one, map_ofNat] at ha hn
  have h1 : (4 : ℤ) ∣ a - 2 := four_dvd _ _ (hb0.add hbi) (by push_cast; linear_combination ha)
  have h4 : IsIntegral ℤ (4 : D.host.E) := by
    simpa using (isIntegral_algebraMap (R := ℤ) (A := D.host.E) (x := 4))
  have h2 : (4 : ℤ) ∣ ((D.mem u).A.T : ℤ) - 1 :=
    four_dvd _ _ ((hb0.add hbi).add ((h4.mul hb0).mul hbi)) (by push_cast; linear_combination -hn)
  have h3 := (D.mem u).A.T_prime.two_le
  obtain ⟨k, rfl⟩ := hd
  set T : ℤ := ((D.mem u).A.T : ℤ) with hT
  have h5 : 5 ≤ T := by omega
  have hk : k ≠ 0 := by
    rintro rfl
    omega
  have hk2 : 1 ≤ k ^ 2 := by
    have := sq_pos_of_ne_zero hk
    omega
  nlinarith [mul_pow T k 2]

theorem coprime_conj {D : D7} (X : ErrX D) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hw : D.what₂.places.resChar w = (D.mem u).A.T) :
    ¬ (0 < vAdd (D.plEq w) (D.embE (X.piT u : D.host.E)) ∧
      0 < vAdd (D.plEq w) (star (D.embE (X.piT u : D.host.E)))) := by
  rintro ⟨h1, h2⟩
  obtain ⟨a, ha⟩ := trace_int D.host (X.piT u) (X.piT_K u)
  have hp := (D.mem u).A.T_prime
  have hn := X.piT_norm u
  have hT0 : (((D.mem u).A.T : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  rw [← hn] at hT0
  rw [← D.embE_conj] at h2
  have i1 : IsIntegral ℤ (D.embE (X.piT u : D.host.E)) :=
    IsIntegral.map D.embE.toIntAlgHom (X.piT u).isIntegral_coe
  have i2 : IsIntegral ℤ (D.embE (D.host.conj (X.piT u : D.host.E))) :=
    IsIntegral.map (D.embE.comp (D.host.conj : D.host.E →+* D.host.E)).toIntAlgHom (X.piT u).isIntegral_coe
  let y : 𝓞 D.what₂.LL := ⟨_, i1⟩
  let z : 𝓞 D.what₂.LL := ⟨_, i2⟩
  have hy : y ≠ 0 := fun h => (map_ne_zero D.embE).2 (left_ne_zero_of_mul hT0) (congrArg Subtype.val h)
  have hz : z ≠ 0 := fun h => (map_ne_zero D.embE).2 (right_ne_zero_of_mul hT0) (congrArg Subtype.val h)
  have m1 := (GlobalTheory.TypeLoss.mem_heightOneIdeal_iff_additiveValuation_pos (D.plEq w) y hy).2 h1
  have m2 := (GlobalTheory.TypeLoss.mem_heightOneIdeal_iff_additiveValuation_pos (D.plEq w) z hz).2 h2
  have e : ((a : ℤ) : 𝓞 D.what₂.LL) = y + z := by
    apply RingOfIntegers.coe_injective
    rw [map_intCast, map_add (f := _)]
    change _ = D.embE _ + D.embE _
    rw [← map_add (f := _), ← ha, map_intCast]
  have m3 : ((a : ℤ) : 𝓞 D.what₂.LL) ∈ (D.plEq w).asIdeal := e ▸ Ideal.add_mem _ m1 m2
  have m4 : (((D.mem u).A.T : ℕ) : 𝓞 D.what₂.LL) ∈ (D.plEq w).asIdeal := hw ▸ resChar_mem D w
  have hc : IsCoprime (((D.mem u).A.T : ℕ) : ℤ) a :=
    (Nat.prime_iff_prime_int.1 hp).irreducible.coprime_iff_not_dvd.2 (not_dvd_trace X u a ha)
  obtain ⟨s, t, hst⟩ := hc
  apply (D.plEq w).isPrime.ne_top
  rw [Ideal.eq_top_iff_one]
  have h := congrArg (Int.cast : ℤ → 𝓞 D.what₂.LL) hst
  push_cast at h
  rw [← h]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ m4) (Ideal.mul_mem_left _ _ m3)

end GlobalTheory.LevelCoprime
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfHCharN
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.Mem.Col2.SplitChar

namespace GlobalTheory.SplitCharGen

variable {D : D7}

def ofHChar (N : ℕ) (χ : Formalism.L2.Host.HChar D.host.E) (n : D.what₂.Tau → ℤ) (hu : χ.IsUnitary)
    (hi : χ.HasInf (Formalism.L2.Host.embTau D) n) (hp : ∀ τ, Even (n τ - (N : ℤ)))
    (hc : ∃ m : ℕ, 0 < m ∧ ∀ u, IntU D u → (∃ s ∈ OhE D, (u : AE D) - 1 = (m : AE D) * s) → χ.1 (finIdl D u) = 1)
    (hn : ∀ x, χ.1 (finIdl D (x * sgU D x)) = 1)
    (hr : ∀ u, IntU D u → (∀ q : ℕ, q.Prime → ¬ InertQ D q → ZeroAt D q ((u : AE D) - 1)) → χ.1 (finIdl D u) = 1) :
    HeckeU D N where
  f := χ.1.comp (finIdl D)
  n := n
  unitary := fun _ => hu _
  cont := hc
  aut := fun a => by
    have h1 := χ.2.2 a
    rw [← GlobalTheory.Mem.ChiLaws.infDiag_mul_finPart, map_mul, ← finIdl_incU, mul_comm] at h1
    have h2 := hi a
    have h3 := congrArg (Units.val : ℂˣ → ℂ) h1
    rw [Units.val_mul, Units.val_one] at h3
    rw [← h3]
    exact congrArg _ h2.symm
  norm := hn
  par := hp
  unr := hr

end GlobalTheory.SplitCharGen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdDerivWeierstrassPOverSquaresNeZero
section
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

noncomputable section

namespace GlobalTheory.CMModel.SqNe

theorem natMul_mem {p : ℕ} {F : IntermediateField ℚ ℂ} {L : PeriodPair} {t : ℂ} (h : Datum p F L t) :
    (p : ℂ) * t ∈ L.lattice := by
  have h1 := neg_mem (h.mul _ h.ker)
  rw [← mul_assoc, ← sq, sqrtNegNat_sq, neg_mul, neg_neg] at h1
  exact h1

theorem mul_notMem {p : ℕ} {F : IntermediateField ℚ ℂ} {L : PeriodPair} {t : ℂ} (h : Datum p F L t)
    {n : ℕ} (hn : Nat.Coprime n p) : (n : ℂ) * t ∉ L.lattice := fun hm => by
  have h1 := natMul_mem h
  obtain ⟨a, b, e⟩ := Nat.isCoprime_iff_coprime.2 hn
  have e' : (a : ℂ) * n + b * p = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → ℂ) e
  have := add_mem (zsmul_mem hm a) (zsmul_mem h1 b)
  rw [zsmul_eq_mul, zsmul_eq_mul, ← mul_assoc, ← mul_assoc, ← add_mul, e', one_mul] at this
  exact h.notMem this

theorem coprime_sq {p : ℕ} (hp : p.Prime) (k : Sq p) : Nat.Coprime (k.1 : ℕ) p :=
  ((Nat.Prime.coprime_iff_not_dvd hp).2 fun h => k.2.1 ((ZMod.natCast_eq_zero_iff _ _).2 h)).symm

theorem sqPt_and_sqProd_ne_zero : ∀ (p : ℕ) (F : IntermediateField ℚ ℂ) (L : PeriodPair) (t : ℂ),
    p.Prime → p % 4 = 3 → 3 < p → Datum p F L t →
      (∀ k : Sq p, sqPt p t k ∉ L.lattice ∧ (p : ℂ) * sqPt p t k ∈ L.lattice) ∧ sqProd p L t ≠ 0 := by
  intro p F L t hp h4 h3 h
  have h2 : p ≠ 2 := by omega
  refine ⟨fun k => ⟨mul_notMem h (coprime_sq hp k), ?_⟩, ?_⟩
  · have := zsmul_mem (natMul_mem h) (k.1 : ℕ)
    rw [zsmul_eq_mul] at this
    convert this using 1
    rw [sqPt]; push_cast; ring
  · refine Finset.prod_ne_zero_iff.2 fun k _ => ?_
    rw [Ne, GlobalTheory.derivWeierstrassP_eq_zero_iff L (show sqPt p t k ∉ L.lattice from mul_notMem h (coprime_sq hp k))]
    have := mul_notMem h (Nat.Coprime.mul_left ((Nat.coprime_primes Nat.prime_two hp).2 h2.symm)
      (coprime_sq hp k))
    intro hm
    apply this
    convert hm using 1
    rw [sqPt]; push_cast; ring

end GlobalTheory.CMModel.SqNe
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeierstrassPTwoMulMulSqStatement
section
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weierstrassP_two_mul_mul_deriv_sq : ∀ (L : PeriodPair) (z : ℂ), z ∉ L.lattice → 2 * z ∉ L.lattice → L.weierstrassP (2 * z) * L.derivWeierstrassP z ^ 2 = (6 * L.weierstrassP z ^ 2 - L.g₂ / 2) ^ 2 / 4 - 2 * L.weierstrassP z * L.derivWeierstrassP z ^ 2 := by
  first | exact @GlobalTheory.weierstrassP_two_mul_mul_sq | exact GlobalTheory.weierstrassP_two_mul_mul_sq | (intros; apply GlobalTheory.weierstrassP_two_mul_mul_sq <;> assumption)
end

