module

public import Formalism.LocalToGlobal.Columns.Bundle0008
public import Formalism.LocalToGlobal.Columns.GSetLemmas
public import Formalism.LocalToGlobal.Columns.Bundle0004
public import Formalism.LocalToGlobal.Columns.CoefColLemmas
public import Formalism.LocalToGlobal.Columns.Bundle0012
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0008
public import Mathlib
public import Formalism.PeriodIntegrals.Bundle0009
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0004
public import Formalism.LocalToGlobal.GroupLattices.FockModels.Bundle0002
public import Formalism.LocalToGlobal.Columns.CmUnramifiedOfFieldConditions
public import Formalism.LocalToGlobal.Columns.RecLevelLocF
public import Formalism.LocalToGlobal.Columns.BaseLemmas
public import Formalism.LocalToGlobal.Columns.TiedValLatG

@[expose] public section

-- bundled from Formalism.LocalToGlobal.Columns.InputsLemmas
section
noncomputable section

namespace Formalism.L2.Col

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.HermitianLatticesTheory MvPolynomial

theorem minkowskiBound_holds : MinkowskiBound := card_dvd_minkowskiNumber

section Stab

variable {X : Fields} {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))}
  (C : CoefPk X n (DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG))) (Λ : LevFam X.E X.K n SG)

end Stab

section Cols

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

end Cols

section Loc

variable {K : Type} [Field K] [NumberField K] [StarRing K]

end Loc

section C2

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] {n : ℕ}

end C2

section AtT

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

end AtT

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.InputsWeyl
section
open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

theorem weylDim_of_weylProd (h : PI.WeylProd) {n : ℕ} (lam : DomWeight n) : WeylDim lam := by
  unfold WeylDim
  rw [Formalism.L2.G.Model.card_ssIdx]
  have hnn : ∀ t, ((lam.natW t : ℕ) : ℤ) = lam.w t - lam.detShift := by
    intro t
    unfold DomWeight.natW
    apply Int.toNat_of_nonneg
    unfold DomWeight.detShift
    have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le _) t.isLt
    rw [dite_eq_left hn]
    have h1 : t ≤ (⟨n - 1, by omega⟩ : Fin n) := by
      rw [Fin.le_def]
      have := t.isLt
      show t.val ≤ n - 1
      omega
    have := lam.anti h1
    omega
  have hanti : Antitone (fun t => ((lam.natW t : ℕ) : ℤ)) := by
    intro a b hab
    have := lam.anti hab
    simp only [hnn]
    omega
  have h1 := Formalism.L2.G.Model.weylQ n _ hanti
  have h2 : _ = Formalism.LogVandermondeBounds.StandardLattice.dimVN (wSeq lam) n := h n (fun t => ((lam.natW t : ℕ) : ℤ)) lam.w lam.detShift hnn
  rw [← h2, ← h1, Rat.cast_natCast]

theorem weylDim_holds {n : ℕ} (lam : DomWeight n) : WeylDim lam := weylDim_of_weylProd weyl_product_formula lam

section Inst

open Finset Formalism.LogVandermondeBounds.StandardLattice

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

end Inst

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.RecLevelLocP
section
open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.L2.DIV (Pl kP)

section Places

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable (hc : Formalism.BasicNotions.CMData F E)
include hc

theorem rll_cO_algebraMap (a : 𝓞 F) : cO E (algebraMap (𝓞 F) (𝓞 E) a) = algebraMap (𝓞 F) (𝓞 E) a := by
  apply RingOfIntegers.ext
  change algebraMap (𝓞 E) E (cO E (algebraMap (𝓞 F) (𝓞 E) a)) = algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) a)
  rw [algebraMap_cO]
  have e : algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) a) = algebraMap F E (algebraMap (𝓞 F) F a) := by
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  rw [e]
  exact (hc.fixed _).2 ⟨_, rfl⟩

theorem IsOver.conj {v : HeightOneSpectrum (𝓞 F)} {P : Pl E} (h : IsOver v P) : IsOver v (conjPrime₂ P) := by
  unfold IsOver at h ⊢
  rw [h]
  ext a
  rw [Ideal.mem_comap, Ideal.mem_comap, mem_conjP, rll_cO_algebraMap hc]

theorem rll_norm_mem (a : 𝓞 E) : ∃ b : 𝓞 F, algebraMap (𝓞 F) (𝓞 E) b = a * cO E a := by
  have h1 : star (algebraMap (𝓞 E) E (a * cO E a)) = algebraMap (𝓞 E) E (a * cO E a) := by
    rw [map_mul, algebraMap_cO, star_mul', star_star, mul_comm]
  obtain ⟨x, hx⟩ := (hc.fixed _).1 h1
  have hi : IsIntegral ℤ x := by
    have h2 : IsIntegral ℤ (algebraMap F E x) := by rw [hx]; exact RingOfIntegers.isIntegral_coe _
    exact (isIntegral_algebraMap_iff ).1 h2
  obtain ⟨b, hb⟩ : ∃ b : 𝓞 F, algebraMap (𝓞 F) F b = x := ⟨⟨x, hi⟩, rfl⟩
  refine ⟨b, ?_⟩
  apply RingOfIntegers.ext
  change algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) b) = algebraMap (𝓞 E) E (a * cO E a)
  rw [← hx, ← hb, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]

theorem rll_over_cases {v : HeightOneSpectrum (𝓞 F)} {P Q : Pl E} (hP : IsOver v P) (hQ : IsOver v Q) :
    Q = P ∨ Q = conjPrime₂ P := by
  classical
  by_contra hne
  push Not at hne
  obtain ⟨a, ha⟩ := Formalism.L2.DIV.crtPl ({Q, P, conjPrime₂ P} : Finset (Pl E)) (fun R => if R = Q then 0 else 1)
  have h1 : a ∈ Q.asIdeal := by
    have := ha Q (by simp)
    simpa using this
  have hnot : ∀ R : Pl E, R ≠ Q → R ∈ ({Q, P, conjPrime₂ P} : Finset (Pl E)) → a ∉ R.asIdeal := by
    intro R hR hm haR
    have := ha R hm
    rw [if_neg hR] at this
    exact (Ideal.ne_top_iff_one _).1 R.isPrime.ne_top (by
      have h2 := Ideal.sub_mem _ haR this
      simpa using h2)
  have h2 := hnot P (Ne.symm hne.1) (by simp)
  have h3 := hnot (conjPrime₂ P) (Ne.symm hne.2) (by simp)
  obtain ⟨b, hb⟩ := rll_norm_mem hc a
  have hbv : b ∈ v.asIdeal := by
    rw [hQ, Ideal.mem_comap, hb]; exact Ideal.mul_mem_right _ _ h1
  rw [hP, Ideal.mem_comap, hb] at hbv
  rcases P.isPrime.mem_or_mem hbv with h | h
  · exact h2 h
  · exact h3 ((mem_conjP P a).2 h)

theorem BasePi.over_unique {ST : Finset (Pl E)} {π : 𝓞 E} (h : BasePi ST π) {v : HeightOneSpectrum (𝓞 F)} {P : Pl E}
    (hP : P ∈ ST) (hov : IsOver v P) : ∀ Q ∈ ST, IsOver v Q → Q = P := by
  intro Q hQ hQv
  rcases rll_over_cases hc hov hQv with e | e
  · exact e
  · exfalso
    have h1 : π ∈ (conjPrime₂ P).asIdeal := e ▸ h.mem hQ
    exact h.conj_notMem hP ((mem_conjP P π).1 h1)

theorem mem_plUnder_iff_norm {S : Finset (Pl E)} {ϖ : 𝓞 E} (hS : ∀ P : Pl E, P ∈ S ↔ ϖ ∈ P.asIdeal) (N : ℕ)
    (hN : ϖ * cO E ϖ = (N : 𝓞 E)) (v : HeightOneSpectrum (𝓞 F)) : v ∈ plUnder F S ↔ (N : 𝓞 F) ∈ v.asIdeal := by
  constructor
  · rintro ⟨P, hP, hv⟩
    rw [hv, Ideal.mem_comap, map_natCast, ← hN]
    exact Ideal.mul_mem_right _ _ ((hS P).1 hP)
  · intro hv
    obtain ⟨P, hP⟩ := Formalism.L2.DIV.exists_overPl (E := E) v
    have hP' : IsOver v P := hP
    have h1 : (N : 𝓞 E) ∈ P.asIdeal := by
      rw [hP, Ideal.mem_comap, map_natCast] at hv; exact hv
    rw [← hN] at h1
    rcases P.isPrime.mem_or_mem h1 with h | h
    · exact ⟨P, (hS P).2 h, hP'⟩
    · exact ⟨conjPrime₂ P, (hS _).2 ((mem_conjP P ϖ).2 h), hP'.conj hc⟩

end Places

section Host

variable {X : Fields} {Pr : Primes X}

theorem basePi_of_ok (hX : X.Ok) (hPr : Pr.Ok) (u : Pr.Word) : BasePi (Pr.vT u) (Pr.piT u) := by
  have hcop := hPr.piT_cop u
  refine ⟨?_, hcop⟩
  intro r
  have h0 : Pr.piT u ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hcop
    exact not_isCoprime_zero_zero hcop
  constructor
  · intro hr
    exact piT_dvd_of_mem hX hPr u r fun P => hr P.1 P.2
  · rintro ⟨q, rfl⟩ P hP
    exact Ideal.mul_mem_right _ _ ((mem_divs h0 P).1 hP)


open Classical in
theorem plUnder_vGs (hc : Formalism.BasicNotions.CMData X.F X.E) (hPr : Pr.Ok) (v : HeightOneSpectrum (𝓞 X.F)) :
    v ∈ plUnder X.F Pr.vGs ↔ (Pr.g 0 : 𝓞 X.F) ∈ v.asIdeal ∨ (Pr.g 1 : 𝓞 X.F) ∈ v.asIdeal := by
  have key : ∀ i, v ∈ plUnder X.F (Pr.vG i) ↔ (Pr.g i : 𝓞 X.F) ∈ v.asIdeal := fun i => by
    have hne : X.conjO (Pr.piG i) ≠ 0 := by
      intro h0
      have := hPr.piG_norm i
      rw [h0, mul_zero] at this
      exact (Nat.cast_ne_zero.2 (hPr.g_prime i).ne_zero) this.symm
    refine mem_plUnder_iff_norm hc (fun P => mem_divs hne P) (Pr.g i) ?_ v
    have h2 : cO X.E (X.conjO (Pr.piG i)) = Pr.piG i := RingOfIntegers.ext (star_star _)
    rw [h2, mul_comm]; exact hPr.piG_norm i
  rw [← key 0, ← key 1]
  constructor
  · rintro ⟨P, hP, ho⟩
    rcases Finset.mem_union.1 hP with h | h
    · exact Or.inl ⟨P, h, ho⟩
    · exact Or.inr ⟨P, h, ho⟩
  · rintro (⟨P, hP, ho⟩ | ⟨P, hP, ho⟩)
    · exact ⟨P, Finset.mem_union_left _ hP, ho⟩
    · exact ⟨P, Finset.mem_union_right _ hP, ho⟩

end Host

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.TiedValBwG
section
open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG Formalism.L2.Forms

section Span

variable {K : Type} [Field K] [NumberField K] (Pl : Rows.Places K) (pw : Pl.Pl → HeightOneSpectrum (𝓞 K))
  (hval : ∀ w (x : K), x ≠ 0 → Pl.val w x = ((vAdd (pw w) x : ℤ) : WithTop ℤ))
  {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

include hval

theorem vl_mem_span_intW_iff (w : Pl.Pl) (A : Submodule (𝓞 K) V) (x : V) :
    x ∈ Submodule.span (intW Pl w) (A : Set V) ↔ x ∈ localization₂ (pw w).asIdeal A := by
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem y hy => exact lc_le_locP _ _ hy
    | zero => exact zero_mem _
    | add y z _ _ hy hz => exact add_mem hy hz
    | smul r y _ hy =>
      obtain ⟨s, hs, hsy⟩ := hy
      obtain ⟨t, ht, hta⟩ := (vl_mem_intW_iff Pl pw hval w (r : K)).1 r.2
      obtain ⟨a, ha⟩ := Submodule.mem_one.1 hta
      refine ⟨t * s, lc_mul_notMem (pw w) ht hs, ?_⟩
      have e : (t * s) • (r • y) = a • (s • y) := by
        rw [Subring.smul_def, ← algebraMap_smul K (t * s), ← algebraMap_smul K a, ← algebraMap_smul K s, smul_smul, smul_smul,
          ha, Algebra.smul_def, map_mul]
        congr 1
        ring
      rw [e]
      exact A.smul_mem _ hsy
  · rintro ⟨t, ht, htx⟩
    have h0 : algebraMap (𝓞 K) K t ≠ 0 := by
      intro h
      exact lc_ne_zero_of_notMem (pw w) ht (by exact_mod_cast (FaithfulSMul.algebraMap_injective (𝓞 K) K) (h.trans (map_zero _).symm))
    have e : x = (⟨_, vl_inv_mem_intW Pl pw hval w ht⟩ : intW Pl w) • (t • x) := by
      rw [Subring.smul_def, ← algebraMap_smul K t, smul_smul, inv_mul_cancel₀ h0, one_smul]
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span htx)

end Span

section DictF

variable {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] (Pl : Rows.Places K)
  (pw : Pl.Pl → HeightOneSpectrum (𝓞 K))
  (hval : ∀ w (x : K), x ≠ 0 → Pl.val w x = ((vAdd (pw w) x : ℤ) : WithTop ℤ))
  {ι : Type} [Fintype ι] {n : ℕ} (emb : ι → E →+* K) (s : K →+* ℂ)

def vlBdF (B : ι → GL (Fin n) E) : ι → GL (Fin n) K := fun τ => inside₂ K n (bc (emb τ) (B τ))

theorem vl_coordF (J : Matrix (Fin n) (Fin n) E) (lam : ι → DomWeight n) (B : ι → GL (Fin n) E) (F : VV K lam) :
    evV emb J lam s F = fnOf _ (shiftOf lam)
      (fun τ => atInf (embAt s emb) (((B τ)⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) τ)
      (MvPolynomial.map s (actP lam (vlBdF emb B)⁻¹ F.1)) := by
  have h := evFr_coord (gramC J (embAt s emb)) s lam (vlBdF emb B) F.1
  have e : (fun τ => (((vlBdF emb B τ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map s)ᵀ) =
      fun τ => atInf (embAt s emb) (((B τ)⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) τ := by
    funext τ
    show ((((bc (emb τ) (B τ))⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ.map s)ᵀ =
      (((B τ)⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).map (s.comp (emb τ))
    rw [← map_inv, bc_coe]
    refine Matrix.ext fun a b => ?_
    rfl
  rw [← e]
  exact h

include hval

theorem mem_localization_iff_forall_localBasis (w : Pl.Pl) (J : Matrix (Fin n) (Fin n) E) (lam lam' : ι → DomWeight n)
    (hn : ∀ τ, (lam τ).natW = (lam' τ).natW) (M : ι → Submodule (𝓞 E) (Fin n → E)) (hM : ∀ τ, Submodule.IsFullLattice E (M τ))
    (F : VV K lam) :
    F ∈ localization₂ (pw w).asIdeal (delK lam fun τ => dualFr (tauLat emb τ (M τ))) ↔
      ∀ B : ι → GL (Fin n) E, (∀ τ, IsLocBasis (Pl.resChar w) (M τ : Set (Fin n → E)) (B τ)) →
        ∃ P ∈ vlIntSpan s Pl w lam', evV emb J lam s F = fnOf _ (shiftOf lam)
          (fun τ => atInf (embAt s emb) (((B τ)⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) τ) P := by
  have hbas : ∀ B : ι → GL (Fin n) E, (∀ τ, IsLocBasis (Pl.resChar w) (M τ : Set (Fin n → E)) (B τ)) →
      ∀ τ, IsBasisAt (pw w) (dualFr (tauLat emb τ (M τ))) (vlBdF emb B τ) := fun B hB τ =>
    pb_isBasisAt_dualFr (pw w) _ (tauLatticeLattice_holds E K ι n emb τ (M τ) (hM τ)).fg _
      (vl_isBasisAt_tauLat Pl pw hval emb τ w (M τ) (B τ) (hB τ))
  have hlat : ∀ τ, Submodule.IsFullLattice K (dualFr (tauLat emb τ (M τ))) := fun τ =>
    du_dualFr_lattice latticeBasisExists_holds _ (tauLatticeLattice_holds E K ι n emb τ (M τ) (hM τ))
  have hmem : ∀ B : ι → GL (Fin n) E, (∀ τ, IsLocBasis (Pl.resChar w) (M τ : Set (Fin n → E)) (B τ)) →
      (F ∈ localization₂ (pw w).asIdeal (delK lam fun τ => dualFr (tauLat emb τ (M τ))) ↔
        actP lam (vlBdF emb B)⁻¹ F.1 ∈ localization₂ (pw w).asIdeal (delStd K lam)) := by
    intro B hB
    have h1 : F ∈ localization₂ (pw w).asIdeal (delK lam fun τ => dualFr (tauLat emb τ (M τ))) ↔
        F.1 ∈ localization₂ (pw w).asIdeal (delP lam fun τ => dualFr (tauLat emb τ (M τ))) := Iff.rfl
    rw [h1, (nablaDeltaLocal_holds K ι n lam _ hlat (pw w) _ (hbas B hB)).2]
    constructor
    · rintro ⟨G, hG, hGF⟩
      have e : actP lam (vlBdF emb B)⁻¹ F.1 = G := by
        rw [← hGF]
        show actP lam (vlBdF emb B)⁻¹ (actP lam (vlBdF emb B) G) = G
        rw [← polyAction_mul, inv_mul_cancel, polyAction_one₂]
      rw [e]
      exact hG
    · intro h
      refine ⟨_, h, ?_⟩
      show actP lam (vlBdF emb B) (actP lam (vlBdF emb B)⁻¹ F.1) = F.1
      rw [← polyAction_mul, mul_inv_cancel, polyAction_one₂]
  constructor
  · intro h B hB
    exact ⟨_, vl_map_mem_intSpan Pl pw hval s w lam lam' hn ((hmem B hB).1 h), vl_coordF emb s J lam B F⟩
  · intro h
    have : Fact (Pl.resChar w).Prime := ⟨Pl.resChar_prime w⟩
    choose B hB using fun τ => by
      letI : Submodule.IsFullLattice E (M τ) := hM τ
      exact Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.LocB.exists_isLocBasis (Pl.resChar w) E (M τ) (hM τ).fg Submodule.IsFullLattice.span_eq_top
    obtain ⟨P, hP, hPe⟩ := h B hB
    obtain ⟨G, hG, rfl⟩ := vl_exists_of_mem_intSpan Pl pw hval s w lam lam' hn hP
    rw [vl_coordF emb s J lam B F] at hPe
    have hinj := fnOf_injective (gramC J (embAt s emb)) (shiftOf lam)
      (fun τ => atInf (embAt s emb) (((B τ)⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) τ)
      (fun τ => Matrix.isUnits_det_units (Matrix.GeneralLinearGroup.map (embAt s emb τ) (B τ)⁻¹)) ⟨fun _ => 1, fun _ => by simp⟩ hPe
    have hG' : actP lam (vlBdF emb B)⁻¹ F.1 = G := MvPolynomial.map_injective s s.injective hinj
    rw [hmem B hB, hG']
    exact hG

theorem mem_localization_iff_forall_localBasis_of_valuation (w : Pl.Pl) (J : Matrix (Fin n) (Fin n) E) (lam lam' : ι → DomWeight n)
    (hn : ∀ τ, (lam τ).natW = (lam' τ).natW) (M : ι → Submodule (𝓞 E) (Fin n → E)) (hM : ∀ τ, Submodule.IsFullLattice E (M τ))
    (F : VV K lam) (B : ι → GL (Fin n) E) (hB : ∀ τ, IsLocBasis (Pl.resChar w) (M τ : Set (Fin n → E)) (B τ)) :
    F ∈ localization₂ (pw w).asIdeal (delK lam fun τ => dualFr (tauLat emb τ (M τ))) ↔
      ∃ P ∈ vlIntSpan s Pl w lam', evV emb J lam s F = fnOf _ (shiftOf lam)
        (fun τ => atInf (embAt s emb) (((B τ)⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) τ) P := by
  constructor
  · intro h
    exact (mem_localization_iff_forall_localBasis Pl pw hval emb s w J lam lam' hn M hM F).1 h B hB
  · rintro ⟨P, hP, hPe⟩
    have hbas : ∀ τ, IsBasisAt (pw w) (dualFr (tauLat emb τ (M τ))) (vlBdF emb B τ) := fun τ =>
      pb_isBasisAt_dualFr (pw w) _ (tauLatticeLattice_holds E K ι n emb τ (M τ) (hM τ)).fg _
        (vl_isBasisAt_tauLat Pl pw hval emb τ w (M τ) (B τ) (hB τ))
    have hlat : ∀ τ, Submodule.IsFullLattice K (dualFr (tauLat emb τ (M τ))) := fun τ =>
      du_dualFr_lattice latticeBasisExists_holds _ (tauLatticeLattice_holds E K ι n emb τ (M τ) (hM τ))
    obtain ⟨G, hG, rfl⟩ := vl_exists_of_mem_intSpan Pl pw hval s w lam lam' hn hP
    rw [vl_coordF emb s J lam B F] at hPe
    have hinj := fnOf_injective (gramC J (embAt s emb)) (shiftOf lam)
      (fun τ => atInf (embAt s emb) (((B τ)⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) τ)
      (fun τ => Matrix.isUnits_det_units (Matrix.GeneralLinearGroup.map (embAt s emb τ) (B τ)⁻¹)) ⟨fun _ => 1, fun _ => by simp⟩ hPe
    have hG' : actP lam (vlBdF emb B)⁻¹ F.1 = G := MvPolynomial.map_injective s s.injective hinj
    have h1 : F ∈ localization₂ (pw w).asIdeal (delK lam fun τ => dualFr (tauLat emb τ (M τ))) ↔
        F.1 ∈ localization₂ (pw w).asIdeal (delP lam fun τ => dualFr (tauLat emb τ (M τ))) := Iff.rfl
    rw [h1, (nablaDeltaLocal_holds K ι n lam _ hlat (pw w) _ hbas).2]
    refine ⟨G, hG, ?_⟩
    show actP lam (vlBdF emb B) G = F.1
    rw [← hG', ← polyAction_mul, mul_inv_cancel, polyAction_one₂]

end DictF

end Formalism.L2.Col
end
end

