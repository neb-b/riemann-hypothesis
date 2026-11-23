module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0355
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0360
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0363
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0069
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0057
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0386
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0349
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0372
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0356
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0385

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinHomImageXDeltaZeroLiftsUniformizerStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.breuilKisinHom_image_X_delta_zero_lifts_uniformizer :
    ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (C : Obj l ↥(OL K))
      (g : Hom bk.prism C), C.D.δ (BK.hf (bk := bk) g X) = 0 ∧
      Ideal.Quotient.mk C.I (BK.hf (bk := bk) g X) = C.str (bk.str.symm (Ideal.Quotient.mk _ X)) := by
  intro l _ K bk C g
  have hδX : (deltaS l bk.a).δ (X : bk.S) = 0 := by
    have h := (deltaS l bk.a).φ_eq (X : bk.S)
    have hφ : (deltaS l bk.a).φ (X : bk.S) = X ^ l := frobS_X l bk.a
    rw [hφ] at h
    have hmul : (l : bk.S) * (deltaS l bk.a).δ X = 0 := by linear_combination -h
    exact (mul_eq_zero.1 hmul).resolve_left (l_ne_zero l bk.a)
  refine ⟨?_, ?_⟩
  · have h := g.f_δ (X : bk.S)
    change C.D.δ (g.f X) = 0
    rw [← h]
    change g.f ((deltaS l bk.a).δ X) = 0
    rw [hδX]
    exact g.f.map_zero
  · refine g.f_str (bk.str.symm (Ideal.Quotient.mk _ X)) X ?_
    change Ideal.Quotient.mk (Ideal.span {bk.E}) X = bk.str (bk.str.symm (Ideal.Quotient.mk _ X))
    rw [RingEquiv.apply_symm_apply]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinIsBetaSubOfLpowSmul
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

theorem GlobalTheory.BKLim.BetaDiv.isBeta_div : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (N d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (F : Frame bk N d ρ) (m k n : ℕ) (β γ : Matrix (Fin d) (Fin d) bk.S), F.IsBeta m k β → 1 ≤ m → n ≤ k → (∀ p q, bk.E ^ m ∣ (β - (l : bk.S) ^ n • γ) p q) → F.IsBeta m (k - n) γ := by
  intro l _ K bk N d ρ F m k n β γ hβ hm hnk hd
  have hT := _root_.GlobalTheory.AinfEPow.ePow_facts l K bk
  have strip : ∀ (r n : ℕ) (a : Ainf l), bk.ev bk.E ^ r ∣ (l : Ainf l) ^ n * a → bk.ev bk.E ^ r ∣ a := by
    intro r n
    induction n with
    | zero => intro a h; simpa using h
    | succ n ih =>
      intro a h
      refine ih a ((hT r).1 _ ?_)
      rw [pow_succ', mul_assoc] at h
      exact h
  have hk : (l : bk.S) ^ k = (l : bk.S) ^ n * (l : bk.S) ^ (k - n) := by
    rw [← pow_add, Nat.add_sub_cancel' hnk]
  refine ⟨fun i j => ?_, fun g i j => ?_⟩
  · have h1 := hβ.1 i j
    have h2 : bk.E ∣ (β - (l : bk.S) ^ n • γ) i j := (dvd_pow_self _ (by omega : m ≠ 0)).trans (hd i j)
    have h3 : bk.E ∣ (l : bk.S) ^ n * (γ - (l : bk.S) ^ (k - n) • (1 : Matrix (Fin d) (Fin d) bk.S)) i j := by
      have : (l : bk.S) ^ n * (γ - (l : bk.S) ^ (k - n) • (1 : Matrix (Fin d) (Fin d) bk.S)) i j =
          (β - (l : bk.S) ^ k • (1 : Matrix (Fin d) (Fin d) bk.S)) i j - (β - (l : bk.S) ^ n • γ) i j := by
        simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, hk]
        ring
      rw [this]
      exact dvd_sub h1 h2
    obtain ⟨c, hc⟩ := h3
    have h4 : bk.ev bk.E ^ 1 ∣ (l : Ainf l) ^ n * bk.ev ((γ - (l : bk.S) ^ (k - n) • (1 : Matrix (Fin d) (Fin d) bk.S)) i j) :=
      ⟨bk.ev c, by rw [pow_one, ← map_mul, ← hc, map_mul, map_pow, map_natCast]⟩
    simpa using (hT 1).2.1 _ (strip 1 n _ h4)
  · set Φ := (F.ε g).map WittVector.frobenius with hΦ
    set σ := Per.σA (g : GQ l) with hσ
    set δ := β - (l : bk.S) ^ n • γ with hδ
    have hev : ∀ p q, bk.ev bk.E ^ m ∣ (δ.map bk.ev) p q := fun p q => by
      obtain ⟨c, hc⟩ := hd p q
      exact ⟨bk.ev c, by rw [Matrix.map_apply, hc, map_mul, map_pow]⟩
    have hσE : bk.ev bk.E ∣ σ (bk.ev bk.E) := by
      have := GlobalTheory.BKLim.BetaBd.dvd_σA_ev_sub bk g bk.E
      simpa using dvd_add this (dvd_refl (bk.ev bk.E))
    have hevσ : ∀ p q, bk.ev bk.E ^ m ∣ ((δ.map bk.ev).map σ) p q := fun p q => by
      obtain ⟨c, hc⟩ := hd p q
      rw [Matrix.map_apply, Matrix.map_apply, hc, map_mul, map_mul, map_pow, map_pow]
      exact Dvd.dvd.mul_right (pow_dvd_pow_of_dvd hσE m) _
    have hβeq : β = (l : bk.S) ^ n • γ + δ := by rw [hδ]; abel
    have hmap : (β.map bk.ev) = (l : Ainf l) ^ n • γ.map bk.ev + δ.map bk.ev := by
      rw [hβeq]; ext p q; simp
    have hmapσ : (β.map bk.ev).map σ = (l : Ainf l) ^ n • (γ.map bk.ev).map σ + (δ.map bk.ev).map σ := by
      rw [hmap]; ext p q; simp
    have hD := hβ.2 g i j
    rw [hmapσ, hmap] at hD
    have hsplit : (Φ * ((l : Ainf l) ^ n • (γ.map bk.ev).map σ + (δ.map bk.ev).map σ) -
        ((l : Ainf l) ^ n • γ.map bk.ev + δ.map bk.ev)) i j =
        (l : Ainf l) ^ n * (Φ * (γ.map bk.ev).map σ - γ.map bk.ev) i j +
          ((Φ * (δ.map bk.ev).map σ) i j - (δ.map bk.ev) i j) := by
      simp only [Matrix.mul_add, Matrix.mul_smul, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      ring
    rw [hsplit] at hD
    have hrest : bk.ev bk.E ^ m ∣ (Φ * (δ.map bk.ev).map σ) i j - (δ.map bk.ev) i j := by
      refine dvd_sub ?_ (hev i j)
      rw [Matrix.mul_apply]
      exact Finset.dvd_sum fun k _ => Dvd.dvd.mul_left (hevσ k j) _
    exact strip m n _ ((dvd_add_left hrest).1 hD)

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinLatticeFrameLimitGaloisInvariant
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.BKLim.BinfInv

private theorem exists_isEps_pt (l : ℕ) [Fact l.Prime] : ∃ e : Per.Fl l, IsEps e := by
  obtain ⟨ζ, ε, h0, -, h1, hr⟩ := GlobalTheory.T.exists_compatible_rootsOfUnity_and_tilt_padic l
  refine ⟨ε, ?_, ?_⟩
  · have := hr 0
    rw [h0, map_one] at this
    exact Subtype.ext this
  · intro h
    have := hr 1
    have e : rootT ε 1 = 1 := h
    rw [e] at this
    apply h1
    apply (algebraMap (Om l) ℂ_[l]).injective
    rw [← this, map_one]
    rfl

private theorem algebraMap_mem_filtration_one_iff_mem_ker (l : ℕ) [Fact l.Prime] (a : Per.AinfP l) :
    algebraMap (Per.AinfP l) (Per.BdRp l) a ∈ Per.FilP l 1 ↔ a ∈ Per.kerP l := by
  rw [GlobalTheory.RingIface.mem_filtration_iff_mem_kerTheta_pow, GlobalTheory.RingIface.ev_alg, Ideal.Quotient.eq_zero_iff_mem, pow_one]

private theorem galoisAction_mem_filtration (l : ℕ) [Fact l.Prime] (g : Per.Gq l) (n : ℕ) (y : Per.BdRp l)
    (hy : y ∈ Per.FilP l n) : Per.σDp g y ∈ Per.FilP l n := by
  obtain ⟨e, he⟩ := exists_isEps_pt l
  obtain ⟨hP, -, -, -⟩ := GlobalTheory.MemLoc.filtration_eq_xi_pow l e he
  have hξ : aDp l (xi e) ∈ Per.FilP l 1 := (hP 1 _).2 (by rw [pow_one])
  have ha : aDp l (xi e) = algebraMap (Per.AinfP l) (Per.BdRp l)
      (algebraMap (Per.Ainf l) (Per.AinfP l) (xi e)) := by
    unfold aDp
    rw [RingHom.comp_apply]
  have hσ : Per.σDp g (aDp l (xi e)) ∈ Per.FilP l 1 := by
    rw [ha] at hξ ⊢
    rw [GlobalTheory.RingIface.sigDp_alg, algebraMap_mem_filtration_one_iff_mem_ker]
    exact GlobalTheory.RingBasics.ker_σ g ((algebraMap_mem_filtration_one_iff_mem_ker l _).1 hξ)
  have hd : aDp l (xi e) ∣ Per.σDp g (aDp l (xi e)) := by
    simpa only [pow_one] using (hP 1 _).1 hσ
  refine (hP n _).2 ((pow_dvd_pow_of_dvd hd n).trans ?_)
  rw [← map_pow]
  exact map_dvd _ ((hP n _).1 hy)

theorem σDp_mem_FilP {l : ℕ} [Fact l.Prime] (g : Per.Gq l) (m : ℕ) {x : Per.BdRp l}
    (hx : x ∈ Per.FilP l m) : Per.σDp g x ∈ Per.FilP l m :=
  galoisAction_mem_filtration l g m x hx

theorem eq_of_forall_mem_FilP {l : ℕ} [Fact l.Prime] {x : Per.BdRp l}
    (hx : ∀ m, x ∈ Per.FilP l m) : x = 0 :=
  GlobalTheory.RingIface.ev_ext l x 0 fun m =>
    ((GlobalTheory.RingIface.mem_filtration_iff_mem_kerTheta_pow l m x).1 (hx m)).trans (map_zero (Per.ev l m)).symm

theorem inv : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (N d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (F : Frame bk N d ρ) (B : Matrix (Fin d) (Fin d) (Per.BdRp l)), (∀ m : ℕ, ∃ (k : ℕ) (β : Matrix (Fin d) (Fin d) bk.S), F.IsBeta m k β ∧ ∀ i j, aDp l (bk.ev (β i j)) - (l : Per.BdRp l) ^ k * B i j ∈ Per.FilP l m) → ∀ g : ↥(GK K), (F.ε g).map ((aDp l).comp WittVector.frobenius) * B.map (Per.σDp (g : GQ l)) = B := by
  intro l _ K bk N d ρ F B hB g
  ext i j
  rw [← sub_eq_zero]
  refine eq_of_forall_mem_FilP fun m => ?_
  obtain ⟨k, β, hβ, hb⟩ := hB m
  set σ := Per.σDp (g : GQ l) with hσ
  set Φ := (F.ε g).map ((aDp l).comp WittVector.frobenius) with hΦ
  set b : Matrix (Fin d) (Fin d) (Per.BdRp l) := β.map ((aDp l).comp bk.ev) with hbdef
  have h1 := ((GlobalTheory.AinfEPow.ePow_facts l K bk m).2.2.1 _).2 (hβ.2 g i j)
  have h1' : (Φ * b.map σ - b) i j ∈ Per.FilP l m := by
    convert h1 using 1
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.sub_apply, Matrix.mul_apply, map_sub, map_sum, map_mul, Matrix.map_apply, hΦ, hbdef, hσ,
      RingHom.comp_apply, GlobalTheory.MemLoc.ActLaws.σDp_aDp]
  have h2 : ∀ x y, (l : Per.BdRp l) ^ k * B x y - b x y ∈ Per.FilP l m := fun x y => by
    have := (Ideal.neg_mem_iff _).2 (hb x y)
    simpa [hbdef, neg_sub] using this
  have key : (l : Per.BdRp l) ^ k * ((Φ * B.map σ) i j - B i j) =
      (Φ * b.map σ - b) i j + ∑ x, Φ i x * σ ((l : Per.BdRp l) ^ k * B x j - b x j) +
        (b i j - (l : Per.BdRp l) ^ k * B i j) := by
    simp only [Matrix.sub_apply, Matrix.mul_apply, Matrix.map_apply, map_sub, map_mul, map_pow, map_natCast,
      mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
    have e : ∑ x, Φ i x * ((l : Per.BdRp l) ^ k * σ (B x j)) = ∑ x, (l : Per.BdRp l) ^ k * (Φ i x * σ (B x j)) :=
      Finset.sum_congr rfl fun _ _ => by ring
    rw [e]
    ring
  have h3 : (l : Per.BdRp l) ^ k * ((Φ * B.map σ) i j - B i j) ∈ Per.FilP l m := by
    rw [key]
    refine Ideal.add_mem _ (Ideal.add_mem _ h1' (Ideal.sum_mem _ fun x _ => Ideal.mul_mem_left _ _ ?_)) (by simpa [hbdef] using hb i j)
    exact σDp_mem_FilP _ m (h2 x j)
  obtain ⟨u, hu⟩ := ((GlobalTheory.MemLoc.isUnit_l_BdRp l).pow k).exists_left_inv
  have := Ideal.mul_mem_left _ u h3
  rwa [← mul_assoc, hu, one_mul] at this

end GlobalTheory.BKLim.BinfInv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPrismHomExtOfX
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP.BK

theorem hom_ext_of_hf_X : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (C : Obj l ↥(OL K))
    (g g' : Hom bk.prism C), BK.hf g X = BK.hf g' X → g = g' := by
  intro l _ K bk C g g' hX

  have hI : ∀ x : bk.S, BK.hf g x - BK.hf g' x ∈ C.I := by
    intro x
    have hr : Ideal.Quotient.mk bk.prism.I x = bk.prism.str (bk.str.symm (Ideal.Quotient.mk _ x)) :=
      (bk.str.apply_symm_apply _).symm
    have h1 := g.f_str _ x hr
    have h2 := g'.f_str _ x hr
    exact Ideal.Quotient.eq.1 (h1.trans h2.symm)
  have hH : IsHausdorff (JJ C) C.A := C.complete.toIsHausdorff

  have hCC : (BK.hf g).comp (PowerSeries.C (R := Wq l bk.a)) = (BK.hf g').comp PowerSeries.C :=
    _root_.GlobalTheory.wittVector_ringHom_eq_of_sub_mem l (Fq l bk.a) C.A (JJ C) (Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)) hH _ _
      (fun w => Ideal.mem_sup_right (hI _))

  have hP : ∀ p : Polynomial (Wq l bk.a), BK.hf g (p : bk.S) = BK.hf g' (p : bk.S) := by
    have h := Polynomial.ringHom_ext (f := (BK.hf g).comp (Polynomial.coeToPowerSeries.ringHom))
      (g := (BK.hf g').comp Polynomial.coeToPowerSeries.ringHom)
      (fun a => by
        simp only [RingHom.comp_apply, Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_C]
        exact RingHom.congr_fun hCC a)
      (by simp only [RingHom.comp_apply, Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_X]; exact hX)
    intro p
    exact RingHom.congr_fun h p

  have hXe : ∃ q : bk.S, (X : bk.S) ^ bk.Ep.natDegree = bk.E - (l : bk.S) * q := by
    have hd : Polynomial.C (l : Wq l bk.a) ∣ bk.Ep - Polynomial.X ^ bk.Ep.natDegree := by
      rw [Polynomial.C_dvd_iff_dvd_coeff]
      intro i
      rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow]
      rcases lt_trichotomy i bk.Ep.natDegree with h | h | h
      · rw [if_neg h.ne, sub_zero]; exact bk.dvd_coeff i h
      · rw [if_pos h, h, bk.monic.coeff_natDegree, sub_self]; exact dvd_zero _
      · rw [if_neg h.ne', sub_zero, Polynomial.coeff_eq_zero_of_natDegree_lt h]; exact dvd_zero _
    obtain ⟨q, hq⟩ := hd
    refine ⟨(q : bk.S), ?_⟩
    have h := congrArg (fun p : Polynomial (Wq l bk.a) => (p : bk.S)) hq
    rw [Polynomial.coe_sub, Polynomial.coe_pow, Polynomial.coe_X, Polynomial.coe_mul,
      Polynomial.coe_C, map_natCast] at h
    show _ = (bk.Ep : bk.S) - _
    linear_combination -h
  obtain ⟨q, hq⟩ := hXe
  have hgXe : BK.hf g X ^ bk.Ep.natDegree ∈ JJ C := by
    rw [← map_pow, hq, map_sub, map_mul, map_natCast]
    refine Ideal.sub_mem _ (Ideal.mem_sup_right (g.f_I _ (Ideal.mem_span_singleton_self _)))
      (Ideal.mem_sup_left (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)))

  have hsplit : ∀ (N : ℕ) (f : bk.S), ∃ (p : Polynomial (Wq l bk.a)) (h : bk.S), f = (p : bk.S) + X ^ N * h := by
    intro N f
    obtain ⟨h, hh⟩ := (PowerSeries.X_pow_dvd_iff (n := N)
      (φ := f - ((trunc N f : Polynomial (Wq l bk.a)) : bk.S))).2 (fun m hm => by
        rw [map_sub, Polynomial.coeff_coe, coeff_trunc, if_pos hm, sub_self])
    exact ⟨_, h, by rw [← hh]; ring⟩
  apply Hom.ext'
  refine RingHom.ext fun f => ?_
  change BK.hf g f = BK.hf g' f
  have key : ∀ n : ℕ, BK.hf g f - BK.hf g' f ∈ JJ C ^ n := by
    intro n
    obtain ⟨p, h, hh⟩ := hsplit (bk.Ep.natDegree * n) f
    have e : ∀ φ : bk.S →+* C.A, φ f = φ (p : bk.S) + φ X ^ (bk.Ep.natDegree * n) * φ h := fun φ => by
      have := congrArg φ hh
      rwa [map_add, map_mul, map_pow] at this
    have hm : BK.hf g X ^ (bk.Ep.natDegree * n) ∈ JJ C ^ n := by
      rw [pow_mul]; exact Ideal.pow_mem_pow hgXe n
    have e2 : BK.hf g f - BK.hf g' f = BK.hf g X ^ (bk.Ep.natDegree * n) * (BK.hf g h - BK.hf g' h) := by
      have hXN : BK.hf g' X ^ (bk.Ep.natDegree * n) = BK.hf g X ^ (bk.Ep.natDegree * n) := by rw [hX]
      linear_combination e (BK.hf g) - e (BK.hf g') + hP p - BK.hf g' h * hXN
    rw [e2]
    exact Ideal.mul_mem_right _ _ hm
  refine sub_eq_zero.1 (hH.haus _ fun n => ?_)
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
  exact key n

end GlobalTheory.BSP.BK
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinQuotientEisensteinCompactness
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BKLim.Cpt

theorem of_add {R : Type} (Q : ℕ → R → Prop) (hmono : ∀ n x, Q (n + 1) x → Q n x) :
    ∀ n k x, Q (n + k) x → Q n x := by
  intro n k x
  induction k with
  | zero => exact id
  | succ k ih => exact fun h => ih (hmono _ _ (by rwa [← add_assoc] at h))

def Good {R : Type} [CommRing R] {ι : Type} (I : ℕ → Ideal R) (Q : ℕ → (ι → R) → Prop) (n : ℕ) (y : ι → R) :
    Prop :=
  ∀ k, n ≤ k → ∃ x, Q k x ∧ ∀ i, x i - y i ∈ I n

theorem exists_seq {R : Type} [CommRing R] (I : ℕ → Ideal R) (hI : ∀ n, I (n + 1) ≤ I n) (hI0 : I 0 = ⊤)
    (hfin : ∀ n, Finite (R ⧸ I n)) (ι : Type) [Finite ι] (Q : ℕ → (ι → R) → Prop)
    (hmono : ∀ n x, Q (n + 1) x → Q n x) (hcong : ∀ n x y, Q n x → (∀ i, x i - y i ∈ I n) → Q n y)
    (hex : ∀ n, ∃ x, Q n x) :
    ∃ y : ℕ → ι → R, (∀ n, Q n (y n)) ∧ ∀ n i, y (n + 1) i - y n i ∈ I n := by
  classical
  have step : ∀ n y, Good I Q n y → ∃ y', Good I Q (n + 1) y' ∧ ∀ i, y' i - y i ∈ I n := by
    intro n y hy
    by_contra hne
    haveI : Finite (ι → R ⧸ I (n + 1)) := by haveI := hfin (n + 1); infer_instance
    let rep : (ι → R ⧸ I (n + 1)) → ι → R := fun t i => Classical.choose (Ideal.Quotient.mk_surjective (t i))
    have hrep : ∀ t i, Ideal.Quotient.mk (I (n + 1)) (rep t i) = t i :=
      fun t i => Classical.choose_spec (Ideal.Quotient.mk_surjective (t i))
    let P : (ι → R ⧸ I (n + 1)) → Prop := fun t =>
      ∃ k, n + 1 ≤ k ∧ ¬ ∃ x, Q k x ∧ ∀ i, x i - rep t i ∈ I (n + 1)
    let kf : (ι → R ⧸ I (n + 1)) → ℕ := fun t => if h : P t then h.choose else 0
    have hkf : ∀ t (h : P t), kf t = h.choose := fun t h => dif_pos h
    obtain ⟨t0, ht0⟩ := Finite.exists_max kf
    obtain ⟨x, hx, hxy⟩ := hy (n + kf t0) (Nat.le_add_right _ _)
    let t : ι → R ⧸ I (n + 1) := fun i => Ideal.Quotient.mk _ (x i)
    have hxt : ∀ i, x i - rep t i ∈ I (n + 1) := fun i =>
      Ideal.Quotient.eq.1 (hrep t i).symm
    have hty : ∀ i, rep t i - y i ∈ I n := fun i => by
      have : rep t i - y i = (x i - y i) - (x i - rep t i) := by ring
      rw [this]
      exact sub_mem (hxy i) (hI n (hxt i))
    have hng : ¬ Good I Q (n + 1) (rep t) := fun hg => hne ⟨rep t, hg, hty⟩
    have hP : P t := by
      by_contra hc
      refine hng fun k hk => ?_
      by_contra hk'
      exact hc ⟨k, hk, hk'⟩
    have hs := hP.choose_spec
    rw [← hkf t hP] at hs
    refine hs.2 ⟨x, ?_, hxt⟩
    have hle : kf t ≤ n + kf t0 := (ht0 t).trans (Nat.le_add_left _ _)
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
    exact of_add Q hmono (kf t) d x (hd ▸ hx)
  choose! f hf1 hf2 using step
  let seq : ℕ → ι → R := fun n => Nat.rec (motive := fun _ => ι → R) 0 (fun n y => f n y) n
  have hgood : ∀ n, Good I Q n (seq n) := by
    intro n
    induction n with
    | zero =>
      intro k _
      obtain ⟨x, hx⟩ := hex k
      exact ⟨x, hx, fun i => by rw [hI0]; exact Submodule.mem_top⟩
    | succ n ih => exact hf1 n (seq n) ih
  refine ⟨seq, fun n => ?_, fun n i => hf2 n (seq n) (hgood n) i⟩
  obtain ⟨x, hx, hxs⟩ := hgood n n le_rfl
  exact hcong n x (seq n) hx hxs

variable {l : ℕ} [hl : Fact l.Prime] {K : FinExt l}

theorem X_pow_mem (bk : BK K) (n m : ℕ) :
    (X : bk.S) ^ (bk.Ep.natDegree * (n + m)) ∈ Ideal.span {(l : bk.S) ^ n} ⊔ Ideal.span {bk.E ^ m} := by
  have h1 : (X : bk.S) ^ (bk.Ep.natDegree * (n + m)) ∈
      (Ideal.span {(l : bk.S)} ⊔ Ideal.span {bk.E}) ^ (n + m) := by
    rw [pow_mul]; exact Ideal.pow_mem_pow (BK.X_pow_natDegree_mem bk) _
  have h2 := Ideal.sup_pow_add_le_pow_sup_pow (I := Ideal.span {(l : bk.S)}) (J := Ideal.span {bk.E})
    (n := n) (m := m)
  rw [Ideal.span_singleton_pow, Ideal.span_singleton_pow] at h2
  exact h2 h1

theorem finite_quot (bk : BK K) (n m : ℕ) :
    Finite (bk.S ⧸ (Ideal.span {(l : bk.S) ^ n} ⊔ Ideal.span {bk.E ^ m})) := by
  haveI := _root_.GlobalTheory.BKFin.finite_quot l K bk n (bk.Ep.natDegree * (n + m))
  have H : Ideal.span {(l : bk.S) ^ n} ⊔ Ideal.span {(X : bk.S) ^ (bk.Ep.natDegree * (n + m))} ≤
      Ideal.span {(l : bk.S) ^ n} ⊔ Ideal.span {bk.E ^ m} :=
    sup_le le_sup_left ((Ideal.span_singleton_le_iff_mem _).2 (X_pow_mem bk n m))
  refine Finite.of_surjective (Ideal.Quotient.factor H) fun y => ?_
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
  exact ⟨Ideal.Quotient.mk _ x, rfl⟩

theorem exists_lim (bk : BK K) (m : ℕ) (s : ℕ → bk.S)
    (hs : ∀ n, s (n + 1) - s n ∈ Ideal.span {(l : bk.S) ^ n} ⊔ Ideal.span {bk.E ^ m}) :
    ∃ L : bk.S, ∀ n, s (n + m) - L ∈ Ideal.span {(l : bk.S) ^ n} ⊔ Ideal.span {bk.E ^ m} := by
  have hd : ∀ n, ∃ a b : bk.S, s (n + 1) - s n = (l : bk.S) ^ n * a + bk.E ^ m * b := by
    intro n
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 (hs n)
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hy
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 hz
    exact ⟨a, b, by rw [← hyz]; ring⟩
  choose a b hab using hd
  let z : ℕ → bk.S := fun n => s n - bk.E ^ m * ∑ k ∈ Finset.range n, b k
  have hz1 : ∀ n, z (n + 1) - z n = (l : bk.S) ^ n * a n := by
    intro n
    simp only [z, Finset.sum_range_succ]
    linear_combination hab n
  have hcau : ∀ n N, n ≤ N → z N - z n ∈ Ideal.span {(l : bk.S) ^ n} := by
    intro n N hN
    induction N, hN using Nat.le_induction with
    | base => simp
    | succ N hN ih =>
      have : z (N + 1) - z n = (z (N + 1) - z N) + (z N - z n) := by ring
      rw [this, hz1]
      exact add_mem (Ideal.mem_span_singleton.2 (dvd_mul_of_dvd_left (pow_dvd_pow _ hN) _)) ih
  have hJ : ∀ n, Ideal.span {(l : bk.S) ^ n} ≤ bk.J ^ n := fun n => by
    rw [← Ideal.span_singleton_pow]; exact Ideal.pow_right_mono le_sup_left n
  obtain ⟨L, hL⟩ := bk.complete.toIsPrecomplete.prec (f := z) (fun {p q} hpq => by
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, ← neg_sub]
    exact neg_mem (hJ p (hcau p q hpq)))
  refine ⟨L, fun n => ?_⟩
  have h1 := hL (n + m)
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at h1
  have h2 := Ideal.sup_pow_add_le_pow_sup_pow (I := Ideal.span {(l : bk.S)}) (J := Ideal.span {bk.E})
    (n := n) (m := m)
  rw [Ideal.span_singleton_pow, Ideal.span_singleton_pow] at h2
  have : s (n + m) - L = (z (n + m) - L) + bk.E ^ m * ∑ k ∈ Finset.range (n + m), b k := by
    simp only [z]; ring
  rw [this]
  exact add_mem (h2 h1) (Ideal.mem_sup_right (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)))

theorem compact : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (ι : Type) [Finite ι] (m : ℕ)
    (Q : ℕ → (ι → bk.S) → Prop), (∀ n x, Q (n + 1) x → Q n x) →
    (∀ n x y, Q n x → (∀ i, x i - y i ∈ Ideal.span {(l : bk.S) ^ n} ⊔ Ideal.span {bk.E ^ m}) → Q n y) →
    (∀ n, ∃ x, Q n x) → ∃ x, ∀ n, Q n x := by
  intro l _ K bk ι _ m Q hmono hcong hex
  obtain ⟨y, hQ, hy⟩ := exists_seq (fun n => Ideal.span {(l : bk.S) ^ n} ⊔ Ideal.span {bk.E ^ m})
    (fun n => sup_le_sup_right (Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow _ (Nat.le_succ n))) _)
    (by simp) (fun n => finite_quot bk n m) ι Q hmono hcong hex
  choose L hL using fun i => exists_lim bk m (fun n => y n i) (fun n => hy n i)
  exact ⟨L, fun n => hcong n _ _ (of_add Q hmono n m _ (hQ (n + m))) (fun i => hL i n)⟩

end GlobalTheory.BKLim.Cpt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CocycleMemCoboundariesOfTateOrthogonalStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cocycle_mem_coboundaries_of_tate_orthogonal : Formalism.GaloisCohomology.LocalTateDualityK → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O) (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDual1 (P.PD K) A.ρ A'.ρ m → ∀ b ∈ continuousCocycles A'.ρ, (∀ a ∈ continuousCocycles A.ρ, CobL (P.PD K) (cupL A'.ρ m a b)) → b ∈ B1 A'.ρ := by
  first | exact @GlobalTheory.TateOrthV.cocycle_mem_coboundaries_of_tate_orthogonal' | exact GlobalTheory.TateOrthV.cocycle_mem_coboundaries_of_tate_orthogonal' | (intros; apply GlobalTheory.TateOrthV.cocycle_mem_coboundaries_of_tate_orthogonal' <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRingSqZeroNilpotentAugmentedStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ring_sq_zero_nilpotent_augmented : ∀ (O A : Type) [CommRing O] [CommRing A] [Algebra O A] (m : ℕ), 0 < m → ∃ (B : Type) (_ : CommRing B) (_ : Algebra O B) (j : A →ₐ[O] B) (π : B →ₐ[O] A) (x y : B), (∀ a, π (j a) = a) ∧ (∀ b, π b = 0 → b ∈ Ideal.span {x, y}) ∧ π x = 0 ∧ π y = 0 ∧ x * x = 0 ∧ y ^ m = 0 ∧ ∀ f, x * y ^ (m - 1) * f = 0 → π f = 0 := by
  first | exact @GlobalTheory.SqZeroPow.exists_ring | exact GlobalTheory.SqZeroPow.exists_ring | (intros; apply GlobalTheory.SqZeroPow.exists_ring <;> assumption)
end

