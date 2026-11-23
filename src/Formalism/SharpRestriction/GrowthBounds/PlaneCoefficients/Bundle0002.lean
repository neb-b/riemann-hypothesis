module

public import Formalism.SharpRestriction.GrowthBounds.PlaneCoefficients.PlaneCoeffOneTTens
public import Formalism.SharpRestriction.GrowthBounds.PlaneCoefficients.NoOpStep
public import Formalism.SharpRestriction.GrowthBounds.TwistedSubstitution.TwistedMonomialFiltration.TwistSubXMemSupported

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.PlaneCoefficients.PmatDetMem
section
noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.PairMembershipBlocks

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords Formalism.MainNotions.G.WittFrameLocaliserOrders

theorem det_mem_sub {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] (S : Subalgebra R A) {r : ℕ}
    (M : Matrix (Fin r) (Fin r) A) (h : ∀ i j, M i j ∈ S) : M.det ∈ S := by
  rw [Matrix.det_apply]
  refine Subalgebra.sum_mem _ fun σ _ => ?_
  rw [Units.smul_def]
  exact Subalgebra.zsmul_mem _ (Subalgebra.prod_mem _ fun i _ => h _ _) _

theorem X_mem_supp {R σ : Type*} [CommRing R] (s : Set σ) (i : σ) (hi : i ∈ s) :
    (X i : MvPolynomial σ R) ∈ supported R s := by
  rw [supported_eq_adjoin_X]
  exact Algebra.subset_adjoin (Set.mem_image_of_mem _ hi)

theorem pmat_det_mem (R : Type) [CommRing R] {n' r k : ℕ} (hrk : r ≤ k) (A : Fin r → Fin n') (P : Fin r → ℕ)
    (hA : ∀ l, Even (A l).val) :
    (pmat R hrk A P).det ∈ supported R {v : TV n' k | v.2.val < r ∧ Even v.1.val} := by
  apply det_mem_sub
  intro l i
  unfold pmat
  rw [Matrix.of_apply]
  exact Subalgebra.pow_mem _ (X_mem_supp {v : TV n' k | v.2.val < r ∧ Even v.1.val} (A l, Fin.castLE hrk i)
    (show (Fin.castLE hrk i).val < r ∧ Even (A l).val from ⟨i.isLt, hA l⟩)) _

theorem restSP : RestSP := by
  intro p n' r k _ R _ F hrk c' Q L₁ N₁ hV hn hr ga hga v hv
  have hfr : ∀ (j : ℤ) (l : Fin r), Even (posOf n' (F.fr j l.val)).val := fun j l =>
    (posOf_even hn _).2 (hV.2.2.2.2.1 j l.val l.isLt).2
  have hAr : ∀ (s : ℤ) (l : Fin r), Even (posOf n' (Arow F s l.val)).val := fun s l =>
    (posOf_even hn _).2 (window_holds_even_tops n' r F L₁ N₁ hV hn hr s l.val l.isLt).1
  have hmem : SPR R p F hrk c' Q ∈ supported R {v : TV n' k | v.2.val < r ∧ Even v.1.val} := by
    unfold SPR
    refine Subalgebra.mul_mem _ (Subalgebra.mul_mem _ (Subalgebra.pow_mem _ (Subalgebra.prod_mem _ fun j _ => ?_) _)
      (Subalgebra.prod_mem _ fun j _ => ?_)) (Subalgebra.prod_mem _ fun s _ => ?_)
    · exact Subalgebra.pow_mem _ (pmat_det_mem R hrk _ _ (hfr j)) _
    · exact Subalgebra.pow_mem _ (pmat_det_mem R hrk _ _ (hfr j)) _
    · exact Subalgebra.pow_mem _ (pmat_det_mem R hrk _ _ (hAr _)) _
  have hvars : v ∈ (SPR R p F hrk c' Q).vars :=
    (mem_vars_iff_mem_support v).2 ⟨ga, hga, Finsupp.mem_support_iff.2 hv⟩
  exact (mem_supported.1 hmem) (Finset.mem_coe.2 hvars)

end Formalism.MainNotions.PairMembershipBlocks
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.PlaneCoefficients.TensZeroRight
section
noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.PairMembershipBlocks.T5

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords Formalism.MainNotions.G.GLWeightTheory Formalism.MainNotions.PairMembershipBlocks

section Lin

variable {σ τ Kf : Type} [Field Kf]

theorem tens_monomial (mo : σ →₀ ℕ) (c : Kf) (G : MvPolynomial τ Kf) :
    tens (monomial mo c) G = monomial mo (c • G) := by
  unfold tens
  by_cases hc : c = 0
  · simp [hc]
  · rw [support_monomial, if_neg hc, Finset.sum_singleton, coeff_monomial, if_pos rfl]

def tensH (G : MvPolynomial τ Kf) (mo : σ →₀ ℕ) : Kf →+ MvPolynomial σ (MvPolynomial τ Kf) where
  toFun c := monomial mo (c • G)
  map_zero' := by simp
  map_add' c c' := by rw [add_smul, map_add (f := _)]

theorem tens_add_left (A A' : MvPolynomial σ Kf) (G : MvPolynomial τ Kf) :
    tens (A + A') G = tens A G + tens A' G :=
  sumSupp_add (tensH G) A A'

theorem tens_add_right (A : MvPolynomial σ Kf) (G G' : MvPolynomial τ Kf) :
    tens A (G + G') = tens A G + tens A G' := by
  unfold tens
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun mo _ => ?_
  rw [smul_add, map_add (f := _)]

theorem tens_zero_left (G : MvPolynomial τ Kf) : tens (0 : MvPolynomial σ Kf) G = 0 := by simp [tens]

theorem tens_zero_right (A : MvPolynomial σ Kf) : tens A (0 : MvPolynomial τ Kf) = 0 := by simp [tens]

theorem compD_add {ι : Type} {s : ℕ} (d : ι → ℕ) (H H' : MvPolynomial (ι × Fin s) Kf) :
    compD d (H + H') = compD d H + compD d H' :=
  sumFilt_add (fun mo => ∀ x, multideg mo x = d x) (fun mo => (monomial mo : Kf →ₗ[Kf] _).toAddMonoidHom) H H'

theorem compD_zero {ι : Type} {s : ℕ} (d : ι → ℕ) : compD d (0 : MvPolynomial (ι × Fin s) Kf) = 0 := by simp [compD]

theorem compD_monomial {ι : Type} {s : ℕ} (d : ι → ℕ) (mo : ι × Fin s →₀ ℕ) (c : Kf) :
    compD d (monomial mo c) = if (∀ x, multideg mo x = d x) then monomial mo c else 0 := by
  unfold compD
  by_cases hc : c = 0
  · simp [hc]
  · rw [support_monomial, if_neg hc, Finset.filter_singleton]
    split_ifs with h
    · rw [Finset.sum_singleton, coeff_monomial, if_pos rfl]
    · rw [Finset.sum_empty]

theorem add_expand {R M : Type*} [CommSemiring R] [AddCommMonoid M] (f : MvPolynomial σ R → M) (h0 : f 0 = 0)
    (hadd : ∀ x y, f (x + y) = f x + f y) (P : MvPolynomial σ R) :
    f P = ∑ a ∈ P.support, f (monomial a (P.coeff a)) := by
  have h := map_sum (AddMonoidHom.mk ⟨f, h0⟩ hadd) (fun a => monomial a (P.coeff a)) P.support
  conv_lhs => rw [P.as_sum]
  exact h

end Lin

section Lev

variable {n' r K m : ℕ} [NeZero n'] (Fr : Frames n' r) (p : ℕ) {O : Type} [CommRing O] [IsDomain O]
  (hk : m + 1 = r + K) {J : ℕ} [NeZero J] (nL : ZMod J → ℕ)

theorem monomialSubstitution_add (F G : MvPolynomial (TV n' (m + 1)) (KK O)) :
    levP Fr p hk nL (F + G) = levP Fr p hk nL F + levP Fr p hk nL G :=
  sumSupp_add (fun mo => (monomial (plMon Fr p hk nL mo) : KK O →ₗ[KK O] _).toAddMonoidHom) F G

theorem levN_add (F G : MvPolynomial (TV n' (m + 1)) (KK O)) :
    levN Fr p hk nL (F + G) = levN Fr p hk nL F + levN Fr p hk nL G :=
  sumSupp_add (fun mo => (monomial (noMon Fr p hk nL mo) : KK O →ₗ[KK O] _).toAddMonoidHom) F G

theorem monomialSubstitution_zero : levP Fr p hk nL (0 : MvPolynomial (TV n' (m + 1)) (KK O)) = 0 := by simp [levP]

theorem levN_zero : levN Fr p hk nL (0 : MvPolynomial (TV n' (m + 1)) (KK O)) = 0 := by simp [levN]

theorem monomialSubstitution_monomial (mo : TV n' (m + 1) →₀ ℕ) (c : KK O) :
    levP Fr p hk nL (monomial mo c) = monomial (plMon Fr p hk nL mo) c := by
  unfold levP
  by_cases hc : c = 0
  · simp [hc]
  · rw [support_monomial, if_neg hc, Finset.sum_singleton, coeff_monomial, if_pos rfl]

theorem levN_monomial (mo : TV n' (m + 1) →₀ ℕ) (c : KK O) :
    levN Fr p hk nL (monomial mo c) = monomial (noMon Fr p hk nL mo) c := by
  unfold levN
  by_cases hc : c = 0
  · simp [hc]
  · rw [support_monomial, if_neg hc, Finset.sum_singleton, coeff_monomial, if_pos rfl]

theorem levImg_monomial (rho : TL J nL r × Fin (r + K) → ℕ) (dPl dNo : TL J nL r → ℕ) (mo : TV n' (m + 1) →₀ ℕ)
    (c : KK O) :
    levImg Fr p hk nL rho dPl dNo (monomial mo c) =
      if InLow Fr p hk nL rho mo ∧ InBlock Fr p hk nL dPl dNo mo then
        monomial (plMon Fr p hk nL mo) (monomial (noMon Fr p hk nL mo) c) else 0 := by
  unfold levImg
  by_cases hc : c = 0
  · simp [hc]
  · rw [support_monomial, if_neg hc, Finset.filter_singleton]
    split_ifs with h
    · rw [Finset.sum_singleton, coeff_monomial, if_pos rfl]
    · rw [Finset.sum_empty]

theorem inBlock_iff (dPl dNo : TL J nL r → ℕ) (mo : TV n' (m + 1) →₀ ℕ) :
    InBlock Fr p hk nL dPl dNo mo ↔
      (∀ x, multideg (plMon Fr p hk nL mo) x = dPl x) ∧ ∀ x, multideg (noMon Fr p hk nL mo) x = dNo x := by
  unfold InBlock multideg plMon noMon
  simp only [Finsupp.coe_equivFunOnFinite_symm]

theorem plMon_eq_zero (mo : TV n' (m + 1) →₀ ℕ) (h : ∀ x a, mo (plVar Fr hk nL x a) = 0) :
    plMon Fr p hk nL mo = 0 := by
  ext v
  simp only [plMon, Finsupp.coe_equivFunOnFinite_symm, Finsupp.coe_zero, Pi.zero_apply, h, Nat.zero_div]

theorem noMon_eq_zero (mo : TV n' (m + 1) →₀ ℕ) (h : ∀ x b, mo (noVar Fr hk nL x b) < lowP Fr p x) :
    noMon Fr p hk nL mo = 0 := by
  ext v
  simp only [noMon, Finsupp.coe_equivFunOnFinite_symm, Finsupp.coe_zero, Pi.zero_apply]
  exact Nat.div_eq_of_lt (h v.1 v.2)

theorem lev_term (hp : 0 < p) (base d b : TV n' (m + 1) →₀ ℕ) (hd : LowDiv Fr p hk nL d)
    (hd0 : ∀ x c, d (noVar Fr hk nL x c) = 0) (hb : LowDiv Fr p hk nL b) (hb0 : ∀ x a, b (plVar Fr hk nL x a) = 0)
    (hbase : ∀ x c, base (noVar Fr hk nL x c) < lowP Fr p x)
    (rho : TL J nL r × Fin (r + K) → ℕ) (dPl dNo : TL J nL r → ℕ) (u v : KK O) :
    levImg Fr p hk nL rho dPl dNo (monomial (base + d) u * monomial b v) =
      if InLow Fr p hk nL rho base then
        tens (compD dPl (levP Fr p hk nL (monomial (base + d) u))) (compD dNo (levN Fr p hk nL (monomial b v)))
      else 0 := by
  have e1 : InLow Fr p hk nL rho (base + d + b) ↔ InLow Fr p hk nL rho base := by
    rw [add_assoc]
    exact inLow_add Fr p hk nL rho base (d + b) (lowDiv_add Fr p hk nL hd hb)
  have e2 : plMon Fr p hk nL (base + d + b) = plMon Fr p hk nL (base + d) := by
    rw [plMon_add Fr p hk nL hp _ _ hb, plMon_eq_zero Fr p hk nL b hb0, add_zero]
  have e3 : noMon Fr p hk nL (base + d + b) = noMon Fr p hk nL b := by
    rw [noMon_add Fr p hk nL hp _ _ hb, noMon_eq_zero Fr p hk nL (base + d), zero_add]
    intro x c
    rw [Finsupp.add_apply, hd0, add_zero]
    exact hbase x c
  rw [monomial_mul, levImg_monomial, monomialSubstitution_monomial, levN_monomial, compD_monomial, compD_monomial, inBlock_iff, e1, e2,
    e3]
  by_cases h1 : InLow Fr p hk nL rho base
  · rw [if_pos h1]
    by_cases h2 : ∀ x, multideg (plMon Fr p hk nL (base + d)) x = dPl x
    · by_cases h3 : ∀ x, multideg (noMon Fr p hk nL b) x = dNo x
      · rw [if_pos ⟨h1, h2, h3⟩, if_pos h2, if_pos h3, tens_monomial, smul_monomial, smul_eq_mul]
      · rw [if_neg (fun h => h3 h.2.2), if_neg h3, tens_zero_right]
    · rw [if_neg (fun h => h2 h.2.1), if_neg h2, tens_zero_left]
  · rw [if_neg h1, if_neg (fun h => h1 h.1)]

theorem lev_mul (hp : 0 < p) (base : TV n' (m + 1) →₀ ℕ) (P Q : MvPolynomial (TV n' (m + 1)) (KK O))
    (hP : ∀ a ∈ P.support, ∃ d, LowDiv Fr p hk nL d ∧ (∀ x c, d (noVar Fr hk nL x c) = 0) ∧ a = base + d)
    (hQ : ∀ b ∈ Q.support, LowDiv Fr p hk nL b ∧ ∀ x a, b (plVar Fr hk nL x a) = 0)
    (hbase : ∀ x c, base (noVar Fr hk nL x c) < lowP Fr p x)
    (rho : TL J nL r × Fin (r + K) → ℕ) (dPl dNo : TL J nL r → ℕ) :
    levImg Fr p hk nL rho dPl dNo (P * Q) =
      if InLow Fr p hk nL rho base then
        tens (compD dPl (levP Fr p hk nL P)) (compD dNo (levN Fr p hk nL Q))
      else 0 := by
  have hL : levImg Fr p hk nL rho dPl dNo (P * Q) = ∑ a ∈ P.support, ∑ b ∈ Q.support,
      levImg Fr p hk nL rho dPl dNo (monomial a (P.coeff a) * monomial b (Q.coeff b)) := by
    rw [add_expand (fun X => levImg Fr p hk nL rho dPl dNo (X * Q)) (by simp [levImg_zero])
      (fun x y => by simp only [add_mul, levImg_add]) P]
    refine Finset.sum_congr rfl fun a _ => ?_
    exact add_expand (fun Y => levImg Fr p hk nL rho dPl dNo (monomial a (P.coeff a) * Y)) (by simp [levImg_zero])
      (fun x y => by simp only [mul_add, levImg_add]) Q
  have hR : tens (compD dPl (levP Fr p hk nL P)) (compD dNo (levN Fr p hk nL Q)) = ∑ a ∈ P.support, ∑ b ∈ Q.support,
      tens (compD dPl (levP Fr p hk nL (monomial a (P.coeff a))))
        (compD dNo (levN Fr p hk nL (monomial b (Q.coeff b)))) := by
    rw [add_expand (fun X => tens (compD dPl (levP Fr p hk nL X)) (compD dNo (levN Fr p hk nL Q)))
      (by simp only [monomialSubstitution_zero, compD_zero, tens_zero_left])
      (fun x y => by simp only [monomialSubstitution_add, compD_add, tens_add_left]) P]
    refine Finset.sum_congr rfl fun a _ => ?_
    exact add_expand (fun Y => tens (compD dPl (levP Fr p hk nL (monomial a (P.coeff a))))
      (compD dNo (levN Fr p hk nL Y))) (by simp only [levN_zero, compD_zero, tens_zero_right])
      (fun x y => by simp only [levN_add, compD_add, tens_add_right]) Q
  have hterm : ∀ a ∈ P.support, ∀ b ∈ Q.support,
      levImg Fr p hk nL rho dPl dNo (monomial a (P.coeff a) * monomial b (Q.coeff b)) =
        if InLow Fr p hk nL rho base then
          tens (compD dPl (levP Fr p hk nL (monomial a (P.coeff a))))
            (compD dNo (levN Fr p hk nL (monomial b (Q.coeff b))))
        else 0 := by
    intro a ha b hb
    obtain ⟨d, hd, hd0, rfl⟩ := hP a ha
    exact lev_term Fr p hk nL hp base d b hd hd0 (hQ b hb).1 (hQ b hb).2 hbase rho dPl dNo _ _
  rw [hL]
  split_ifs with h
  · rw [hR]
    refine Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb => ?_
    rw [hterm a ha b hb, if_pos h]
  · refine Finset.sum_eq_zero fun a ha => Finset.sum_eq_zero fun b hb => ?_
    rw [hterm a ha b hb, if_neg h]

end Lev

end Formalism.MainNotions.PairMembershipBlocks.T5
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.PlaneCoefficients.ValuationGeOfLeAddOne
section
noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.PairMembershipBlocks

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords Formalism.MainNotions.G.GLWeightTheory
open Formalism.MainNotions.TestSideWords.TwistedFiltration.G2

section Gen

variable {σ R : Type*} [CommRing R]

theorem X_mul_mono (v : σ) (mo : σ →₀ ℕ) (c : R) : X v * monomial mo c = monomial (mo + Finsupp.single v 1) c := by
  rw [X, monomial_mul, one_mul, add_comm]

theorem pderiv_add_single (w : σ) (L : σ →₀ ℕ) (c : R) :
    pderiv w (monomial (L + Finsupp.single w 1) c) = monomial L (c * ((L w : R) + 1)) := by
  rw [pderiv_monomial, add_tsub_cancel_right, Finsupp.add_apply, Finsupp.single_eq_same]
  push_cast
  rfl

theorem pderiv_mono_zero (w : σ) (L : σ →₀ ℕ) (c : R) (h : L w = 0) : pderiv w (monomial L c) = 0 := by
  rw [pderiv_monomial, h, Nat.cast_zero, mul_zero, map_zero]

theorem exists_add_single (w : σ) (L : σ →₀ ℕ) (h : L w ≠ 0) : ∃ L', L = L' + Finsupp.single w 1 := ⟨L - Finsupp.single w 1,
  (tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr h))).symm⟩

end Gen

section PolS

variable {R : Type} [CommRing R] {ι : Type} {n : ℕ}

theorem multideg_add_single (mo : ι × Fin n →₀ ℕ) (x0 : ι) (a : Fin n) (i : ι) :
    multideg (mo + Finsupp.single (x0, a) 1) i = multideg mo i + if i = x0 then 1 else 0 := by
  unfold multideg
  simp only [Finsupp.add_apply, Finset.sum_add_distrib]
  congr 1
  by_cases h : i = x0
  · subst h
    simp [Finsupp.single_apply]
  · simp [Finsupp.single_apply, h, Ne.symm h]

theorem mem_Pol' {d : ι → ℕ} {F : MvPolynomial (ι × Fin n) R} :
    F ∈ Pol R n d ↔ ∀ m ∈ F.support, ∀ i, multideg m i = d i := by
  unfold Pol
  rw [mem_restrictSupport_iff]
  constructor
  · intro h m hm
    exact h hm
  · intro h m hm
    exact h m hm

theorem mono_mem_Pol {d : ι → ℕ} (m : ι × Fin n →₀ ℕ) (c : R) (h : ∀ i, multideg m i = d i) :
    monomial m c ∈ Pol R n d := by
  rw [mem_Pol']
  intro m' hm'
  have h1 := support_monomial_subset hm'
  rw [Finset.mem_singleton] at h1
  rw [h1]
  exact h

theorem Pol_pderiv {d d' : ι → ℕ} (x0 : ι) (a : Fin n) (h0 : d' x0 = d x0 + 1) (h1 : ∀ i, i ≠ x0 → d' i = d i)
    {H : MvPolynomial (ι × Fin n) R} (hH : H ∈ Pol R n d') : pderiv (x0, a) H ∈ Pol R n d := by
  rw [mem_Pol'] at hH
  set_option synthInstance.maxHeartbeats 100000 in
    rw [H.as_sum, map_sum]
  refine Submodule.sum_mem _ fun m hm => ?_
  by_cases hz : m (x0, a) = 0
  · rw [pderiv_mono_zero _ _ _ hz]
    exact Submodule.zero_mem _
  · obtain ⟨m', rfl⟩ := exists_add_single _ m hz
    rw [pderiv_add_single]
    apply mono_mem_Pol
    intro i
    have hi := hH _ hm i
    rw [multideg_add_single] at hi
    by_cases hix : i = x0
    · subst hix
      simp at hi
      omega
    · simp [hix] at hi
      rw [hi, h1 i hix]

theorem Pol_X_mul {d d' : ι → ℕ} (x0 : ι) (a : Fin n) (h0 : d x0 = d' x0 + 1) (h1 : ∀ i, i ≠ x0 → d' i = d i)
    {H : MvPolynomial (ι × Fin n) R} (hH : H ∈ Pol R n d') : X (x0, a) * H ∈ Pol R n d := by
  rw [mem_Pol'] at hH
  rw [H.as_sum, Finset.mul_sum]
  refine Submodule.sum_mem _ fun m hm => ?_
  rw [X_mul_mono]
  apply mono_mem_Pol
  intro i
  rw [multideg_add_single, hH m hm i]
  by_cases hix : i = x0
  · subst hix
    simp
    omega
  · simp [hix]
    exact h1 i hix

end PolS

theorem valuation_ge_of_le_add_one {x y : WithTop ℤ} {t t' : ℝ} (h : x ≤ y + ((1 : ℤ) : WithTop ℤ)) (hx : geZ x t') (ht : t + 1 ≤ t') :
    geZ y t := by
  intro k hk
  rw [hk] at h
  have h' : x ≤ ((k + 1 : ℤ) : WithTop ℤ) := by
    rw [WithTop.coe_add]
    exact h
  induction x using WithTop.recTopCoe with
  | top => simp at h'
  | coe k'' =>
    have h2 := hx k'' rfl
    have h3 : (k'' : ℝ) ≤ (k : ℝ) + 1 := by exact_mod_cast WithTop.coe_le_coe.mp h'
    linarith

section ValOp

variable {Kf : Type} [Field Kf] {ι : Type} {n : ℕ} [NeZero n] (LL : Letters ι) (S : Set ι)

end ValOp

end Formalism.MainNotions.PairMembershipBlocks
end
end

