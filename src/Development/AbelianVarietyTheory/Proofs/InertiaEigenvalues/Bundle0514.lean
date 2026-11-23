module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0458
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0474
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlockCharactersCrystallineOfRules
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0489
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisPrescribedUnramifiedKummer
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0500
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0482
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0472
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0477
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0495
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0488
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0494
public import Formalism.SharpRestriction.LevelLetterCocycles.LiftingTheory
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0485
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Formalism.SharpRestriction.LevelLetterCocycles.RamificationTwoAndConjugationAtQAndD
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0454
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0490
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsAdicCompleteDividedTwoVariableSubring
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter
open scoped Formalism.Per

namespace GlobalTheory.CrysPrism.CompPP

theorem mem_span_pow_smul_top {R : Type} [CommRing R] (c x : R) (k : ℕ) :
    x ∈ (Ideal.span {c} ^ k • ⊤ : Submodule R R) ↔ c ^ k ∣ x := by
  change x ∈ Ideal.span {c} ^ k • (⊤ : Ideal R) ↔ _
  rw [Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]

variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a] {O : Type} [CommRing O] [Algebra ℤ_[l] O]
  [Module.Free ℤ_[l] O] {K : Type} [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]

theorem natCast_l_ne_zero : (l : Wq l a) ≠ 0 := WittVector.p_nonzero l (Fq l a)


variable (K) in
theorem emb_injective (t : Wq l a →ₐ[ℤ_[l]] O) (τ : ZMod a) :
    Function.Injective fun x : Wq l a => algebraMap O K (emb t τ x) := by
  haveI : Nontrivial O :=
    ⟨⟨0, 1, fun h => one_ne_zero (by simpa using congrArg (algebraMap O K) h.symm : (1 : K) = 0)⟩⟩
  have ht : Function.Injective t := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra h0
    obtain ⟨m, b, rfl⟩ := WittVector.exists_eq_pow_p_mul' x h0
    have hu : IsUnit (t (b : Wq l a)) := b.isUnit.map t
    rw [map_mul, map_pow, map_natCast] at hx
    have hlm : (l : O) ^ m = 0 := (hu.mul_left_eq_zero).1 hx
    have h2 : ((l : ℤ_[l]) ^ m) • (1 : O) = 0 := by
      rw [Algebra.smul_def, mul_one, map_pow, map_natCast]; exact hlm
    rcases smul_eq_zero.1 h2 with h3 | h3
    · exact pow_ne_zero m (Nat.cast_ne_zero.2 hl.out.ne_zero) h3
    · exact one_ne_zero h3
  exact IsUnitBall.inj.comp (ht.comp (sigmaNeg l a τ).injective)

variable (t : Wq l a →ₐ[ℤ_[l]] O) (e : ℕ)

def Wit (F : ZMod a → K⟦X⟧⟦X⟧) (w : ℕ × ℕ → Wq l a) : Prop :=
  ∀ τ i n, ((i.factorial * (n / e).factorial : ℕ) : K) * coeff n (coeff i (F τ)) =
      algebraMap O K (emb t τ (w (i, n)))

omit [Module.Free ℤ_[l] O] in
theorem Wit.sub {F G : ZMod a → K⟦X⟧⟦X⟧} {w v : ℕ × ℕ → Wq l a} (hF : Wit t e F w) (hG : Wit t e G v) :
    Wit t e (F - G) (w - v) := by
  intro τ i n
  simp only [Pi.sub_apply, map_sub, mul_sub, hF τ i n, hG τ i n]

omit [Module.Free ℤ_[l] O] in
theorem Wit.zero : Wit t e (0 : ZMod a → K⟦X⟧⟦X⟧) 0 := by
  intro τ i n
  simp

omit [Module.Free ℤ_[l] O] in
theorem Wit.lpow {G : ZMod a → K⟦X⟧⟦X⟧} {v : ℕ × ℕ → Wq l a} (hG : Wit t e G v) (k : ℕ) :
    Wit t e ((l : ZMod a → K⟦X⟧⟦X⟧) ^ k * G) (fun p => (l : Wq l a) ^ k * v p) := by
  intro τ i n
  have h1 : ((l : ZMod a → K⟦X⟧⟦X⟧) ^ k * G) τ = C (C ((l : K) ^ k)) * G τ := by
    simp only [Pi.mul_apply, Pi.pow_apply, Pi.natCast_apply, map_pow, map_natCast]
  rw [h1, coeff_C_mul, coeff_C_mul, map_mul, map_mul, map_pow, map_pow, map_natCast, map_natCast,
    ← hG τ i n]
  ring

theorem Wit.unique {F : ZMod a → K⟦X⟧⟦X⟧} {w v : ℕ × ℕ → Wq l a} (hw : Wit t e F w) (hv : Wit t e F v) :
    w = v :=
  funext fun p => emb_injective K t 0 ((hw 0 p.1 p.2).symm.trans (hv 0 p.1 p.2))

omit [Module.Free ℤ_[l] O] in
theorem Wit.eq [CharZero K] {F G : ZMod a → K⟦X⟧⟦X⟧} {w : ℕ × ℕ → Wq l a} (hF : Wit t e F w)
    (hG : Wit t e G w) : F = G :=
  funext fun τ => PowerSeries.ext fun i => PowerSeries.ext fun n =>
    mul_left_cancel₀ (Nat.cast_ne_zero.2 (by positivity)) ((hF τ i n).trans (hG τ i n).symm)


variable (K) in
def mkF (v : ℕ × ℕ → Wq l a) : ZMod a → K⟦X⟧⟦X⟧ := fun τ =>
  PowerSeries.mk fun i => PowerSeries.mk fun n =>
    algebraMap O K (emb t τ (v (i, n))) / ((i.factorial * (n / e).factorial : ℕ) : K)

omit [Module.Free ℤ_[l] O] in
theorem wit_mk [CharZero K] (v : ℕ × ℕ → Wq l a) : Wit t e (mkF K t e v) v := by
  intro τ i n
  simp only [mkF, coeff_mk]
  exact mul_div_cancel₀ _ (Nat.cast_ne_zero.2 (by positivity))

end GlobalTheory.CrysPrism.CompPP

namespace GlobalTheory.CrysPrism.CompPP

variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a] {O : Type} [CommRing O] [Algebra ℤ_[l] O]
  [Module.Free ℤ_[l] O] {K : Type} [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
  (t : Wq l a →ₐ[ℤ_[l]] O) (e : ℕ)


omit [Module.Free ℤ_[l] O] in
theorem tendsToZeroLAdically_of_eq_prime_pow_mul {u v : ℕ × ℕ → Wq l a} (k : ℕ) (h : ∀ p, u p = (l : Wq l a) ^ k * v p)
    (hu : LTo0 l u) : LTo0 l v := by
  intro r
  filter_upwards [hu (k + r)] with p hp
  rw [h p, pow_add] at hp
  exact (mul_dvd_mul_iff_left (pow_ne_zero k natCast_l_ne_zero)).1 hp

theorem dvd_iff [CharZero K] (hcl : ∀ F ∈ PPd t K e, F ∈ PPSet t K e) (F : ↥(PPd t K e)) (k : ℕ)
    {w : ℕ × ℕ → Wq l a} (hw : Wit t e F.1 w) :
    (l : ↥(PPd t K e)) ^ k ∣ F ↔ ∀ p, (l : Wq l a) ^ k ∣ w p := by
  constructor
  · rintro ⟨G, rfl⟩
    obtain ⟨v, -, hv⟩ := hcl G.1 G.2
    have h1 : Wit t e ((l : ↥(PPd t K e)) ^ k * G).1 (fun p => (l : Wq l a) ^ k * v p) := by
      have := Wit.lpow t e hv k
      simpa using this
    rw [Wit.unique t e hw h1]
    exact fun p => dvd_mul_right _ _
  · intro h
    choose v hv using h
    obtain ⟨w', hw0', hw'⟩ := hcl F.1 F.2
    rw [← Wit.unique t e hw hw'] at hw0'
    have hv0 : LTo0 l v := tendsToZeroLAdically_of_eq_prime_pow_mul k hv hw0'
    refine ⟨⟨mkF K t e v, Subring.subset_closure ⟨v, hv0, wit_mk t e v⟩⟩, Subtype.ext ?_⟩
    have h1 := Wit.lpow t e (wit_mk (K := K) t e v) k
    have h2 : (fun p => (l : Wq l a) ^ k * v p) = w := funext fun p => (hv p).symm
    rw [h2] at h1
    simpa using Wit.eq t e hw h1

theorem complete_of [CharZero K] (hcl : ∀ F ∈ PPd t K e, F ∈ PPSet t K e) :
    IsAdicComplete (Ideal.span {(l : ↥(PPd t K e))}) ↥(PPd t K e) := by
  have hWq : ∀ (x y : Wq l a) (n : ℕ), (x ≡ y [SMOD (Ideal.span {(l : Wq l a)} ^ n • ⊤ : Submodule (Wq l a) (Wq l a))] ↔
      (l : Wq l a) ^ n ∣ x - y) := fun x y n => by
    rw [SModEq.sub_mem, mem_span_pow_smul_top]
  have hPP : ∀ (x y : ↥(PPd t K e)) (n : ℕ), (x ≡ y [SMOD (Ideal.span {(l : ↥(PPd t K e))} ^ n • ⊤ :
      Submodule ↥(PPd t K e) ↥(PPd t K e))] ↔ (l : ↥(PPd t K e)) ^ n ∣ x - y) := fun x y n => by
    rw [SModEq.sub_mem, mem_span_pow_smul_top]
  refine { haus' := fun F hF => ?_, prec' := fun f hf => ?_ }
  · obtain ⟨w, -, hw⟩ := hcl F.1 F.2
    have h0 : w = 0 := funext fun p => IsHausdorff.haus' (I := Ideal.span {(l : Wq l a)}) (w p) fun n =>
      (hWq _ _ n).2 (by
        rw [sub_zero]
        exact (dvd_iff t e hcl F n hw).1 (by simpa using (hPP F 0 n).1 (hF n)) p)
    rw [h0] at hw
    exact Subtype.ext (Wit.eq t e hw (Wit.zero t e))
  · choose W hW0 hW using fun m => hcl (f m).1 (f m).2
    have hd : ∀ {m n : ℕ}, m ≤ n → ∀ p, (l : Wq l a) ^ m ∣ W m p - W n p := fun {m n} hmn p =>
      (dvd_iff t e hcl (f m - f n) m (Wit.sub t e (hW m) (hW n))).1 ((hPP _ _ m).1 (hf hmn)) p
    choose w hw using fun p => IsPrecomplete.prec' (I := Ideal.span {(l : Wq l a)}) (fun m => W m p)
      fun {m n} hmn => (hWq _ _ m).2 (hd hmn p)
    have hw' : ∀ p n, (l : Wq l a) ^ n ∣ W n p - w p := fun p n => (hWq _ _ n).1 (hw p n)
    have hw0 : LTo0 l w := by
      intro r
      filter_upwards [hW0 r r] with p hp
      simpa using dvd_sub hp (hw' p r)
    refine ⟨⟨mkF K t e w, Subring.subset_closure ⟨w, hw0, wit_mk t e w⟩⟩, fun n => (hPP _ _ n).2 ?_⟩
    exact (dvd_iff t e hcl _ n (Wit.sub t e (hW n) (wit_mk t e w))).2 fun p => hw' p n

end GlobalTheory.CrysPrism.CompPP

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism

theorem GlobalTheory.CrysPrism.PPd_isAdicComplete : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), IsAdicComplete (Ideal.span {(l : ↥(PPd t K e))}) ↥(PPd t K e) := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ t
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[l] K).injective
  exact GlobalTheory.CrysPrism.CompPP.complete_of t e (_root_.GlobalTheory.CrysPrism.PPd_subset_PPSet l a e O K t)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsConstituentOfIsBlockSum
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.PtCore

namespace GlobalTheory.ChiOneEnl

open GlobalTheory.IndefiniteRowSideFullHecke

theorem isConstituent_of_isBlockSum (D : D7) (i : D.nd.Loc)
    (r : D.nd.X i → (Formalism.MainNotions.N.GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (Formalism.MainNotions.N.GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
    (h : BlockJumpCount.IsBlockSum D.nd i r ρ π) :
    BlockCharactersCrystallineNonGaloisCusps.IsConstituent D i (chiU D.nd i 1) (rO D.nd i r π) := by
  obtain ⟨e, he⟩ := h
  let c : Fin D.R.t := ⟨0, D.R.t_odd.pos⟩
  refine ⟨e.symm (0, Pi.single c 1), ?_, fun g => ?_⟩
  · intro h0
    have h1 := congrArg (fun u => (e u).2 c) h0
    simp at h1
  · apply e.injective
    have h2 := he g (e.symm (0, Pi.single c 1))
    rw [map_smul, e.apply_symm_apply]
    rw [e.apply_symm_apply] at h2
    refine h2.trans ?_
    refine Prod.ext ?_ ?_
    · simp
    · funext a
      by_cases ha : a = c
      · subst ha
        simp [c, Algebra.smul_def]
      · simp [ha]

theorem isCrys_chiE_of_constituent (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∈ placesOver D.host.E (D.nd.l i)) (L' : FinExt (D.nd.l i)) (hL : (D.nbr i w hw).LL.1 ≤ L'.1)
    (hS : CrystallineSubrepresentation.SubCrys (Br.PD D.loc D.nbr i w hw) ↥L'.1) {n : ℕ}
    (χ : Formalism.MainNotions.N.GE D.nd →* (D.nd.O i)ˣ) (M : Formalism.MainNotions.N.GE D.nd →* Matrix (Fin n) (Fin n) (D.nd.O i))
    (h : BlockCharactersCrystallineNonGaloisCusps.IsConstituent D i χ M)
    (hc : IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (locE D i w hw L' hL M))) :
    IsCrys (Br.PD D.loc D.nbr i w hw) (Formalism.WeaklyAdmissibleFiltrations.charRep (chiE D i w hw L' hL χ)) := by
  obtain ⟨v, hv, hg⟩ := h
  let f := (inc D i w hw L' hL).comp (Br.toLLK (D.nbr i w hw))
  let v' : Fin n → ↥L'.1 := fun a => f (v a)
  have hv' : v' ≠ 0 := by
    intro h0
    apply hv
    funext a
    exact f.injective ((congrFun h0 a).trans (map_zero _).symm)
  have hf : ∀ x, f (toK D.nd i x) = inc D i w hw L' hL ((D.nbr i w hw).toLL x) := fun x =>
    congrArg (inc D i w hw L' hL) (WordJumpsCompare.toLLK_toK _ _ _ _ _)
  have key : ∀ g : Br.G D.nbr i w hw, (locE D i w hw L' hL M g).mulVec v' =
      ((chiE D i w hw L' hL χ g : (↥L'.1)ˣ) : ↥L'.1) • v' := by
    intro g
    funext a
    have h1 := congrArg f (congrFun (hg (decS D.nd w (Br.iota D.nbr i w hw g))) a)
    have h2 : (mapM (toK D.nd i) M (decS D.nd w (Br.iota D.nbr i w hw g))).mulVec v a =
        ∑ b, toK D.nd i (M (decS D.nd w (Br.iota D.nbr i w hw g)) a b) * v b := rfl
    set_option synthInstance.maxHeartbeats 100000 in
      rw [h2, map_sum, Pi.smul_apply, smul_eq_mul, map_mul, hf] at h1
    simp only [map_mul, hf] at h1
    rw [Pi.smul_apply, smul_eq_mul]
    exact h1
  refine hS _ (matRep (locE D i w hw L' hL M)) _ _ (LinearMap.toSpanSingleton _ _ v') (fun g c => ?_)
    (LinearMap.ker_eq_bot.mp (LinearMap.ker_toSpanSingleton _ hv')) hc
  change (((chiE D i w hw L' hL χ g : (↥L'.1)ˣ) : ↥L'.1) • c) • v' =
    (locE D i w hw L' hL M g).mulVec (c • v')
  rw [Matrix.mulVec_smul, key, smul_smul, smul_eq_mul, mul_comm]

theorem chiOneE_of_isBlockSum (hF : GlobalTheory.Published.FontaineBcris) (D : D7) (i : D.nd.Loc)
    (r : D.nd.X i → (Formalism.MainNotions.N.GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (Formalism.MainNotions.N.GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
    (hs : GlobalTheory.IndefiniteRowSideFullHecke.BlockJumpCount.IsBlockSum D.nd i r ρ π)
    (hc : ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)),
      IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (Br.loc D.nbr i w hw (rO D.nd i r π)))) :
    ChiOneE D i := by
  intro w hw L' hL
  have hR := GlobalTheory.BlockCrys.subDualRules_of_fontaine hF (D.nd.l i) (D.loc _) (D.locA _) ⟨D.locT _⟩
  have hE : IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (locE D i w hw L' hL (rO D.nd i r π))) :=
    GlobalTheory.CrysCoef.isCrys_inclusion (D.nd.l i) (D.loc _) (D.nbr i w hw).Kw (D.nbr i w hw).LL L' hL _ _ (hc w hw)
  exact GlobalTheory.BlockCrys.isCrys_inv _ (hR.1 _ _) (hR.2 _ _) _
    (isCrys_chiE_of_constituent D i w hw L' hL (hR.1 _ _) _ _
      (isConstituent_of_isBlockSum D i r ρ π hs) hE)

end GlobalTheory.ChiOneEnl

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitOfFrobeniusDvdEisensteinPowMul
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

noncomputable section
namespace GlobalTheory.LemZ

theorem weier : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (g : (Wq l a)⟦X⟧), ¬ (l : (Wq l a)⟦X⟧) ∣ g →
    ∃ (P : Polynomial (Wq l a)) (U : (Wq l a)⟦X⟧), IsUnit U ∧ P.Monic ∧
      (∀ i < P.natDegree, (l : Wq l a) ∣ P.coeff i) ∧ g = U * (P : (Wq l a)⟦X⟧) := _root_.GlobalTheory.weierstrass_prep_not_dvd_l

theorem descend : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (P Q : Polynomial (Wq l a)), P.Monic →
    (∀ i < P.natDegree, (l : Wq l a) ∣ P.coeff i) → frobS l a (P : (Wq l a)⟦X⟧) ∣ (Q : (Wq l a)⟦X⟧) →
    Polynomial.expand (Wq l a) l (P.map (sigma l a : Wq l a →+* Wq l a)) ∣ Q := _root_.GlobalTheory.expand_map_dvd_of_frobS_dvd

theorem coeffZero : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (P E : Polynomial (Wq l a)) (M : ℕ), P.Monic → E.coeff 0 ≠ 0 →
    Polynomial.expand (Wq l a) l (P.map (sigma l a : Wq l a →+* Wq l a)) ∣ E ^ M * P → P.coeff 0 ≠ 0 := _root_.GlobalTheory.coeff_zero_ne_zero_of_frobenius_dvd_pow_mul

theorem frobAut : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a], ∃ Φ : Om l ≃ₐ[ℚ_[l]] Om l,
    ∀ w : Wq l a, Φ (GlobalTheory.TameFrob.iotaO l a w) = GlobalTheory.TameFrob.iotaO l a (sigma l a w) := _root_.GlobalTheory.TameFrob.exists_algEquiv_iotaO_sigma

theorem rootLt : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (P : Polynomial (Wq l a)), P.Monic →
    (∀ i < P.natDegree, (l : Wq l a) ∣ P.coeff i) → ∀ x : Om l, (P.map (GlobalTheory.TameFrob.iotaO l a)).IsRoot x → ‖x‖ < 1 := _root_.GlobalTheory.RootLt.norm_lt_one_of_isRoot

theorem irr : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (E : Polynomial (Wq l a)), E.Monic → 0 < E.natDegree →
    (∀ i < E.natDegree, (l : Wq l a) ∣ E.coeff i) → (∃ w : (Wq l a)ˣ, E.coeff 0 = (l : Wq l a) * w) →
    Irreducible (E.map (GlobalTheory.TameFrob.iota l a)) := _root_.GlobalTheory.TameFrob.irreducible_map_iota_of_eisenstein

theorem conj : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (z z' : Om l),
    Polynomial.aeval z' (minpoly (↥(Kunr l a)) z) = 0 → ‖z'‖ = ‖z‖ := _root_.GlobalTheory.conj_norm_eq_of_minpoly_root

theorem expandCoeff : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (E : Polynomial (Wq l a)), E.Monic →
    Irreducible (E.map (GlobalTheory.TameFrob.iota l a)) → ∀ z : Om l, z ≠ 0 →
    (∀ z' : Om l, Polynomial.aeval z' (minpoly (↥(Kunr l a)) z) = 0 → ∀ y : Om l, y ^ l = z' →
      (E.map (GlobalTheory.TameFrob.iotaO l a)).IsRoot y) →
    ∀ i, ¬ l ∣ i → E.coeff i = 0 := _root_.GlobalTheory.ExpandCoeff.coeff_eq_zero_of_roots

theorem isUnit_of_frob_dvd : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), ∀ g : bk.S, ¬ (l : bk.S) ∣ g →
    ∀ M : ℕ, frobS l bk.a g ∣ bk.E ^ M * g → IsUnit g := by
  intro l _ K bk g hg M hdvd
  classical
  obtain ⟨P, U, hU, hPm, hPd, rfl⟩ := weier l bk.a g hg
  have h1 : frobS l bk.a (P : (Wq l bk.a)⟦X⟧) ∣ ((bk.Ep ^ M * P : Polynomial (Wq l bk.a)) : (Wq l bk.a)⟦X⟧) := by
    rw [map_mul] at hdvd
    have h3 : frobS l bk.a (P : (Wq l bk.a)⟦X⟧) ∣ bk.E ^ M * (P : (Wq l bk.a)⟦X⟧) * U := by
      have := (dvd_mul_left _ _).trans hdvd
      rw [show bk.E ^ M * (U * (P : (Wq l bk.a)⟦X⟧)) = bk.E ^ M * (P : (Wq l bk.a)⟦X⟧) * U by ring] at this
      exact this
    rw [Polynomial.coe_mul, Polynomial.coe_pow]
    exact hU.dvd_mul_right.1 h3
  have h2 := descend l bk.a P _ hPm hPd h1
  by_cases hd : P.natDegree = 0
  · rw [Polynomial.eq_one_of_monic_natDegree_zero hPm hd, Polynomial.coe_one, mul_one]
    exact hU
  exfalso
  have hl0 : (l : Wq l bk.a) ≠ 0 := fun h => by
    have := congrArg (GlobalTheory.TameFrob.iotaO l bk.a) h
    rw [map_natCast, map_zero] at this
    exact (Fact.out : l.Prime).ne_zero (by exact_mod_cast this)
  have hE0 : bk.Ep.coeff 0 ≠ 0 := by
    obtain ⟨w, hw⟩ := bk.coeff_zero
    rw [hw]
    exact mul_ne_zero hl0 w.ne_zero
  have hP0 := coeffZero l bk.a P bk.Ep M hPm hE0 h2
  set ι := GlobalTheory.TameFrob.iotaO l bk.a with hι
  have hιinj : Function.Injective ι := GlobalTheory.TameFrob.iotaO_injective l bk.a
  set Pι := P.map ι with hPι
  have hPι0 : Pι ≠ 0 := (hPm.map ι).ne_zero
  have hdeg : Pι.degree ≠ 0 := by
    rw [hPι, Polynomial.degree_map_eq_of_injective hιinj, Polynomial.degree_eq_natDegree hPm.ne_zero]
    exact_mod_cast hd
  obtain ⟨x0, hx0⟩ := IsAlgClosed.exists_root Pι hdeg
  have hne : Pι.roots.toFinset.Nonempty := ⟨x0, Multiset.mem_toFinset.2 ((Polynomial.mem_roots hPι0).2 hx0)⟩
  obtain ⟨x, hxs, hxmax⟩ := Finset.exists_max_image _ (fun y : Om l => ‖y‖) hne
  have hx : Pι.IsRoot x := (Polynomial.mem_roots hPι0).1 (Multiset.mem_toFinset.1 hxs)
  have hmax : ∀ y : Om l, Pι.IsRoot y → ‖y‖ ≤ ‖x‖ := fun y hy =>
    hxmax y (Multiset.mem_toFinset.2 ((Polynomial.mem_roots hPι0).2 hy))
  set r := ‖x‖ with hr
  have hr1 : r < 1 := rootLt l bk.a P hPm hPd x hx
  have hxne : x ≠ 0 := by
    rintro rfl
    apply hP0
    apply hιinj
    simpa [hPι, Polynomial.IsRoot, Polynomial.eval_zero_map, ← Polynomial.coeff_zero_eq_eval_zero] using hx
  have hr0 : 0 < r := norm_pos_iff.2 hxne
  obtain ⟨Φ, hΦ⟩ := frobAut l bk.a
  have hn : ∀ y, ‖Φ y‖ = ‖y‖ := fun y => (spectralNorm_eq_of_equiv Φ y).symm
  set z := Φ x with hzdef
  have hz : ‖z‖ = r := hn x
  have hz0 : z ≠ 0 := fun h => by rw [h, norm_zero] at hz; exact hr0.ne hz
  set Q := P.map (sigma l bk.a : Wq l bk.a →+* Wq l bk.a) with hQ
  have hQι : Q.map ι = Pι.map (Φ : Om l →+* Om l) := by
    rw [hQ, hPι, Polynomial.map_map, Polynomial.map_map]
    congr 1
    ext w
    exact (hΦ w).symm
  have hzQ : (Q.map ι).IsRoot z := by
    rw [hQι]
    exact hx.map (Φ : Om l →+* Om l)
  have hcomp : (algebraMap (↥(Kunr l bk.a)) (Om l)).comp (GlobalTheory.TameFrob.iota l bk.a) = ι := RingHom.ext fun w => rfl
  have haev : ∀ y : Om l, Polynomial.aeval y (Q.map (GlobalTheory.TameFrob.iota l bk.a)) = (Q.map ι).eval y := fun y => by
    rw [Polynomial.aeval_def, Polynomial.eval₂_map, hcomp, Polynomial.eval_map]
  have hmdvd : minpoly (↥(Kunr l bk.a)) z ∣ Q.map (GlobalTheory.TameFrob.iota l bk.a) := by
    apply minpoly.dvd
    rw [haev]
    exact hzQ
  have key : ∀ z' : Om l, Polynomial.aeval z' (minpoly (↥(Kunr l bk.a)) z) = 0 → ∀ y : Om l, y ^ l = z' →
      (bk.Ep.map ι).IsRoot y := by
    intro z' hz' y hy
    have hnz' : ‖z'‖ = r := (conj l bk.a z z' hz').trans hz
    have hz'Q : (Q.map ι).IsRoot z' := by
      obtain ⟨c, hc⟩ := hmdvd
      rw [Polynomial.IsRoot, ← haev, hc, map_mul, hz', zero_mul]
    have hyE : ((bk.Ep ^ M * P).map ι).IsRoot y := by
      have h4 : ((Polynomial.expand (Wq l bk.a) l Q).map ι).IsRoot y := by
        rw [Polynomial.IsRoot, Polynomial.map_expand, Polynomial.expand_eval, hy]
        exact hz'Q
      obtain ⟨c, hc⟩ := h2
      rw [Polynomial.IsRoot, hc, Polynomial.map_mul, Polynomial.eval_mul, h4.eq_zero, zero_mul]
    have hyr : r < ‖y‖ := by
      by_contra hle
      push_neg at hle
      have h5 : ‖y‖ ^ l = r := by rw [← norm_pow, hy, hnz']
      have h6 : r ^ l < r := pow_lt_self_of_lt_one₀ hr0 hr1 (Fact.out : l.Prime).one_lt
      have h7 : ‖y‖ ^ l ≤ r ^ l := pow_le_pow_left₀ (norm_nonneg _) hle l
      linarith
    have hyP : ¬ Pι.IsRoot y := fun h => absurd (hmax y h) (not_le.2 hyr)
    rw [Polynomial.IsRoot, Polynomial.map_mul, Polynomial.map_pow, Polynomial.eval_mul, Polynomial.eval_pow] at hyE
    have h8 := (mul_eq_zero.1 hyE).resolve_right hyP
    rcases Nat.eq_zero_or_pos M with hM | hM
    · rw [hM, pow_zero] at h8; exact absurd h8 one_ne_zero
    · exact (pow_eq_zero_iff hM.ne').1 h8
  have hirr := irr l bk.a bk.Ep bk.monic bk.deg_pos bk.dvd_coeff bk.coeff_zero
  have hc := expandCoeff l bk.a bk.Ep bk.monic hirr z hz0 key
  obtain ⟨i, hi, hci⟩ := bk.not_expand
  exact hci (hc i hi)

end GlobalTheory.LemZ
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JumpsExactAdm
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

namespace GlobalTheory

theorem jumps_exact_adm : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW),
    Formalism.MainNotions.CrystallineLiftingBounds.adm23 D HW F ∧ Formalism.MainNotions.LiftingTheory.adm23 D HW F := by
  intro D HW F
  exact ⟨fun l _ K LL => GlobalTheory.T.isJumpV_iff_of_exact_crystalline_lattices l (D.loc l) (D.locA l) (D.locT l) K LL,
    fun l _ K LL => GlobalTheory.T.isJumpV_iff_of_exact_crystalline_lattices l (D.loc l) (D.locA l) (D.locT l) K LL⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeDivisibleCoboundariesLeLocConstCocyclesAlStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_divisible_coboundaries_le_locConst_cocycles' : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ), BD LA ≤ divisibleCocycles LA := by
  first | exact @GlobalTheory.BDLocConst.lattice_divisible_coboundaries_le_locConst_cocycles | exact GlobalTheory.BDLocConst.lattice_divisible_coboundaries_le_locConst_cocycles | (intros; apply GlobalTheory.BDLocConst.lattice_divisible_coboundaries_le_locConst_cocycles <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeQuotientToDivisibleQuotientMemCocyclesStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeQuotientToDivisibleQuotient_mem_cocycles : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (ϖ : O) (r : ℕ) (hI : StableSub LA (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T)) (c : ↥(GK K) → ↥LA.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T)), c ∈ quotientCocycles LA _ hI → (fun g => GlobalTheory.BKFinLevel.ioL LA ϖ r (c g)) ∈ divisibleCocycles LA := by
  first | exact @GlobalTheory.BKFinLevelCocycle.ioL_mem_Z1D | exact GlobalTheory.BKFinLevelCocycle.ioL_mem_Z1D | (intros; apply GlobalTheory.BKFinLevelCocycle.ioL_mem_Z1D <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrismaticFCrystalFrobeniusPullbackBasisStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prismaticFCrystal_frobenius_pullback_basis : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (M : FCrys l ↥(OL K)) (e : Module.Basis (Fin d) bk.prism.A (M.M bk.prism)) (a : ℕ) (A : Matrix (Fin d) (Fin d) bk.S), (∀ j : Fin d, IsFrac (bk.toP bk.E) (M.Φ bk.prism ⟨bk.toP bk.E, Ideal.mem_span_singleton_self _⟩ (e j)) (∑ i, bk.toP (A i j) • e i) a) → ∀ (Q : Obj l ↥(OL K)) (g : Hom bk.prism Q) (t : ↥Q.I) (y : Fin d → Q.A) (m : M.M Q) (k : ℕ), IsFrac (t : Q.A) (M.Φ Q t (∑ j, y j • M.tr g (e j))) m k → ∃ r : ℕ, (t : Q.A) ^ r • (BK.hf g bk.E ^ a • m - (t : Q.A) ^ k • ∑ i, (A.map (BK.hf g)).mulVec (fun j => Q.D.φ (y j)) i • M.tr g (e i)) = 0 := by
  first | exact @GlobalTheory.BSP.frob_tr_basis | exact GlobalTheory.BSP.frob_tr_basis | (intros; apply GlobalTheory.BSP.frob_tr_basis <;> assumption)
end

