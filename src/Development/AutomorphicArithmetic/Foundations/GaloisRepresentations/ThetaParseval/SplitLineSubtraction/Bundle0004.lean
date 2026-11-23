module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.TwoUpOKOf
public import Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitAtOfIsSplitPl
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0225

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.MapUnivAdd
section
namespace UpperTheory.Gal.TP.Sub

open Formalism.BasicNotions

private theorem multiset_map_fin_add_eq_add {n t : ℕ} (f : Fin (n + t) → ℤ) :
    Multiset.map f Finset.univ.val =
      Multiset.map (fun k : Fin n => f (Fin.castAdd t k)) Finset.univ.val +
        Multiset.map (fun i : Fin t => f (Fin.natAdd n i)) Finset.univ.val := by
  rw [Fin.univ_val_map, List.ofFn_add, ← Multiset.coe_add, Fin.univ_val_map, Fin.univ_val_map]
  rfl

private theorem multiset_map_fin_rev_eq {n : ℕ} (f : Fin n → ℤ) :
    Multiset.map f Finset.univ.val = Multiset.map (fun k : Fin n => f k.rev) Finset.univ.val := by
  conv_lhs => rw [← Multiset.map_univ_val_equiv (Fin.revPerm : Equiv.Perm (Fin n)), Multiset.map_map]
  rfl

theorem wtId_holds : WtId := by
  intro n t lam lam' mX mW hL
  refine ⟨fun m p hm hp => ?_, fun m p hm hp => ?_⟩
  · unfold wtJumps
    rw [multiset_map_fin_add_eq_add]
    congr 1
    · rw [Multiset.map_map]
      congr 1
      funext k
      have h1 := hL (Fin.castAdd t k)
      simp only [Fin.coe_castAdd, k.2, dif_pos, Fin.eta] at h1
      simp only [Function.comp_apply, Fin.coe_castAdd]
      omega
    · rw [multiset_map_fin_rev_eq (fun i : Fin t => -p i)]
      congr 1
      funext i
      have h1 := hL (Fin.natAdd n i)
      have h2 := hp i.rev
      simp only [Fin.coe_natAdd, Fin.val_rev] at h1 h2 ⊢
      rw [dite_eq_right (by omega)] at h1
      have hi := i.2
      push_cast at h1
      omega
  · unfold wtJumps
    rw [multiset_map_fin_rev_eq, multiset_map_fin_rev_eq (fun k : Fin n => ((k : ℕ) : ℤ) - lam.dual.w k)]
    simp only [DomWeight.dual, Fin.rev_rev, Fin.val_rev]
    rw [multiset_map_fin_add_eq_add]
    congr 1
    · rw [Multiset.map_map]
      congr 1
      funext k
      have h1 := hL (Fin.castAdd t k)
      simp only [Fin.coe_castAdd, k.2, dif_pos, Fin.eta] at h1
      simp only [Function.comp_apply, Fin.coe_castAdd]
      have hk := k.2
      omega
    · congr 1
      funext i
      have h1 := hL (Fin.natAdd n i)
      have h2 := hp i
      simp only [Fin.coe_natAdd] at h1 h2 ⊢
      rw [dite_eq_right (by omega)] at h1
      have hi := i.2
      have hc : ((n + t - (n + (i : ℕ) + 1) : ℕ) : ℤ) = (t : ℤ) - 1 - (i : ℕ) := by
        rw [Nat.cast_sub (by omega)]
        push_cast
        ring
      push_cast at h1
      rw [hc]
      omega

end UpperTheory.Gal.TP.Sub
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.PBaseNG
section
open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Host Formalism.ConjugateSelfDual Formalism.BasicNotions GlobalTheory.HeckeGal GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open UpperTheory.V.Af (algSat)
open UpperTheory.Gal.TP.Sub

private theorem unram_of_forall {E : Type} [Field E] [NumberField E] [IsCMField E]
    (hE : ∀ w : HeightOneSpectrum (𝓞 E), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal) :
    Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E) := by
  haveI : Algebra.FormallyUnramified (𝓞 (maximalRealSubfield E)) (𝓞 E) := by
    rw [Algebra.formallyUnramified_iff_forall]
    intro q
    obtain ⟨Q, hQ, hqQ⟩ := Ideal.exists_le_maximal q.1 q.2.ne_top
    have hne : Q ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hQ (RingOfIntegers.not_isField E)
    have hU := hE ⟨Q, hQ.isPrime, hne⟩
    have hopen := Algebra.isOpen_unramifiedLocus (R := 𝓞 (maximalRealSubfield E)) (A := 𝓞 E)
    exact hopen.stableUnderGeneralization
      ((PrimeSpectrum.le_iff_specializes q ⟨Q, hQ.isPrime⟩).mp hqQ) hU
  exact ⟨inferInstance, inferInstance⟩

private theorem under_eq_of_inert {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)} (h : Formalism.UG.IsInertAt F E v w) :
    w.under (𝓞 F) = v := by
  apply HeightOneSpectrum.ext
  have hle : v.asIdeal ≤ (w.under (𝓞 F)).asIdeal := by
    show v.asIdeal ≤ w.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E))
    rw [← Ideal.map_le_iff_le_comap]
    exact h.le
  exact (v.isMaximal.eq_of_le (w.under (𝓞 F)).isPrime.ne_top hle).symm

private theorem not_split_of_inert {E : Type} [Field E] [NumberField E] [IsCMField E]
    {v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))} {w : HeightOneSpectrum (𝓞 E)}
    (h : Formalism.UG.IsInertAt (maximalRealSubfield E) E v w) : ¬ GlobalTheory.UnitaryBC.IsSplitAt w := by
  rintro ⟨u, hne, hu⟩
  apply hne
  have hv : u.under (𝓞 (maximalRealSubfield E)) = v := hu.trans (under_eq_of_inert h)
  have hle : w.asIdeal ≤ u.asIdeal := by
    rw [← show Ideal.map (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) v.asIdeal = w.asIdeal from h, Ideal.map_le_iff_le_comap, ← hv]
    exact le_rfl
  exact (HeightOneSpectrum.ext ((w.isMaximal.eq_of_le u.isPrime.ne_top hle))).symm

theorem UpperTheory.Gal.TP.Sub.baseNG_holds :
    UpperTheory.Gal.TP.Skew.SkewLine → BaseNG := by
  intro hS E _ _ _ hE hI
  have hcm : IsCMExt (maximalRealSubfield E) E (UpperTheory.TP.cj E) :=
    ⟨inferInstance, inferInstance, Algebra.IsQuadraticExtension.finrank_eq_two _ _,
      fun τ x => IsCMField.complexEmbedding_complexConj E τ x⟩
  have hu := unram_of_forall hE
  obtain ⟨B, δ, 𝔞, -, -, hP, hstd, -, h1, h2⟩ := hS (maximalRealSubfield E) E (UpperTheory.TP.cj E) hcm hu
  refine ⟨B, δ, 𝔞, ?_, h1, h2⟩
  exact
    { cm := hcm
      unram := hu
      std := hstd
      inert := fun v w h => by
        obtain ⟨a, b, c⟩ := hI w (not_split_of_inert h)
        rw [under_eq_of_inert h] at a b c
        exact ⟨a, b, PositivityTheory.Mix.psiUnr_of_not_le hstd v c⟩
      psiP := fun v hv => absurd hv (by simp [hP]) }
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.PEmbSplit
section
open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Host Formalism.ConjugateSelfDual Formalism.BasicNotions GlobalTheory.HeckeGal GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open UpperTheory.V.Af (algSat)
open UpperTheory.Gal.TP.Sub

theorem UpperTheory.Gal.TP.Sub.embSplit_holds :
    EmbSplit := by
  intro E _ _ _ emb
  have hcj : ∀ (φ : E →+* ℂ), (ComplexEmbedding.conjugate φ).comp
      (algebraMap (maximalRealSubfield E) E) =
      ComplexEmbedding.conjugate (φ.comp (algebraMap (maximalRealSubfield E) E)) := by
    intro φ
    ext x
    simp [ComplexEmbedding.conjugate_coe_eq]
  have hinj : ∀ (w w' : InfinitePlace (maximalRealSubfield E)), w.embedding = w'.embedding → w = w' := by
    intro w w' h
    rw [← InfinitePlace.mk_embedding w, ← InfinitePlace.mk_embedding w', h]
  refine ⟨?_, ?_, ?_⟩
  · intro τ
    let w := InfinitePlace.mk (τ.comp (algebraMap (maximalRealSubfield E) E))
    refine ⟨w, ?_⟩
    have hw : (InfinitePlace.mk τ).comap (algebraMap (maximalRealSubfield E) E) =
        (InfinitePlace.mk (emb w).1).comap (algebraMap (maximalRealSubfield E) E) := by
      rw [InfinitePlace.comap_mk, InfinitePlace.comap_mk, (emb w).2, InfinitePlace.mk_embedding]
    have hmk : InfinitePlace.mk τ = InfinitePlace.mk (emb w).1 :=
      (IsCMField.equivInfinitePlace E).injective hw
    rcases InfinitePlace.mk_eq_iff.1 hmk with h | h
    · exact Or.inl h
    · right
      rw [← h]
      ext x
      simp [ComplexEmbedding.conjugate_coe_eq]
  · intro w w' h
    apply hinj
    rw [← (emb w).2, ← (emb w').2, h]
  · intro w w' h
    have h1 : w.embedding = ComplexEmbedding.conjugate w'.embedding := by
      rw [← (emb w).2, ← (emb w').2, h, hcj]
    have hww : w = w' := by
      rw [← InfinitePlace.mk_embedding w, ← InfinitePlace.mk_embedding w', h1,
        InfinitePlace.mk_conjugate_eq]
    subst hww
    apply IsTotallyComplex.complexEmbedding_not_isReal (emb w).1
    exact h.symm
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.PSatId
section
open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Host Formalism.ConjugateSelfDual Formalism.BasicNotions GlobalTheory.HeckeGal GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open UpperTheory.V.Af (algSat)
open UpperTheory.Gal.TP.Sub

private theorem multiset_bind_pure_coe_eq_map (S : Multiset ℂˣ) :
    (do let a ← S; Pure.pure (a : ℂ) : Multiset ℂ) = Multiset.map (fun a : ℂˣ => (a : ℂ)) S := by
  show Multiset.bind S (fun a => {(a : ℂ)}) = _
  exact Multiset.bind_singleton _ _

private theorem multiset_map_fin_eq_map_range (t : ℕ) (f : ℕ → ℂ) :
    Multiset.map (fun i : Fin t => f i) Finset.univ.val = Multiset.map f (Finset.range t).val := by
  rw [Fin.univ_val_map, List.ofFn_eq_map]
  have h : List.map (fun i : Fin t => f i) (List.finRange t) = List.map f (List.range t) := by
    rw [← List.map_coe_finRange_eq_range, List.map_map]
    rfl
  rw [h, ← Multiset.map_coe]
  rfl

theorem UpperTheory.Gal.TP.Sub.satId_holds :
    SatId := by
  intro E _ _ w n t B x y k c hk hc
  have hq0 : ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ≠ 0 := by
    rw [Nat.cast_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]
    exact w.ne_bot
  have hs : ∀ m : ℕ, (((((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ (((m : ℝ) - 1) / 2) : ℝ)) : ℂ) =
      ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (((m : ℂ) - 1) / 2) := by
    intro m
    rw [Complex.ofReal_cpow (by positivity)]
    push_cast
    rfl
  simp only [algSat, GlobalTheory.LFun.seg, hs]
  rw [multiset_bind_pure_coe_eq_map, multiset_bind_pure_coe_eq_map]
  simp only [Multiset.map_add (f := _), Multiset.map_map]
  have hR := multiset_map_fin_eq_map_range t (fun j : ℕ => (x : ℂ) *
      ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (((n : ℂ) + 2 * t - 2) / 2 - (j : ℂ)))
  have hc' : c = fun i : Fin t => (fun j : ℕ => (x : ℂ) *
      ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (((n : ℂ) + 2 * t - 2) / 2 - (j : ℂ))) (i : ℕ) := funext hc
  rw [hc', hR]
  congr 1
  · apply Multiset.map_congr rfl
    intro b _
    simp only [Function.comp, Units.val_mul, Units.val_inv_eq_inv_val, hk]
    have hsplit : (((n + t : ℕ) : ℂ) - 1) / 2 = ((n : ℂ) - 1) / 2 + (t : ℂ) / 2 := by
      push_cast
      ring
    rw [hsplit, Complex.cpow_add _ _ hq0, Complex.cpow_neg, mul_inv, mul_inv, inv_inv, inv_inv]
    ring
  · apply Multiset.map_congr rfl
    intro j _
    simp only [Function.comp, Units.val_mul, GlobalTheory.LFun.npowU, Units.val_mk0, GlobalTheory.LFun.npow]
    rw [mul_left_comm, ← Complex.cpow_add _ _ hq0]
    congr 2
    push_cast
    ring
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.UpOfHolds
section
open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Host Formalism.ConjugateSelfDual Formalism.BasicNotions GlobalTheory.HeckeGal GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open UpperTheory.V.Af (algSat)
open UpperTheory.Gal.TP.Sub

theorem UpperTheory.Gal.TP.Sub.upOf_holds :
    EmbSplit → WtId → SatId → UpperTheory.Gal.TP.Loc.LiftSatU → UpOf := by
  intro hE hWt hS hLS E _ _ _ n t hn hnt Bs χX χW mX mW U hU lam hl U' hL κ m ψ p hD
  classical
  obtain ⟨hcov, -, hne⟩ := hE E Bs.emb
  choose l' hl'w hl'L using hL.wt
  choose w₀ hw₀ using hcov
  have hn' : 1 ≤ n + t := by omega
  let lam' : (E →+* ℂ) → DomWeight (n + t) := fun τ =>
    if τ = (Bs.emb (w₀ τ)).1 then l' (w₀ τ) else (l' (w₀ τ)).dual
  have key : ∀ τ, (∃ w, τ = (Bs.emb w).1 ∧ lam' τ = l' w) ∨
      ∃ w, τ = ComplexEmbedding.conjugate (Bs.emb w).1 ∧ lam' τ = (l' w).dual := by
    intro τ
    rcases hw₀ τ with h | h
    · exact Or.inl ⟨w₀ τ, h, if_pos h⟩
    · exact Or.inr ⟨w₀ τ, h, if_neg fun h' => hne (w₀ τ) (w₀ τ) (h'.symm.trans h)⟩
  refine ⟨lam', hL.aut, fun τ => ?_, hD.alg, fun τ => ?_, ?_⟩
  · rcases key τ with ⟨w, rfl, h⟩ | ⟨w, rfl, h⟩
    · rw [h]
      exact hl'w w
    · rw [h]
      exact GlobalTheory.DefiniteBC.hasWeightAt_conjugate hn' (hl'w w)
  · rcases key τ with ⟨w, rfl, h⟩ | ⟨w, rfl, h⟩
    · rw [h]
      exact (hWt n t _ _ _ _ (hl'L w)).1 _ (fun i => p i _) (hD.m₁ w) fun i => hD.p₁ i w
    · have hd : lam (ComplexEmbedding.conjugate (Bs.emb w).1) = (lam (Bs.emb w).1).dual :=
        GlobalTheory.DefU.hasWeightAt_unique ⟨U, hU⟩ _ (hl _) (GlobalTheory.DefiniteBC.hasWeightAt_conjugate hn (hl _))
      rw [h, hd]
      exact (hWt n t _ _ _ _ (hl'L w)).2 _ (fun i => p i _) (hD.m₂ w) fun i => hD.p₂ i w
  · intro v hv hκ hψ B hB
    obtain ⟨hX, hW, hk, hc⟩ := hD.loc v hκ hψ
    have h1 := hLS E n (n + t) (by omega) Bs χX χW mX mW _ U U' hU hL v hv hX hW B hB
    rw [Nat.add_sub_cancel_left] at h1
    refine ⟨_, h1, ?_⟩
    have hnorm : normV v = Ideal.absNorm v.asIdeal := by
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
      rfl
    rw [hnorm]
    exact hS E v n t B _ _ _ (fun i => (((ψ i).val v : ℂˣ) : ℂ)) hk hc
end

