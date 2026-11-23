module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0166
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0877
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.LevelChange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2842
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelEqKN
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0908

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.IntegralMultipleCoprime
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

private def unitBall (p : ℕ) [Fact p.Prime] : Subring (PadicAlgCl p) where
  carrier := {y | ‖y‖ ≤ 1}
  mul_mem' := fun {a b} ha hb => by
    simp only [Set.mem_setOf_eq] at *
    rw [norm_mul]
    exact mul_le_one₀ ha (norm_nonneg _) hb
  one_mem' := by simp
  add_mem' := fun {a b} ha hb => (PadicAlgCl.isNonarchimedean p a b).trans (max_le ha hb)
  zero_mem' := by simp
  neg_mem' := by simp

private theorem den_of_norm {p : ℕ} [hp : Fact p.Prime] (q : ℚ) (h : ‖(q : ℚ_[p])‖ ≤ 1) :
    ¬ p ∣ q.den := by
  intro hd
  have hnum : ¬ (p : ℤ) ∣ q.num := by
    intro hn
    have h1 : p ∣ q.num.natAbs := Int.natCast_dvd.mp hn
    have h2 := Nat.dvd_gcd h1 hd
    rw [Nat.Coprime.gcd_eq_one q.reduced] at h2
    exact hp.out.one_lt.ne' (Nat.dvd_one.mp h2)
  have hn1 : ‖(q.num : ℚ_[p])‖ = 1 :=
    le_antisymm (Padic.norm_int_le_one _)
      (not_lt.mp fun hlt => hnum (Padic.norm_intCast_lt_one_iff.mp hlt))
  have hd1 : ‖(q.den : ℚ_[p])‖ < 1 := Padic.norm_natCast_lt_one_iff.mpr hd
  have heq : (q : ℚ_[p]) * q.den = q.num := by exact_mod_cast Rat.mul_den_eq_num q
  have hn := congrArg norm heq
  rw [norm_mul, hn1] at hn
  nlinarith [norm_nonneg (q.den : ℚ_[p]), norm_nonneg (q : ℚ_[p])]

private theorem coeff_den {p : ℕ} [Fact p.Prime] {F : Type} [Field F] [NumberField F] (x : F)
    (h : ∀ τ : F →+* PadicAlgCl p, ‖τ x‖ ≤ 1) (i : ℕ) : ¬ p ∣ ((minpoly ℚ x).coeff i).den := by
  have hx : IsIntegral ℚ x := Algebra.IsIntegral.isIntegral x
  set P := (minpoly ℚ x).map (algebraMap ℚ (PadicAlgCl p)) with hP
  have hPm : P.Monic := (minpoly.monic hx).map _
  have hroot : ∀ r ∈ P.roots, ‖r‖ ≤ 1 := by
    intro r hr
    have hr' : r ∈ (minpoly ℚ x).rootSet (PadicAlgCl p) := by
      rw [Polynomial.mem_rootSet]
      refine ⟨minpoly.ne_zero hx, ?_⟩
      rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
      exact (Polynomial.mem_roots hPm.ne_zero).mp hr
    rw [← Algebra.IsAlgebraic.range_eval_eq_rootSet_minpoly] at hr'
    obtain ⟨ψ, rfl⟩ := hr'
    exact h ψ.toRingHom
  have hprod : (P.roots.map fun a => Polynomial.X - Polynomial.C a).prod = P :=
    Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hPm IsAlgClosed.card_roots_eq_natDegree
  have hlift : P ∈ Polynomial.lifts (unitBall p).subtype := by
    rw [← hprod]
    refine Subsemiring.multiset_prod_mem _ _ ?_
    intro f hf
    obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.mp hf
    exact ⟨Polynomial.X - Polynomial.C ⟨a, hroot a ha⟩, by simp⟩
  obtain ⟨y, hy⟩ := (Polynomial.lifts_iff_coeff_lifts P).mp hlift i
  have hn : ‖P.coeff i‖ ≤ 1 := by
    rw [← hy]
    exact y.2
  rw [hP, Polynomial.coeff_map] at hn
  apply den_of_norm
  have hc : algebraMap ℚ (PadicAlgCl p) ((minpoly ℚ x).coeff i)
      = algebraMap ℚ_[p] (PadicAlgCl p) (((minpoly ℚ x).coeff i : ℚ) : ℚ_[p]) := by
    simp only [eq_ratCast, map_ratCast]
  rw [hc] at hn
  exact (PadicAlgCl.norm_extends p _).symm.trans_le hn

private theorem integral_multiple_coprime {p : ℕ} [Fact p.Prime] {F : Type} [Field F] [NumberField F] (x : F)
    (h : ∀ i, ¬ p ∣ ((minpoly ℚ x).coeff i).den) :
    ∃ (m : ℕ) (c : 𝓞 F), m.Coprime p ∧ (c : F) = m * x := by
  have hx : IsIntegral ℚ x := Algebra.IsIntegral.isIntegral x
  set P := minpoly ℚ x with hP
  set M : ℕ := ∏ i ∈ Finset.range (P.natDegree + 1), (P.coeff i).den with hM
  have hMcop : M.Coprime p :=
    Nat.Coprime.prod_left fun i _ =>
      ((Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)).mpr (h i)).symm
  have hQ : P.scaleRoots (M : ℚ) ∈ Polynomial.lifts (Int.castRingHom ℚ) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro i
    rw [Polynomial.coeff_scaleRoots]
    by_cases hi : i ≤ P.natDegree
    · rcases hi.lt_or_eq with hlt | heq
      · obtain ⟨k, hk⟩ : (P.coeff i).den ∣ M :=
          Finset.dvd_prod_of_mem _ (Finset.mem_range.mpr (by omega))
        have hc : P.coeff i * M = (P.coeff i).num * k := by
          rw [hk]
          push_cast
          rw [← _root_.mul_assoc, Rat.mul_den_eq_num]
        have hpow : (M : ℚ) ^ (P.natDegree - i) = M * M ^ (P.natDegree - i - 1) := by
          rw [← pow_succ']
          congr 1
          omega
        refine ⟨(P.coeff i).num * k * M ^ (P.natDegree - i - 1), ?_⟩
        rw [hpow, ← _root_.mul_assoc, hc]
        simp
      · subst heq
        refine ⟨1, ?_⟩
        rw [Nat.sub_self, pow_zero, _root_.mul_one, map_one]
        exact (minpoly.monic hx).leadingCoeff.symm
    · refine ⟨0, ?_⟩
      simp [Polynomial.coeff_eq_zero_of_natDegree_lt (not_le.mp hi)]
  have hmon : (P.scaleRoots (M : ℚ)).Monic := (Polynomial.monic_scaleRoots_iff _).mpr (minpoly.monic hx)
  obtain ⟨Q, hQmap, -, hQm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hQ hmon
  have hint : IsIntegral ℤ ((M : F) * x) := by
    refine ⟨Q, hQm, ?_⟩
    have h0 := Polynomial.scaleRoots_aeval_eq_zero (r := (M : ℚ)) (minpoly.aeval ℚ x)
    have hcast : Int.castRingHom ℚ = algebraMap ℤ ℚ := Subsingleton.elim _ _
    rw [← hP, ← hQmap, hcast, Polynomial.aeval_map_algebraMap, map_natCast] at h0
    rw [← Polynomial.aeval_def]
    exact h0
  exact ⟨M, ⟨(M : F) * x, hint⟩, hMcop, rfl⟩

theorem UpperTheory.Gal.W2.fInt_of :
    UpperTheory.Gal.W2.EmbAll → UpperTheory.Gal.W2.FInt := by
  intro hE p _ G x hx
  apply integral_multiple_coprime
  apply coeff_den
  intro τ
  obtain ⟨w, σ, h | h⟩ := hE p G τ
  · rw [h x]
    calc ‖σ (G.emb w x)‖ = ‖G.emb w x‖ := (spectralNorm_eq_of_equiv σ _).symm
      _ ≤ 1 := (hx w).1
  · rw [h x]
    calc ‖σ (G.emb w ((IsCMField.complexConj G.F) x))‖
        = ‖G.emb w ((IsCMField.complexConj G.F) x)‖ := (spectralNorm_eq_of_equiv σ _).symm
      _ ≤ 1 := (hx w).2
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PEmbAll
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

theorem UpperTheory.Gal.W2.embAll_of :
    UpperTheory.Gal.W2.EmbAll := by
  intro p _ G τ
  rcases HTGroupOver.liesOver_or_conj p G τ with h | h
  · obtain ⟨i, σ, hσ⟩ := G.emb_all τ h
    refine ⟨i, σ, Or.inl fun x => ?_⟩
    rw [hσ]
    rfl
  · obtain ⟨i, σ, hσ⟩ := G.emb_all _ h
    refine ⟨i, σ, Or.inr fun x => ?_⟩
    have hx := congrArg (fun f : G.F →+* PadicAlgCl p => f (IsCMField.complexConj G.F x)) hσ
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      conjQ_apply] at hx
    have hc : (conjQ G.F).toRingHom ((IsCMField.complexConj G.F) x) = x := by
      simp [conjQ_apply]
    rw [hc] at hx
    exact hx
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PFTrace
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

namespace UpperTheory.Gal.W2.FrobeniusTrace

variable {p : ℕ} [Fact p.Prime]

private theorem not_both (G : HTGroup p) (τ : G.F →+* PadicAlgCl p) (h1 : LiesOver G.Kq G.u τ)
    (h2 : LiesOver G.Kq G.u (τ.comp (IsCMField.complexConj G.F : G.F →+* G.F))) : False := by
  obtain ⟨x, hx, hne⟩ := CentAtP.exists_conj_ne G
  apply hne
  apply τ.injective
  have a := h1 ⟨x, hx⟩
  have b := h2 ⟨x, hx⟩
  exact b.trans a.symm

private theorem exists_ext (E : IntermediateField ℚ_[p] (PadicAlgCl p))
    (s : E →ₐ[ℚ_[p]] PadicAlgCl p) :
    ∃ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p, ∀ y : E, σ (y : PadicAlgCl p) = s y := by
  obtain ⟨φ, hφ⟩ := IntermediateField.exists_algHom_of_splits
    (fun z => ⟨Algebra.IsIntegral.isIntegral z, IsAlgClosed.splits _⟩) s
  refine ⟨AlgEquiv.ofBijective φ (Algebra.IsAlgebraic.algHom_bijective φ), fun y => ?_⟩
  rw [AlgEquiv.ofBijective_apply]
  exact congrArg (fun f => f y) hφ

private theorem hom_ext {F : Type} [Field F] (τ : F →+* PadicAlgCl p)
    (s s' : FwOf τ →ₐ[ℚ_[p]] PadicAlgCl p) (h : ∀ x, s (embOf τ x) = s' (embOf τ x)) : s = s' := by
  refine IntermediateField.algHom_ext_of_eq_adjoin ℚ_[p]
    (rfl : FwOf τ = IntermediateField.adjoin ℚ_[p] (Set.range τ)) ?_
  rintro _ ⟨x, rfl⟩
  exact h x

private theorem sigma_eq (G : HTGroup p) {w w' : Fin G.m} (s : G.Fw w →ₐ[ℚ_[p]] PadicAlgCl p)
    (s' : G.Fw w' →ₐ[ℚ_[p]] PadicAlgCl p) (h : ∀ x, s (G.embW w x) = s' (G.embW w' x)) :
    (⟨w, s⟩ : Σ w, G.Fw w →ₐ[ℚ_[p]] PadicAlgCl p) = ⟨w', s'⟩ := by
  obtain ⟨σ, hσ⟩ := exists_ext _ s
  obtain ⟨σ', hσ'⟩ := exists_ext _ s'
  have hw : w = w' := by
    refine G.emb_inj w w' (σ.trans σ'.symm) (RingHom.ext fun x => ?_)
    have e1 : σ (G.emb w x) = s (G.embW w x) := hσ (G.embW w x)
    have e2 : σ' (G.emb w' x) = s' (G.embW w' x) := hσ' (G.embW w' x)
    change σ'.symm (σ (G.emb w x)) = G.emb w' x
    rw [e1, h, ← e2, AlgEquiv.symm_apply_apply]
  subst hw
  rw [hom_ext (G.emb w) s s' h]

private theorem liesOver_comp (G : HTGroup p) {w : Fin G.m} (s : G.Fw w →ₐ[ℚ_[p]] PadicAlgCl p) :
    LiesOver G.Kq G.u ((s : G.Fw w →+* PadicAlgCl p).comp (G.embW w)) := by
  intro x
  have e : G.embW w (x : G.F) = algebraMap ℚ_[p] (G.Fw w) (G.u x) := Subtype.ext (G.emb_over w x)
  change s (G.embW w (x : G.F)) = _
  rw [e, s.commutes]

private noncomputable def phi (G : HTGroup p) :
    ((Σ w, G.Fw w →ₐ[ℚ_[p]] PadicAlgCl p) ⊕ (Σ w, G.Fw w →ₐ[ℚ_[p]] PadicAlgCl p)) →
      (G.F →ₐ[ℚ] PadicAlgCl p)
  | .inl a => ((a.2 : G.Fw a.1 →+* PadicAlgCl p).comp (G.embW a.1)).toRatAlgHom
  | .inr a => ((a.2 : G.Fw a.1 →+* PadicAlgCl p).comp
      ((G.embW a.1).comp (IsCMField.complexConj G.F : G.F →+* G.F))).toRatAlgHom

private theorem phi_inl (G : HTGroup p) (a : Σ w, G.Fw w →ₐ[ℚ_[p]] PadicAlgCl p) (x : G.F) :
    phi G (.inl a) x = a.2 (G.embW a.1 x) := rfl

private theorem phi_inr (G : HTGroup p) (a : Σ w, G.Fw w →ₐ[ℚ_[p]] PadicAlgCl p) (x : G.F) :
    phi G (.inr a) x = a.2 (G.embW a.1 (IsCMField.complexConj G.F x)) := rfl

private theorem phi_ne (G : HTGroup p) (a b : Σ w, G.Fw w →ₐ[ℚ_[p]] PadicAlgCl p) :
    phi G (.inl a) ≠ phi G (.inr b) := by
  intro h
  refine not_both G _ (liesOver_comp G a.2) fun k => ?_
  have e := DFunLike.congr_fun h (IsCMField.complexConj G.F (k : G.F))
  rw [phi_inl, phi_inr, IsCMField.complexConj_apply_apply] at e
  exact e.trans (liesOver_comp G b.2 k)

private theorem phi_injective (G : HTGroup p) : Function.Injective (phi G) := by
  rintro (⟨w, s⟩ | ⟨w, s⟩) (⟨w', s'⟩ | ⟨w', s'⟩) hab
  · rw [sigma_eq G s s' fun x => (phi_inl G ⟨w, s⟩ x).symm.trans
      ((DFunLike.congr_fun hab x).trans (phi_inl G ⟨w', s'⟩ x))]
  · exact absurd hab (phi_ne G _ _)
  · exact absurd hab.symm (phi_ne G _ _)
  · have key : ∀ y, s (G.embW w y) = s' (G.embW w' y) := by
      intro y
      have e := (phi_inr G ⟨w, s⟩ (IsCMField.complexConj G.F y)).symm.trans
        ((DFunLike.congr_fun hab _).trans (phi_inr G ⟨w', s'⟩ _))
      rwa [IsCMField.complexConj_apply_apply] at e
    rw [sigma_eq G s s' key]

private theorem phi_surjective (hE : EmbAll) (G : HTGroup p) : Function.Surjective (phi G) := by
  intro ψ
  obtain ⟨w, σ, h | h⟩ := hE p G ψ.toRingHom
  · refine ⟨.inl ⟨w, σ.toAlgHom.comp (G.Fw w).val⟩, AlgHom.ext fun x => ?_⟩
    rw [phi_inl]
    exact (h x).symm
  · refine ⟨.inr ⟨w, σ.toAlgHom.comp (G.Fw w).val⟩, AlgHom.ext fun x => ?_⟩
    rw [phi_inr]
    exact (h x).symm

end UpperTheory.Gal.W2.FrobeniusTrace

open UpperTheory.Gal.W2.FrobeniusTrace in
theorem UpperTheory.Gal.W2.fTrace_of :
    UpperTheory.Gal.W2.EmbAll → UpperTheory.Gal.W2.FTrace := by
  intro hE p _ G x
  apply (algebraMap ℚ_[p] (PadicAlgCl p)).injective
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_add (f := _), map_sum, map_sum]
  have hl : algebraMap ℚ_[p] (PadicAlgCl p) ((Algebra.trace ℚ G.F x : ℚ) : ℚ_[p])
      = algebraMap ℚ (PadicAlgCl p) (Algebra.trace ℚ G.F x) := by
    simp only [map_ratCast, eq_ratCast]
  rw [hl]
  simp_rw [trace_eq_sum_embeddings (E := PadicAlgCl p)]
  rw [← Fintype.sum_bijective (phi G) ⟨phi_injective G, phi_surjective hE G⟩
    (fun a => phi G a x) (fun σ => σ x) (fun _ => rfl)]
  rw [Fintype.sum_sum_type, Fintype.sum_sigma, Fintype.sum_sigma]
  simp only [phi_inl, phi_inr]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PIsogCoord
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

namespace UpperTheory.Gal.W2.IsogenyReduction

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p}

private theorem exists_bound (k : Module.End (AfP p) (AfP p ⊗[ℚ] VQ D)) :
    ∃ c : ℕ, 0 < c ∧ ∀ z ∈ LaHat D, c • k z ∈ LaHat D := by
  haveI := D.freeLa
  haveI := D.finLa
  let b := Module.Free.chooseBasis ℤ D.La
  let S : Set (AfP p) := Set.range (fun ij : Module.Free.ChooseBasisIndex ℤ D.La × Module.Free.ChooseBasisIndex ℤ D.La =>
    (KNLevel.bA b).repr (k (KNLevel.bA b ij.2)) ij.1)
  have hS : IsCompact S := (Set.finite_range _).isCompact
  obtain ⟨c, hc, hcS⟩ := GlobalTheory.T.exists_common_pos_denominator_of_isCompact_finiteAdeleAway p S hS
  refine ⟨c, hc, ?_⟩
  have hB : ∀ j, inAf D (b j) = KNLevel.bA b j := by
    intro j
    simp [KNLevel.bA, inAf, Algebra.TensorProduct.basis_apply]
  have hgen : ∀ j, c • k (inAf D (b j)) ∈ LaHat D := by
    intro j
    apply KNLevel.mem_laHat_of_repr b
    intro i
    rw [hB j, map_nsmul, Finsupp.smul_apply, nsmul_eq_mul]
    exact hcS _ ⟨(i, j), rfl⟩
  have hall : ∀ x : D.La, (c • k) (inAf D x) ∈ LaHat D := by
    intro x
    let f : D.La →+ (AfP p ⊗[ℚ] VQ D) :=
      ((c • k).toAddMonoidHom).comp (AddMonoidHom.mk' (inAf D) GammaUniq.inAf_add)
    have hf : ∀ y, f y = (c • k) (inAf D y) := fun y => rfl
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hf, ← b.sum_repr x, map_sum]
    refine AddSubgroup.sum_mem _ (fun j _ => ?_)
    rw [map_zsmul]
    exact AddSubgroup.zsmul_mem _ (hgen j) _
  intro z hz
  exact GammaUniq.map_mem (c • k) hall hz

private theorem end_eq (k T : Module.End (AfP p) (AfP p ⊗[ℚ] VQ D))
    (h : ∀ (a : D.La) (n : ℕ), 0 < n → n.Coprime p → ∃ w ∈ LaHat D, ∃ w' ∈ LaHat D,
      k (inAf D a) = T (inAf D a) + n • w + n • k w') : k = T := by
  apply GammaUniq.end_ext
  intro a
  obtain ⟨c, hc, hcb⟩ := exists_bound k
  have hz : c • (k (inAf D a) - T (inAf D a)) = 0 := by
    apply GammaUniq.eq_zero_of_dvd_laHat
    intro n hn hnp
    obtain ⟨w, hw, w', hw', he⟩ := h a n hn hnp
    refine ⟨c • w + c • k w', add_mem (AddSubgroup.nsmul_mem _ hw c) (hcb w' hw'), ?_⟩
    have hd : k (inAf D a) - T (inAf D a) = n • w + n • k w' := by
      rw [he]
      abel
    rw [hd, smul_add, smul_add, smul_comm c n w, smul_comm c n (k w')]
  have hX : k (inAf D a) - T (inAf D a) = 0 := by
    rw [← Nat.cast_smul_eq_nsmul ℚ] at hz
    exact (smul_eq_zero.mp hz).resolve_left (by exact_mod_cast hc.ne')
  exact sub_eq_zero.mp hX

variable (L : Link D G)

private theorem rd_add (x : (AfP p ⊗[ℚ] G.C)ˣ) (g : G.GAf) (u w : VQ D) :
    rd L x g (u + w) = rd L x g u + rd L x g w := by
  simp only [rd, TensorProduct.tmul_add, map_add (f := _)]

private theorem rd_nsmul (x : (AfP p ⊗[ℚ] G.C)ˣ) (g : G.GAf) (n : ℕ) (w : VQ D) :
    rd L x g (n • w) = n • rd L x g w := by
  induction n with
  | zero =>
    simp only [zero_smul, UpperTheory.Gal.W2.rd, TensorProduct.tmul_zero, map_zero]
  | succ n ih =>
    rw [succ_nsmul, rd_add, ih, succ_nsmul]

private theorem rd_eq (x : (AfP p ⊗[ℚ] G.C)ˣ) (g h : G.GAf) (w : VQ D) :
    rd L x h w = L.actG (h⁻¹ * g) (rd L x g w) := by
  unfold UpperTheory.Gal.W2.rd
  rw [← Module.End.mul_apply (L.actG (h⁻¹ * g)), ← map_mul, mul_inv_cancel_right]

private theorem coord_of (x : (AfP p ⊗[ℚ] G.C)ˣ) {N : ℕ} {D' : PLat D.O D.inv} {t t₀ : D.La → D'.La}
    {j : D'.La →+ VQ D} {g : G.GAf} (hc : IsCoordA L x N D' t₀ j g) (h : ∀ a, ∃ u, t₀ a = t a + N • u) :
    IsCoordA L x N D' t j g := by
  refine ⟨hc.1, fun a => ?_⟩
  obtain ⟨w, hw, he⟩ := hc.2 a
  obtain ⟨u, hu⟩ := h a
  have hmem : rd L x g (j u) ∈ LaHat D := (hc.1 (j u)).mp ⟨0, u, by simp⟩
  refine ⟨w - rd L x g (j u), sub_mem hw hmem, ?_⟩
  rw [hu, map_add (f := _), map_nsmul, rd_add, rd_nsmul] at he
  rw [smul_sub, ← add_sub_assoc, ← he, add_sub_cancel_right]

end UpperTheory.Gal.W2.IsogenyReduction

open UpperTheory.Gal.W2.IsogenyReduction in
theorem UpperTheory.Gal.W2.isogCoord_of :
    UpperTheory.Gal.W2.AdOfWit → UpperTheory.Gal.W2.CoordKN → UpperTheory.Gal.W2.IsogForm → UpperTheory.Gal.W2.RdDense → UpperTheory.Gal.W2.IsogCoord := by
  intro hAd hCo hIf hRd p _ D G L B N N' hN hNp hN' hN'p h hconj ρ D' t D'' t'' P P'' inc d hP hP'' hPP
    hdp hd f nu f'' nu'' hf hf'' hft hft'' hiff j h₁ M hpl hco hloc
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact (Fact.out : p.Prime).one_lt.ne' (Nat.coprime_zero_left _ |>.mp hdp)
  have hd' : (d : ℚ) ≠ 0 := by exact_mod_cast hd0
  have hinc : Function.Injective inc := fun u1 u2 he => hP.2.1 (by rw [← hPP u1, ← hPP u2, he])
  obtain ⟨lift, hlift⟩ : ∃ lift : D''.La → D'.La, ∀ u'', inc (lift u'') = d • u'' :=
    ⟨fun u'' => (hd u'').choose, fun u'' => (hd u'').choose_spec⟩
  have hlift_add : ∀ a b, lift (a + b) = lift a + lift b := fun a b =>
    hinc (by rw [map_add (f := _), hlift, hlift, hlift, smul_add])
  have hlift_inc : ∀ u, lift (inc u) = d • u := fun u => hinc (by rw [hlift, map_nsmul])
  obtain ⟨j'', hj''⟩ : ∃ j'' : D''.La →+ VQ D, ∀ u'', j'' u'' = (d : ℚ)⁻¹ • j (lift u'') :=
    ⟨AddMonoidHom.mk' (fun u'' => (d : ℚ)⁻¹ • j (lift u''))
      (fun a b => by simp only [hlift_add, map_add (f := _), smul_add]), fun _ => rfl⟩
  have hj''d : ∀ u'', (d : ℚ) • j'' u'' = j (lift u'') := by
    intro u''
    rw [hj'', smul_smul, mul_inv_cancel₀ hd', one_smul]
  have hj''inc : ∀ u, j'' (inc u) = j u := by
    intro u
    rw [hj'', hlift_inc, map_nsmul, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul, inv_mul_cancel₀ hd', one_smul]
  have hpl'' : IsPlace L B.β D'' j'' := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro a b hab
      have h1 : j (lift a) = j (lift b) := by rw [← hj''d, ← hj''d, hab]
      have h2 := hpl.1 h1
      have h3 : d • a = d • b := by rw [← hlift, ← hlift, h2]
      haveI := D''.free
      have h4 : (d : ℤ) • a = (d : ℤ) • b := by rw [natCast_zsmul, natCast_zsmul]; exact h3
      exact smul_right_injective D''.La (by exact_mod_cast hd0 : (d : ℤ) ≠ 0) h4
    · intro c u
      have hl : lift (c • u) = c • lift u := hinc (by
        rw [hlift, map_smul, hlift]
        exact smul_comm d c u)
      rw [hj'', hj'', hl, hpl.2.1, map_smul]
    · intro w
      obtain ⟨m, u, hm, hmw⟩ := hpl.2.2.1 w
      exact ⟨m, inc u, hm, by rw [hj''inc]; exact hmw⟩
    · obtain ⟨r, hr, hrEF⟩ := hIf p D G L h ρ D' D'' P P'' inc hP hP'' hPP f nu f'' nu'' hf hf'' hiff
      obtain ⟨s, hs, hsEF⟩ := hpl.2.2.2
      refine ⟨r * s, mul_pos hr hs, fun u1 u2 => ?_⟩
      have key : ((D''.EF (d • u1) (d • u2) : ℤ) : ℚ) = (d : ℚ) * d * (D''.EF u1 u2) := by
        simp only [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul]
        push_cast
        ring
      have hform : ∀ (c : ℚ) (x y : VQ D), formB L B.β (c • x) (c • y) = c * c * formB L B.β x y := by
        intro c x y
        simp only [formB, map_smul, LinearMap.smul_apply, smul_eq_mul]
        ring
      calc ((D''.EF u1 u2 : ℤ) : ℚ) = ((d : ℚ) * d)⁻¹ * (D''.EF (d • u1) (d • u2) : ℤ) := by
            rw [key]
            field_simp
        _ = ((d : ℚ) * d)⁻¹ * (D''.EF (inc (lift u1)) (inc (lift u2)) : ℤ) := by rw [hlift, hlift]
        _ = ((d : ℚ) * d)⁻¹ * (r * (D'.EF (lift u1) (lift u2) : ℤ)) := by rw [hrEF]
        _ = ((d : ℚ) * d)⁻¹ * (r * (s * formB L B.β (j (lift u1)) (j (lift u2)))) := by rw [hsEF]
        _ = r * s * formB L B.β (j'' u1) (j'' u2) := by
            rw [← hj''d u1, ← hj''d u2, hform]
            field_simp
  have hloc'' : IsLocP D'' j'' M := by
    intro w
    constructor
    · rintro ⟨m, u'', hm, hmw⟩
      refine (hloc w).mp ⟨d * m, lift u'', Nat.Coprime.mul_left hdp hm, ?_⟩
      rw [mul_smul, hmw, ← hj''d, Nat.cast_smul_eq_nsmul]
    · intro hw
      obtain ⟨m, u, hm, hmw⟩ := (hloc w).mpr hw
      exact ⟨m, inc u, hm, by rw [hj''inc]; exact hmw⟩
  obtain ⟨h₂, hR₂⟩ := hAd p D G L B D'' j'' hpl'' f'' nu'' hf''
  obtain ⟨h₃, hR₃⟩ := hAd p D G L B D' j hpl f nu hf
  have hc₂ : IsCoordA L (trivX B) N D'' t'' j'' h₂ := coord_of L (trivX B) (hR₂ N hN hNp) hft''
  have hc₃ : IsCoordA L (trivX B) N' D' t j h₃ := coord_of L (trivX B) (hR₃ N' hN' hN'p) hft
  have hk₃ : h₃⁻¹ * h₁ ∈ L.KN N' := (hCo p D G L (trivX B) N' hN' hN'p D' t j h₁ h₃ hco).mp hc₃
  have hkey : h₂⁻¹ * h₃ = h := by
    apply GammaUniq.actG_injective L
    apply end_eq
    intro a n hn hnp
    obtain ⟨w₃, hw₃m, hw₃⟩ := (hR₃ n hn hnp).2 a
    obtain ⟨b, e, he⟩ := (hf''.2 n hn hnp).2.2.2.1 (inc (f n a))
    obtain ⟨wT, hwTm, hT⟩ := (hiff n hn hnp a b).mp ⟨e, he⟩
    obtain ⟨w₂, hw₂m, hw₂⟩ := (hR₂ n hn hnp).2 b
    have hrm : rd L (trivX B) h₂ (j'' e) ∈ LaHat D := ((hR₂ n hn hnp).1 (j'' e)).mp ⟨0, e, by simp⟩
    refine ⟨w₂ + rd L (trivX B) h₂ (j'' e) - wT, sub_mem (add_mem hw₂m hrm) hwTm, -w₃, neg_mem hw₃m, ?_⟩
    have eA : rd L (trivX B) h₂ (j (f n a)) = L.actG (h₂⁻¹ * h₃) (inAf D a) + n • L.actG (h₂⁻¹ * h₃) w₃ := by
      rw [rd_eq L (trivX B) h₃ h₂, hw₃, map_add (f := _), map_nsmul]
    have eB : rd L (trivX B) h₂ (j (f n a)) = inAf D b + n • w₂ + n • rd L (trivX B) h₂ (j'' e) := by
      rw [← hj''inc, he, map_add (f := _), map_nsmul, rd_add, rd_nsmul, hw₂]
    have e1 := eA.symm.trans eB
    rw [eq_sub_of_add_eq e1, hT]
    simp only [smul_add, smul_sub, map_neg, smul_neg]
    abel
  have hh₂ : h₂ = h₃ * h⁻¹ := by
    rw [← hkey, mul_inv_rev, inv_inv, mul_inv_cancel_left]
  refine ⟨j'', hj''inc, hpl'', ?_, hloc''⟩
  apply (hCo p D G L (trivX B) N hN hNp D'' t'' j'' h₂ (h₁ * h⁻¹) hc₂).mpr
  have hx : (h₁ * h⁻¹)⁻¹ * h₂ = h * (h₃⁻¹ * h₁)⁻¹ * h⁻¹ := by
    rw [hh₂]
    group
  rw [hx]
  exact hconj _ (inv_mem hk₃)
end

