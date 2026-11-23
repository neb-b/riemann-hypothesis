module

public import Mathlib
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsRegularOfSupportDimQuotientAddLengthLe
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0028
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0012
public import ReciprocityTheory.CommutativeAlgebra.SaturatedChains.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0014
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0005

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaCotQuot
section
open IsLocalRing UpperTheory.V.AlgebraTools

theorem UpperTheory.V.AlgebraTools.regular_quotient_cotInd :
    ∀ (R : Type) [CommRing R] [IsRegularLocalRing R] (κ : Type) [Fintype κ] (x : κ → R), CotInd R x →
      IsRegularLocalRing (R ⧸ Ideal.span (Set.range x)) ∧
      ringKrullDim (R ⧸ Ideal.span (Set.range x)) + (Fintype.card κ : ℕ) = ringKrullDim R ∧
      (Ideal.span (Set.range x)).IsPrime := by
  intro R _ _ κ _ x hx
  classical
  obtain ⟨s, y, -, hs, hc⟩ := cotInd_extend R κ x hx
  rw [Set.Sum.elim_range] at hs
  have hd : ringKrullDim R = ((Fintype.card κ + s : ℕ) : WithBot ℕ∞) := by
    rw [hc, IsRegularLocalRing.spanFinrank_maximalIdeal]
  set I := Ideal.span (Set.range x) with hI
  have hle : I ≤ maximalIdeal R := by
    rw [← hs]
    exact Ideal.span_mono Set.subset_union_left
  have hne : I ≠ ⊤ := fun h => Ideal.IsPrime.ne_top' (top_le_iff.mp (h ▸ hle))
  have : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hne
  have : IsLocalRing (R ⧸ I) := .of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have hmax : Ideal.map (Ideal.Quotient.mk I) (maximalIdeal R) = maximalIdeal (R ⧸ I) :=
    map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective
  have hspan : Ideal.span (Set.range fun i => Ideal.Quotient.mk I (y i)) = maximalIdeal (R ⧸ I) := by
    rw [← hmax, ← hs, Ideal.span_union, Ideal.map_sup, ← hI, Ideal.map_quotient_self, bot_sup_eq,
      Ideal.map_span, ← Set.range_comp]
    rfl
  have hfin : ((maximalIdeal (R ⧸ I)).spanFinrank : WithBot ℕ∞) ≤ (s : ℕ) := by
    rw [← hspan]
    have h1 := Submodule.spanFinrank_span_le_ncard_of_finite (R := R ⧸ I)
      (Set.finite_range fun i => Ideal.Quotient.mk I (y i))
    have h2 : (Set.range fun i => Ideal.Quotient.mk I (y i)).ncard ≤ s := by
      rw [← Set.image_univ]
      exact (Set.ncard_image_le Set.finite_univ).trans (by simp [Set.ncard_univ])
    exact_mod_cast h1.trans h2
  have hdim : ((s : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ I) := by
    have h1 := ringKrullDim_le_ringKrullDim_quotient_add_encard (Set.range x)
      (by
        rw [IsLocalRing.ringJacobson_eq_maximalIdeal]
        rintro _ ⟨k, rfl⟩
        exact hx.mem k)
    rw [hd] at h1
    have h2 : (Set.range x).encard ≤ (Fintype.card κ : ℕ∞) := by
      rw [← Set.image_univ]
      refine (Set.encard_image_le _ _).trans ?_
      rw [Set.encard_univ, ENat.card_eq_coe_fintype_card]
    have hnb : ringKrullDim (R ⧸ I) ≠ ⊥ := ringKrullDim_ne_bot
    obtain ⟨n, hn⟩ := WithBot.ne_bot_iff_exists.mp hnb
    rw [← hn] at h1 ⊢
    have h3 : (Fintype.card κ : ℕ∞) + (s : ℕ∞) ≤ n + (Set.range x).encard := by
      exact_mod_cast h1
    have h4 : (s : ℕ∞) + (Fintype.card κ : ℕ∞) ≤ n + (Fintype.card κ : ℕ∞) := by
      rw [add_comm]
      exact h3.trans (by gcongr)
    have h5 : (s : ℕ∞) ≤ n := (ENat.add_le_add_iff_right (ENat.natCast_ne_top _)).mp h4
    exact_mod_cast h5
  have hreg : IsRegularLocalRing (R ⧸ I) := .of_spanFinrank_maximalIdeal_le _ (hfin.trans hdim)
  have heq : ringKrullDim (R ⧸ I) = (s : ℕ) :=
    le_antisymm ((ringKrullDim_le_spanFinrank_maximalIdeal _).trans hfin) hdim
  refine ⟨hreg, ?_, ?_⟩
  · rw [heq, hd, add_comm]
    push_cast
    rfl
  · exact (Ideal.Quotient.isDomain_iff_prime I).1 (GlobalTheory.isDomain_of_isRegularLocalRing _)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaCplEx
section
open IsLocalRing UpperTheory.V.AlgebraTools

private lemma mem_pow_iff (L : Type) [CommRing L] [IsNoetherianRing L] [IsLocalRing L] (n : ℕ)
    (x : AdicCompletion (maximalIdeal L) L) :
    x ∈ maximalIdeal (AdicCompletion (maximalIdeal L) L) ^ n ↔
      AdicCompletion.eval (maximalIdeal L) L n x = 0 := by
  rw [AdicCompletion.maximalIdeal_eq_map, ← Ideal.map_pow, ← Submodule.restrictScalars_mem L,
    ← Ideal.smul_top_eq_map,
    AdicCompletion.pow_smul_top_eq_ker_eval (maximalIdeal L).fg_of_isNoetherianRing]
  rfl

private lemma strict_loc (L : Type) [CommRing L] [IsNoetherianRing L] [IsLocalRing L] (n : ℕ)
    (a : L) (h : algebraMap L (AdicCompletion (maximalIdeal L) L) a ∈
      maximalIdeal (AdicCompletion (maximalIdeal L) L) ^ n) : a ∈ maximalIdeal L ^ n := by
  rw [mem_pow_iff, AdicCompletion.algebraMap_apply, AdicCompletion.eval_apply,
    AdicCompletion.of_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h
  simpa [smul_eq_mul, Ideal.mul_top] using h

private lemma dense_loc (L : Type) [CommRing L] [IsNoetherianRing L] [IsLocalRing L] (n : ℕ)
    (b : AdicCompletion (maximalIdeal L) L) :
    ∃ a : L, b - algebraMap L (AdicCompletion (maximalIdeal L) L) a ∈
      maximalIdeal (AdicCompletion (maximalIdeal L) L) ^ n := by
  obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective _ (AdicCompletion.eval (maximalIdeal L) L n b)
  refine ⟨a, ?_⟩
  rw [mem_pow_iff, map_sub, ← ha, AdicCompletion.algebraMap_apply, AdicCompletion.eval_apply,
    AdicCompletion.of_apply]
  simp

theorem UpperTheory.V.AlgebraTools.isCplAt_cplAt :
    ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (p : Ideal R) [p.IsPrime], IsCplAt R p (CplAt R p) := by
  intro R _ _ p _
  let L := Localization.AtPrime p
  have hRB : ∀ r : R, algebraMap R (CplAt R p) r =
      algebraMap L (CplAt R p) (algebraMap R L r) := fun r =>
    IsScalarTower.algebraMap_apply R L (CplAt R p) r
  refine ⟨GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion L (maximalIdeal L), inferInstance, ?_, ?_, ?_⟩
  · rw [IsScalarTower.algebraMap_eq R L (CplAt R p), ← Ideal.comap_comap,
      IsLocalRing.maximalIdeal_comap]
    exact Localization.AtPrime.under_maximalIdeal
  · intro n b
    obtain ⟨a', ha'⟩ := dense_loc L n b
    obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl a'
    refine ⟨r, s, s.2, ?_⟩
    have e : algebraMap R (CplAt R p) s * b - algebraMap R (CplAt R p) r =
        algebraMap R (CplAt R p) s *
          (b - algebraMap L (CplAt R p) (IsLocalization.mk' L r s)) := by
      rw [mul_sub, hRB, hRB, ← map_mul, mul_comm (algebraMap R L s), IsLocalization.mk'_spec]
    rw [e]
    exact Ideal.mul_mem_left _ _ ha'
  · intro n a ha
    rw [hRB] at ha
    have h1 := strict_loc L n _ ha
    rw [← Localization.AtPrime.map_eq_maximalIdeal, ← Ideal.map_pow,
      IsLocalization.mem_map_algebraMap_iff p.primeCompl] at h1
    obtain ⟨⟨⟨b, hb⟩, s⟩, hx⟩ := h1
    simp only [← map_mul] at hx
    obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists p.primeCompl L).1 hx
    refine ⟨c * s, ?_, ?_⟩
    · exact p.primeCompl.mul_mem c.2 s.2
    · have : (c : R) * s * a = c * b := by
        rw [mul_assoc, mul_comm (s : R) a]
        exact hc
      rw [this]
      exact Ideal.mul_mem_left _ _ hb
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaCplUniq
section
open IsLocalRing UpperTheory.V.AlgebraTools

theorem UpperTheory.V.AlgebraTools.IsCplAt.nonempty_algEquiv :
    ∀ (R : Type) [CommRing R] (p : Ideal R) (B : Type) [CommRing B] [IsLocalRing B] [Algebra R B] (B' : Type) [CommRing B'] [IsLocalRing B'] [Algebra R B'],
      IsCplAt R p B → IsCplAt R p B' → Nonempty (B ≃ₐ[R] B') := by
  intro R _ p B _ _ _ B' _ _ _ hB hB'
  haveI : IsAdicComplete (maximalIdeal B) B := hB.complete
  haveI : IsAdicComplete (maximalIdeal B') B' := hB'.complete
  obtain ⟨ψ, hψ, -⟩ := IsCplAt.existsUnique_lift R p B hB B' (algebraMap R B') hB'.comap_eq
  obtain ⟨χ, hχ, -⟩ := IsCplAt.existsUnique_lift R p B' hB' B (algebraMap R B) hB.comap_eq
  obtain ⟨_, -, huB⟩ := IsCplAt.existsUnique_lift R p B hB B (algebraMap R B) hB.comap_eq
  obtain ⟨_, -, huB'⟩ := IsCplAt.existsUnique_lift R p B' hB' B' (algebraMap R B') hB'.comap_eq
  have h1 : χ.comp ψ = RingHom.id B := by
    have ha : (χ.comp ψ).comp (algebraMap R B) = algebraMap R B := by
      rw [RingHom.comp_assoc, hψ, hχ]
    rw [huB _ ha, huB (RingHom.id B) (RingHom.id_comp _)]
  have h2 : ψ.comp χ = RingHom.id B' := by
    have ha : (ψ.comp χ).comp (algebraMap R B') = algebraMap R B' := by
      rw [RingHom.comp_assoc, hχ, hψ]
    rw [huB' _ ha, huB' (RingHom.id B') (RingHom.id_comp _)]
  refine ⟨AlgEquiv.ofRingEquiv (f := RingEquiv.ofRingHom ψ χ h2 h1) ?_⟩
  intro x
  exact congrArg (fun φ : R →+* B' => φ x) hψ
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaDepthCat
section
open IsLocalRing

theorem UpperTheory.V.AlgebraTools.exists_isRegular_of_free_quotient :
    ∀ (L B : Type) [CommRing L] [IsRegularLocalRing L] [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
      [Algebra L B] [IsLocalHom (algebraMap L B)] (M : Type) [AddCommGroup M] [Module B M] [Module L M]
      [IsScalarTower L B M] [Module.Finite B M] [Nontrivial M] (r e : ℕ) (y : Fin r → B),
      ringKrullDim L = e → (∀ i, y i ∈ maximalIdeal B) → GlobalTheory.IsQuasiRegularSeq M y →
      Module.Free L (M ⧸ Ideal.span (Set.range y) • (⊤ : Submodule B M)) →
      ∃ xs : List B, xs.length = r + e ∧ (∀ x ∈ xs, x ∈ maximalIdeal B) ∧ RingTheory.Sequence.IsRegular M xs := by
  intro L B _ _ _ _ _ _ _ M _ _ _ _ _ _ r e y he hy hq hfree
  obtain ⟨zs, h, hd⟩ := GlobalTheory.exists_ofList_eq_maximalIdeal_length_eq L
  have hreg := (GlobalTheory.isRegular_of_ofList_eq_maximalIdeal h hd.le).toIsWeaklyRegular
  have hlen : zs.length = e := by
    rw [he] at hd
    exact_mod_cast hd
  have hmem : ∀ x ∈ List.ofFn y ++ zs.map (algebraMap L B), x ∈ maximalIdeal B := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
      exact hy i
    · refine map_maximalIdeal_le (algebraMap L B) ?_
      rw [← h, Ideal.map_ofList]
      exact Ideal.subset_span hx
  refine ⟨List.ofFn y ++ zs.map (algebraMap L B), by simp [hlen], hmem, ?_⟩
  rw [IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal hmem,
    RingTheory.Sequence.isWeaklyRegular_append_iff, GlobalTheory.ofList_ofFn_eq_span_range,
    RingTheory.Sequence.isWeaklyRegular_map_algebraMap_iff]
  refine ⟨hq.isWeaklyRegular ?_, ?_⟩
  · exact fun i => maximalIdeal_le_jacobson _ (hy i)
  · exact ((TensorProduct.lid L _).isWeaklyRegular_congr zs).mp hreg.isWeaklyRegular_rTensor
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaDimFin
section
open IsLocalRing

theorem UpperTheory.V.AlgebraTools.supportDim_le_of_finite :
    ∀ (L B : Type) [CommRing L] [IsNoetherianRing L] [CommRing B] [Algebra L B] (N : Type) [AddCommGroup N] [Module B N]
      [Module L N] [IsScalarTower L B N] [Module.Finite L N], Module.supportDim B N ≤ ringKrullDim L := by
  intro L B _ _ _ _ N _ _ _ _ _
  have hfin : Module.Finite B N := Module.Finite.of_restrictScalars_finite L B N
  rw [Module.supportDim_eq_ringKrullDim_quotient_annihilator]
  let f : B →ₐ[L] Module.End L N := Algebra.lsmul L L N
  have hf : ∀ b : B, b ∈ Module.annihilator B N → f b = 0 := by
    intro b hb
    ext n
    exact Module.mem_annihilator.mp hb n
  let g : (B ⧸ Module.annihilator B N) →ₐ[L] Module.End L N :=
    Ideal.Quotient.liftₐ (Module.annihilator B N) f hf
  have hinj : Function.Injective g := by
    refine (injective_iff_map_eq_zero g).mpr ?_
    intro q hq
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective q
    rw [Ideal.Quotient.eq_zero_iff_mem]
    refine Module.mem_annihilator.mpr (fun n => ?_)
    have h := LinearMap.congr_fun hq n
    exact h
  haveI : Algebra.IsIntegral L (B ⧸ Module.annihilator B N) :=
    ⟨fun q => (isIntegral_algHom_iff g hinj).mp (Algebra.IsIntegral.isIntegral _)⟩
  exact Order.krullDim_le_of_strictMono
    (fun P => (⟨Ideal.comap (algebraMap L (B ⧸ Module.annihilator B N)) P.asIdeal, inferInstance⟩ :
      PrimeSpectrum L))
    (fun P Q h => Ideal.IsIntegral.comap_lt_comap h)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaEquidim
section
open IsLocalRing

theorem UpperTheory.V.AlgebraTools.dim_minimalPrime_eq :
    ∀ (B : Type) [CommRing B] [IsLocalRing B] [IsNoetherianRing B] (M : Type) [AddCommGroup M] [Module B M]
      [Module.Finite B M] (xs : List B), (∀ x ∈ xs, x ∈ maximalIdeal B) → RingTheory.Sequence.IsWeaklyRegular M xs →
      Module.supportDim B M ≤ (xs.length : ℕ) →
      ∀ Z ∈ (Module.annihilator B M).minimalPrimes, ringKrullDim (B ⧸ Z) = (xs.length : ℕ) := by
  intro B _ _ _ M _ _ _ xs hxs hreg hdim Z hZ
  apply le_antisymm
  · calc ringKrullDim (B ⧸ Z) ≤ ringKrullDim (B ⧸ Module.annihilator B M) :=
          ringKrullDim_le_of_surjective (Ideal.Quotient.factor hZ.1.2)
            (Ideal.Quotient.factor_surjective hZ.1.2)
      _ = Module.supportDim B M := (Module.supportDim_eq_ringKrullDim_quotient_annihilator B M).symm
      _ ≤ _ := hdim
  · exact GlobalTheory.length_le_ringKrullDim_quotient_of_isAssociatedPrime hxs hreg
      (Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes B M hZ)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaPolyReg
section
open IsLocalRing UpperTheory.V.AlgebraTools

private theorem fibre_reg (R : Type) [CommRing R] (J n : Ideal R) [n.IsPrime] (hn : J ≤ n)
    [IsRegularRing (R ⧸ J)] (A : Type) [CommRing A] [Algebra R A] [IsLocalization.AtPrime A n] :
    IsRegularLocalRing (A ⧸ J.map (algebraMap R A)) := by
  have hJn : RingHom.ker (Ideal.Quotient.mk J) ≤ n := by
    rwa [Ideal.mk_ker]
  have hm : (n.map (Ideal.Quotient.mk J)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hJn
  have hle : J ≤ (J.map (algebraMap R A)).comap (algebraMap R A) := Ideal.le_comap_map
  letI : Algebra (R ⧸ J) (A ⧸ J.map (algebraMap R A)) := (Ideal.quotientMap _ _ hle).toAlgebra
  have hl := IsLocalization.of_surjective n.primeCompl A (S' := A ⧸ J.map (algebraMap R A))
    (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective rfl
    (by rw [Ideal.mk_ker, Ideal.mk_ker])
  have e : n.primeCompl.map (Ideal.Quotient.mk J) = (n.map (Ideal.Quotient.mk J)).primeCompl := by
    have hc : (n.map (Ideal.Quotient.mk J)).comap (Ideal.Quotient.mk J) = n := by
      rw [Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective, sup_eq_left.2 hJn]
    ext y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    constructor
    · rintro ⟨x', hx', e⟩ hx
      exact hx' (hc.le (show Ideal.Quotient.mk J x' ∈ _ from e ▸ hx))
    · exact fun hx => ⟨x, fun h => hx (Ideal.mem_map_of_mem _ h), rfl⟩
  rw [e] at hl
  have := IsRegularRing.isRegularLocalRing_localization (n.map (Ideal.Quotient.mk J))
  exact IsRegularLocalRing.of_ringEquiv (IsLocalization.algEquiv (n.map (Ideal.Quotient.mk J)).primeCompl
    (Localization.AtPrime (n.map (Ideal.Quotient.mk J))) _).toRingEquiv

theorem UpperTheory.V.AlgebraTools.regular_polynomial_localization :
    ∀ (A : Type) [CommRing A] [IsRegularLocalRing A] (σ : Type) [Finite σ] (Q : Ideal (MvPolynomial σ A)) [Q.IsPrime],
      (maximalIdeal A).map (MvPolynomial.C : A →+* MvPolynomial σ A) ≤ Q →
      IsRegularLocalRing (Localization.AtPrime Q) ∧ ∀ (κ : Type) [Fintype κ] (x : κ → A), CotInd A x →
        CotInd (Localization.AtPrime Q) (fun k => algebraMap (MvPolynomial σ A) _ (MvPolynomial.C (x k))) := by
  intro A _ _ σ _ Q _ hQ
  have hcomp : algebraMap A (Localization.AtPrime Q) =
      (algebraMap (MvPolynomial σ A) (Localization.AtPrime Q)).comp MvPolynomial.C :=
    IsScalarTower.algebraMap_eq A (MvPolynomial σ A) (Localization.AtPrime Q)
  haveI : IsRegularRing (MvPolynomial σ A ⧸
      (maximalIdeal A).map (MvPolynomial.C : A →+* MvPolynomial σ A)) := by
    letI := Ideal.Quotient.field (maximalIdeal A)
    haveI : IsRegularRing (MvPolynomial σ (A ⧸ maximalIdeal A)) := inferInstance
    exact IsRegularRing.of_ringEquiv
      (MvPolynomial.quotientEquivQuotientMvPolynomial (σ := σ) (maximalIdeal A)).toRingEquiv
  have hf := fibre_reg _ _ Q hQ (Localization.AtPrime Q)
  rw [Ideal.map_map, ← hcomp] at hf
  haveI : IsNoetherianRing (Localization.AtPrime Q) :=
    IsLocalization.isNoetherianRing Q.primeCompl _ inferInstance
  haveI : Module.Flat (MvPolynomial σ A) (Localization.AtPrime Q) :=
    IsLocalization.flat _ Q.primeCompl
  haveI : Module.Flat A (Localization.AtPrime Q) :=
    Module.Flat.trans A (MvPolynomial σ A) (Localization.AtPrime Q)
  haveI : IsLocalHom (algebraMap A (Localization.AtPrime Q)) := by
    refine ⟨fun a ha => ?_⟩
    by_contra hna
    have h1 : MvPolynomial.C a ∈ Q := hQ (Ideal.mem_map_of_mem _ ((mem_maximalIdeal a).2 hna))
    rw [hcomp] at ha
    exact (IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime Q) Q _).1 ha h1
  have H := regular_of_flat_fibre A (Localization.AtPrime Q)
  rw [hcomp] at H
  exact H
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CentraliserRank
section
open Polynomial Matrix IsLocalRing TensorProduct

theorem UpperTheory.V.AlgebraTools.centraliser_rank :
    ∀ {F : Type} [Field F] {ι : Type} [Fintype ι] [DecidableEq ι] (a : ι → F) (P : Matrix ι ι F), Function.Injective a → P.charpoly = ∏ i, (X - C (a i)) → Module.finrank F (LinearMap.ker (LinearMap.mulLeft F P - LinearMap.mulRight F P)) = Fintype.card ι ∧ ∀ Y, P * Y = Y * P → ∃ q : F[X], Y = aeval P q := by
  intro F _ ι _ _ a P ha hP
  have hu : ∀ i j, i ≠ j → IsUnit (a i - a j) := fun i j hij =>
    (sub_ne_zero.2 (fun h => hij (ha h))).isUnit
  have hCH : aeval P (∏ i, (X - C (a i))) = 0 := by
    rw [← hP]; exact Matrix.aeval_self_charpoly P
  obtain ⟨hcoi, -, -, hcomm⟩ := UpperTheory.V.AlgebraTools.lag_coi a P hu hCH
  have hne := UpperTheory.V.AlgebraTools.lag_ne_zero a P hu (by
    rw [hP, Polynomial.map_prod]; simp)
  obtain ⟨g, hg⟩ := UpperTheory.V.AlgebraTools.coi_conj_single _ hcoi hne
  have hpoly : ∀ i, ∃ q : F[X], UpperTheory.V.AlgebraTools.lag a P i = aeval P q := fun i =>
    ⟨_ • _, by rw [UpperTheory.V.AlgebraTools.lag, map_smul]⟩
  set f := UpperTheory.V.AlgebraTools.lag a P with hf
  have hinj : ∀ A B : Matrix ι ι F, (g : Matrix ι ι F) * A * ((g⁻¹ : GL ι F) : Matrix ι ι F) =
      (g : Matrix ι ι F) * B * ((g⁻¹ : GL ι F) : Matrix ι ι F) → A = B := by
    intro A B h
    exact (Units.mul_right_inj g).1 ((Units.mul_left_inj g⁻¹).1 h)
  have hmul : ∀ A B : Matrix ι ι F, (g : Matrix ι ι F) * (A * B) * ((g⁻¹ : GL ι F) : Matrix ι ι F) =
      ((g : Matrix ι ι F) * A * ((g⁻¹ : GL ι F) : Matrix ι ι F)) *
      ((g : Matrix ι ι F) * B * ((g⁻¹ : GL ι F) : Matrix ι ι F)) := by
    intro A B
    simp only [mul_assoc, Units.inv_mul_cancel_left]
  have hspan : ∀ Y, P * Y = Y * P → ∃ c : ι → F, Y = ∑ i, c i • f i := by
    intro Y hY
    set Z := (g : Matrix ι ι F) * Y * ((g⁻¹ : GL ι F) : Matrix ι ι F) with hZ
    refine ⟨fun i => Z i i, hinj _ _ ?_⟩
    rw [Finset.mul_sum, Finset.sum_mul]
    simp only [Matrix.mul_smul, Matrix.smul_mul, hg]
    rw [← hZ]
    ext i j
    rw [Matrix.sum_apply, Finset.sum_eq_single i]
    · by_cases hij : i = j
      · subst hij; simp
      · have h1 : Z * single j j (1 : F) = single j j 1 * Z := by
          rw [← hg j, hZ, ← hmul, ← hmul, (hcomm Y j hY.symm).eq]
        have h2 := congrFun (congrFun h1 i) j
        rw [Matrix.mul_single_apply_same, Matrix.single_mul_apply_of_ne _ _ _ _ _ hij] at h2
        rw [mul_one] at h2
        simp [hij, h2]
    · intro b _ hb
      simp [hb]
    · simp
  have hq : ∀ Y, P * Y = Y * P → ∃ q : F[X], Y = aeval P q := by
    intro Y hY
    obtain ⟨c, rfl⟩ := hspan Y hY
    choose q hq using hpoly
    exact ⟨∑ i, c i • q i, by simp [hq]⟩
  refine ⟨?_, hq⟩
  have hli : LinearIndependent F f := by
    rw [Fintype.linearIndependent_iff]
    intro c hc j
    have h1 : (∑ i, c i • f i) * f j = c j • f j := by
      rw [Finset.sum_mul, Finset.sum_eq_single j]
      · rw [smul_mul_assoc, (hcoi.idem j).eq]
      · intro b _ hb
        rw [smul_mul_assoc, hcoi.ortho hb, smul_zero]
      · simp
    rw [hc, zero_mul] at h1
    exact (smul_eq_zero.1 h1.symm).resolve_right (hne j)
  have hker : LinearMap.ker (LinearMap.mulLeft F P - LinearMap.mulRight F P) =
      Submodule.span F (Set.range f) := by
    apply le_antisymm
    · intro Y hY
      have hY' : P * Y = Y * P := by simpa [sub_eq_zero] using hY
      obtain ⟨c, rfl⟩ := hspan Y hY'
      exact Submodule.sum_mem _ fun i _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      have := (hcomm P i (Commute.refl P)).eq
      simpa [sub_eq_zero] using this
  rw [hker, finrank_span_eq_card hli]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.LemmaL
section
open Polynomial Matrix IsLocalRing TensorProduct UpperTheory.V.AlgebraTools

private theorem UpperTheory.V.AlgebraTools.entry_of_single {R ι : Type} [CommRing R] [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι R) (a b : ι) :
    (single a a (1 : R) * M * single b b (1 : R) : Matrix ι ι R) a b = M a b := by
  simp

theorem UpperTheory.V.AlgebraTools.lemma_L :
    ∀ {R Γ : Type} [CommRing R] [IsLocalRing R] [Group Γ] {n : ℕ} (r : Γ →* GL (Fin n) R) (ψ : Fin n → Γ →* Rˣ), (n : Cardinal) ≤ Cardinal.mk (ResidueField R) → (∀ g : Fin n → Γ, (List.ofFn fun i => ((r (g i) : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) - algebraMap R _ ((ψ i (g i) : Rˣ) : R)).prod = 0) → Function.Injective (fun i => (residue R : R →* ResidueField R).comp ((Units.coeHom R).comp (ψ i))) → (∀ z : MonoidAlgebra R Γ, (MonoidAlgebra.lift R (Matrix (Fin n) (Fin n) R) Γ ((Units.coeHom _).comp r) z).charpoly.map (residue R) = ∏ i, (X - C (residue R (MonoidAlgebra.lift R R Γ ((Units.coeHom _).comp (ψ i)) z)))) → ∃ (z : MonoidAlgebra R Γ) (g : GL (Fin n) R), (∀ i j, i ≠ j → IsUnit (MonoidAlgebra.lift R R Γ ((Units.coeHom R).comp (ψ i)) z - MonoidAlgebra.lift R R Γ ((Units.coeHom R).comp (ψ j)) z)) ∧ (∀ i, (g : Matrix (Fin n) (Fin n) R) * lag (fun i => MonoidAlgebra.lift R R Γ ((Units.coeHom R).comp (ψ i)) z) (MonoidAlgebra.lift R (Matrix (Fin n) (Fin n) R) Γ ((Units.coeHom _).comp r) z) i * ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) = single i i 1) ∧ ∀ s, (∀ i j, j < i → (g * r s * g⁻¹ : GL (Fin n) R) i j = 0) ∧ ∀ i, (g * r s * g⁻¹ : GL (Fin n) R) i i = (ψ i s : R) := by
  intro R Γ _ _ _ n r ψ hcard hprod hinj hchar
  obtain ⟨z, hz⟩ := sep_chars (fun i => (Units.coeHom R).comp (ψ i)) hcard hinj
  have hord := ord_ext ((Units.coeHom _).comp r) (fun i => (Units.coeHom R).comp (ψ i)) hprod
  obtain ⟨hcoi, htri, hdiag⟩ := lag_triangular
    (MonoidAlgebra.lift R (Matrix (Fin n) (Fin n) R) Γ ((Units.coeHom _).comp r))
    (fun i => MonoidAlgebra.lift R R Γ ((Units.coeHom R).comp (ψ i))) z hord hz
  have hne := lag_ne_zero (fun i => MonoidAlgebra.lift R R Γ ((Units.coeHom R).comp (ψ i)) z) _ hz (hchar z)
  obtain ⟨g, hg⟩ := coi_conj_single _ hcoi hne
  refine ⟨z, g, hz, hg, fun s => ?_⟩
  set e := lag (fun i => MonoidAlgebra.lift R R Γ ((Units.coeHom R).comp (ψ i)) z)
    (MonoidAlgebra.lift R (Matrix (Fin n) (Fin n) R) Γ ((Units.coeHom _).comp r) z) with he
  have hρ : MonoidAlgebra.lift R (Matrix (Fin n) (Fin n) R) Γ ((Units.coeHom _).comp r)
      (MonoidAlgebra.of R Γ s) = ((r s : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) := by
    simp [MonoidAlgebra.lift_of]
  have hχ : ∀ i, MonoidAlgebra.lift R R Γ ((Units.coeHom R).comp (ψ i)) (MonoidAlgebra.of R Γ s)
      = ((ψ i s : Rˣ) : R) := fun i => by
    simp [MonoidAlgebra.lift_of]
  have hinv : ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) * (g : Matrix (Fin n) (Fin n) R) = 1 :=
    Units.inv_mul g
  have key : ∀ i j, ((g * r s * g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) i j =
      ((g : Matrix (Fin n) (Fin n) R) * (e i * ((r s : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) * e j)
        * ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R)) i j := by
    intro i j
    refine (UpperTheory.V.AlgebraTools.entry_of_single (((g * r s * g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R)) i j).symm.trans ?_
    rw [← hg i, ← hg j]
    congr 1
    simp only [Units.val_mul, Matrix.mul_assoc]
    simp only [← Matrix.mul_assoc (((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R)), hinv, Matrix.one_mul]
  refine ⟨fun i j hji => ?_, fun i => ?_⟩
  · rw [key, ← hρ, htri _ i j hji]
    simp
  · rw [key, ← hρ, hdiag, Matrix.mul_smul, Matrix.smul_mul, hg i, hχ]
    simp
end

