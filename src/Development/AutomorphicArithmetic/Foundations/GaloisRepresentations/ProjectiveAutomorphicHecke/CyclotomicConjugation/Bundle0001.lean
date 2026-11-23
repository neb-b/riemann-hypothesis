module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.CyclotomicConjugation.QuadConjAlt
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0063
public import GroundTheory.AutomorphicForms.StrongApproximationSLDense
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0009

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.CyclotomicConjugation.ConjLoc
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.L2.Host GlobalTheory.HeckeGal
open GlobalTheory.SplitPts (conjE)
open GroundTheory.Global.AdeleBaseChange (finiteAdeleMap)
open UpperTheory.Gal.CertificateRingHomMap UpperTheory.Gal.CertificateRingHomMap.ZetaNonvanishing₂

theorem UpperTheory.Gal.CertificateRingHomMap.ZetaNonvanishing₂.conjLoc :
    UpperTheory.Gal.CertificateRingHomMap.ZetaNonvanishing₂.ConjLoc := by
  intro E _ _ _ a u
  have hp : ∀ (b : Af E) (v : Plc E), b v = pLoc E v b := fun _ _ => rfl
  refine ⟨fun h => ?_, ?_, fun m => ?_, ?_, continuous_conjFin _⟩
  · rw [hp, pLoc_conjFin, ← hp, h, map_one]
  · rw [hp, pLoc_conjFin, (conjLoc_spec (conjE E) u).2.2, ← hp]
  · have h := (conjLoc_spec (conjE E) u).2.2 ((m : ℕ) : (cj u).adicCompletion E)
    rwa [map_natCast] at h
  · refine FiniteAdeleRing.ext (R := 𝓞 E) E fun v => ?_
    rw [hp, hp a, pLoc_conjFin, pLoc_conjFin, GlobalTheory.SplitPts.conjLoc_pLoc, GlobalTheory.SplitPts.conjLoc_psi]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.CyclotomicConjugation.KPlace
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.L2.Host GlobalTheory.HeckeGal
open GlobalTheory.SplitPts (conjE)
open GroundTheory.Global.AdeleBaseChange (finiteAdeleMap)
open UpperTheory.Gal.CertificateRingHomMap UpperTheory.Gal.CertificateRingHomMap.ZetaNonvanishing₂

private theorem val_two (K : Type) [Field K] [NumberField K] (hK : Module.finrank ℚ K ≤ 2)
    (P Q : HeightOneSpectrum (𝓞 K)) (hne : P ≠ Q) (h : P.asIdeal.under ℤ = Q.asIdeal.under ℤ) :
    Valued.v ((Ideal.absNorm P.asIdeal : ℕ) : P.adicCompletion K) = WithZero.exp (-1 : ℤ) :=
  _root_.UpperTheory.Reformulated.B.UnipotentFundamentalDomain.val_two K hK P Q hne h

private theorem finrank_Kx_le {E : Type} [Field E] [NumberField E] (d : ℕ) (x : E)
    (hx : x ^ 2 = -(d : E)) : Module.finrank ℚ (Kx x) ≤ 2 := by
  have hi : IsIntegral ℚ x := Algebra.IsIntegral.isIntegral x
  have e : Module.finrank ℚ (Kx x) = (minpoly ℚ x).natDegree := IntermediateField.adjoin.finrank hi
  rw [e]
  have hm : (Polynomial.X ^ 2 + Polynomial.C (d : ℚ)).Monic :=
    Polynomial.monic_X_pow_add_C _ two_ne_zero
  have hz : Polynomial.aeval x (Polynomial.X ^ 2 + Polynomial.C (d : ℚ)) = 0 := by
    simp [hx]
  have hd := minpoly.min ℚ x hm hz
  have := Polynomial.natDegree_le_natDegree hd
  rwa [Polynomial.natDegree_X_pow_add_C] at this

private theorem sameK_iff {E : Type} [Field E] [NumberField E] (x : E) (w w' : Plc E) :
    SameK x w w' ↔ w.under (𝓞 (Kx x)) = w'.under (𝓞 (Kx x)) := by
  constructor
  · intro h
    refine HeightOneSpectrum.ext (Ideal.ext fun a => ?_)
    exact h (algebraMap (𝓞 (Kx x)) (𝓞 E) a) ((a : Kx x)).2
  · intro h y hy
    have hk : IsIntegral ℤ (⟨y, hy⟩ : Kx x) := by
      have h1 : IsIntegral ℤ (algebraMap (Kx x) E ⟨y, hy⟩) := y.isIntegral_coe
      exact (isIntegral_algebraMap_iff ).1 h1
    obtain ⟨a, ha⟩ : ∃ a : 𝓞 (Kx x), algebraMap (𝓞 (Kx x)) (𝓞 E) a = y :=
      ⟨⟨⟨y, hy⟩, hk⟩, RingOfIntegers.ext rfl⟩
    have hm : ∀ u : Plc E, a ∈ (u.under (𝓞 (Kx x))).asIdeal ↔ y ∈ u.asIdeal := by
      intro u
      rw [← ha]
      rfl
    rw [← hm w, ← hm w', h]

private theorem under_int_cj {E : Type} [Field E] [NumberField E] [IsCMField E] (K : Type) [Field K]
    [NumberField K] [Algebra K E] (w : Plc E) :
    (w.under (𝓞 K)).asIdeal.under ℤ = ((cj w).under (𝓞 K)).asIdeal.under ℤ := by
  have key : (cj w).asIdeal = Ideal.comap (RingOfIntegers.mapRingEquiv (conjE E)) w.asIdeal :=
    (GlobalTheory.Mem.Chr.conjPl_iff_comap _ _ _).1 (GlobalTheory.CuspRep.conjPl_conjSrc (conjE E) w)
  have hm : ∀ (u : Plc E) (n : ℤ), n ∈ (u.under (𝓞 K)).asIdeal.under ℤ ↔ (n : 𝓞 E) ∈ u.asIdeal := by
    intro u n
    have e : algebraMap (𝓞 K) (𝓞 E) (algebraMap ℤ (𝓞 K) n) = (n : 𝓞 E) := by simp
    rw [← e]
    rfl
  refine Ideal.ext fun n => ?_
  rw [hm, hm, key, Ideal.mem_comap, map_intCast]

theorem UpperTheory.Gal.CertificateRingHomMap.ZetaNonvanishing₂.kPlace :
    UpperTheory.Gal.CertificateRingHomMap.ZetaNonvanishing₂.KPlace := by
  intro E _ _ _ d x _ hx
  refine ⟨sameK_iff x, fun w hw => ?_⟩
  rw [sameK_iff] at hw
  exact val_two (Kx x) (finrank_Kx_le d x hx) _ _ (Ne.symm hw) (under_int_cj (Kx x) w)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.CyclotomicConjugation.NormEmb
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.L2.Host GlobalTheory.HeckeGal
open GlobalTheory.SplitPts (conjE)
open GroundTheory.Global.AdeleBaseChange (finiteAdeleMap)
open UpperTheory.Gal.CertificateRingHomMap UpperTheory.Gal.CertificateRingHomMap.ZetaNonvanishing₂

namespace UpperTheory.Gal.CertificateRingHomMap.ZetaNonvanishing₂.NormEmbeddings

private theorem eq_on_adjoin {E : Type} [Field E] [NumberField E] (x : E) (f g : E →+* ℂ)
    (h : f x = g x) (y : E) (hy : y ∈ IntermediateField.adjoin ℚ {x}) : f y = g y := by
  induction hy using IntermediateField.adjoin_induction with
  | mem z hz => rw [Set.mem_singleton_iff.1 hz]; exact h
  | algebraMap q => simp
  | add a b _ _ ha hb => simp [ha, hb]
  | inv a _ ha => simp [ha]
  | mul a b _ _ ha hb => simp [ha, hb]

private theorem norm_Kx {E : Type} [Field E] [NumberField E] (x : E) (φ : E →+* ℂ) (k : E)
    [DecidablePred fun φ' : E →+* ℂ => φ' x = φ x] :
    φ (algebraMap (Kx x) E (Algebra.norm (Kx x) k)) =
      ∏ φ' ∈ Finset.univ.filter (fun φ' : E →+* ℂ => φ' x = φ x), φ' k := by
  letI : Algebra (Kx x) ℂ := (φ.comp (algebraMap (Kx x) E)).toAlgebra
  haveI : FiniteDimensional (Kx x) E := FiniteDimensional.right ℚ (Kx x) E
  have hc : ∀ r : Kx x, algebraMap (Kx x) ℂ r = φ (algebraMap (Kx x) E r) := fun _ => rfl
  have h := Algebra.norm_eq_prod_embeddings (Kx x) ℂ k
  rw [hc] at h
  rw [h]
  refine Finset.prod_bij (fun σ _ => (σ : E →+* ℂ)) ?_ ?_ ?_ ?_
  · intro σ _
    have hxm : x ∈ IntermediateField.adjoin ℚ {x} := IntermediateField.mem_adjoin_simple_self ℚ x
    have := σ.commutes (⟨x, hxm⟩ : Kx x)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hc] at this
    exact this
  · intro σ _ τ _ hst
    exact AlgHom.coe_ringHom_injective hst
  · intro φ' hφ'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hφ'
    refine ⟨{ φ' with commutes' := fun r => ?_ }, Finset.mem_univ _, ?_⟩
    · exact eq_on_adjoin x φ' φ hφ' _ r.2
    · ext y; rfl
  · intro σ _
    rfl

private theorem conj_of_sq {z : ℂ} {d : ℕ} (hd : 0 < d) (hz : z ^ 2 = -(d : ℂ)) :
    starRingEnd ℂ z = -z := by
  have h1 : (starRingEnd ℂ z) ^ 2 = z ^ 2 := by
    rw [← map_pow, hz]; simp
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h | h
  · exfalso
    obtain ⟨r, rfl⟩ := Complex.conj_eq_iff_real.1 h
    have h2 : (r ^ 2 : ℝ) = -(d : ℝ) := by exact_mod_cast hz
    have h3 : (0 : ℝ) < d := by exact_mod_cast hd
    nlinarith [sq_nonneg r]
  · exact h

private theorem emb_conj {E : Type} [Field E] [NumberField E] [IsCMField E] (φ : E →+* ℂ) (a : E) :
    φ (conjE E a) = starRingEnd ℂ (φ a) := by
  have h : conjE E a = IsCMField.complexConj E a := rfl
  rw [h]
  exact (IsCMField.complexEmbedding_complexConj E φ a)

end UpperTheory.Gal.CertificateRingHomMap.ZetaNonvanishing₂.NormEmbeddings

open UpperTheory.Gal.CertificateRingHomMap.ZetaNonvanishing₂.NormEmbeddings in
theorem UpperTheory.Gal.CertificateRingHomMap.ZetaNonvanishing₂.normEmb :
    UpperTheory.Gal.CertificateRingHomMap.ZetaNonvanishing₂.NormEmb := by
  classical
  intro E _ _ _ d x hd hx k
  have hsq : ∀ φ : E →+* ℂ, (φ x) ^ 2 = -(d : ℂ) := fun φ => by
    rw [← map_pow, hx]; simp
  have hne : ∀ φ : E →+* ℂ, φ x ≠ 0 := fun φ h0 => by
    have h1 := hsq φ
    rw [h0] at h1
    have h2 : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
    apply h2
    simpa using h1.symm
  have hcj : ∀ φ : E →+* ℂ, φ (conjE E (algebraMap (Kx x) E (Algebra.norm (Kx x) (k : E)))) =
      ∏ φ' ∈ Finset.univ.filter (fun φ' : E →+* ℂ => φ' x = -φ x), φ' k := by
    intro φ
    have h := norm_Kx x ((starRingEnd ℂ).comp φ) (k : E)
    simp only [RingHom.comp_apply, conj_of_sq hd (hsq φ)] at h
    rw [emb_conj, h]
  have hQ : ((Algebra.norm ℚ (k : E) : ℚ) : ℂ) = ∏ φ' : E →+* ℂ, φ' k := by
    have h := Algebra.norm_eq_prod_embeddings ℚ ℂ (k : E)
    rw [eq_ratCast] at h
    rw [h]
    exact Fintype.prod_equiv (RingHom.equivRatAlgHom E ℂ).symm _ _ (fun _ => rfl)
  let φ₀ : E →+* ℂ := (IsAlgClosed.lift : E →ₐ[ℚ] ℂ).toRingHom
  have hmul : φ₀ (algebraMap (Kx x) E (Algebra.norm (Kx x) (k : E))) *
      φ₀ (conjE E (algebraMap (Kx x) E (Algebra.norm (Kx x) (k : E)))) =
      ((Algebra.norm ℚ (k : E) : ℚ) : ℂ) := by
    rw [norm_Kx x φ₀ (k : E), hcj φ₀, hQ, ← Finset.prod_filter_mul_prod_filter_not Finset.univ
      (fun φ' : E →+* ℂ => φ' x = φ₀ x)]
    congr 2
    ext φ'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have h2 : (φ' x) ^ 2 = (φ₀ x) ^ 2 := by rw [hsq, hsq]
    constructor
    · intro h h'
      rw [h] at h'
      have : (2 : ℂ) * φ₀ x = 0 := by linear_combination -h'
      exact hne φ₀ (by simpa using this)
    · intro h
      rcases sq_eq_sq_iff_eq_or_eq_neg.1 h2 with h3 | h3
      · exact absurd h3 h
      · exact h3
  refine ⟨hcj, hQ, ?_, ?_⟩
  · have ht : φ₀ (algebraMap (Kx x) E (Algebra.norm (Kx x) (k : E))) ≠ 0 := by
      haveI : FiniteDimensional (Kx x) E := FiniteDimensional.right ℚ (Kx x) E
      rw [Ne, map_eq_zero, map_eq_zero, Algebra.norm_eq_zero_iff]
      exact k.ne_zero
    rw [emb_conj, Complex.mul_conj] at hmul
    have h1 : Complex.normSq (φ₀ (algebraMap (Kx x) E (Algebra.norm (Kx x) (k : E)))) =
        ((Algebra.norm ℚ (k : E) : ℚ) : ℝ) := by exact_mod_cast hmul
    have h2 := Complex.normSq_pos.2 ht
    rw [h1] at h2
    exact_mod_cast h2
  · apply φ₀.injective
    rw [map_mul, hmul]
    simp
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.CyclotomicConjugation.NormGlob
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.L2.Host GlobalTheory.HeckeGal
open GlobalTheory.SplitPts (conjE)
open GroundTheory.Global.AdeleBaseChange (finiteAdeleMap)
open UpperTheory.Gal.CertificateRingHomMap UpperTheory.Gal.CertificateRingHomMap.ZetaNonvanishing₂

private noncomputable abbrev sn (K : Type) [Field K] [NumberField K] : GroundTheory.Global.IdeleGroup K →* (Af K)ˣ :=
  Units.map (MonoidHom.snd (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K))

private noncomputable abbrev fi (K : Type) [Field K] [NumberField K] : (Af K)ˣ →* GroundTheory.Global.IdeleGroup K :=
  Units.map (MonoidHom.inr (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K))

private theorem sn_norm (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (x : GroundTheory.Global.IdeleGroup L) :
    sn K (GroundTheory.Global.ideleNorm K L x) = fN K L (sn L x) := by
  apply Units.ext
  apply RestrictedProduct.ext
  intro v
  exact (GroundTheory.Global.ideleNorm_snd x v).trans (GroundTheory.Global.ideleNorm_snd (fi L (sn L x)) v).symm

private theorem continuous_sn (K : Type) [Field K] [NumberField K] : Continuous (sn K) :=
  Continuous.units_map _ continuous_snd

private theorem continuous_fi (K : Type) [Field K] [NumberField K] : Continuous (fi K) :=
  Continuous.units_map _ (continuous_const.prodMk continuous_id)

theorem UpperTheory.Gal.CertificateRingHomMap.ZetaNonvanishing₂.normGlob :
    UpperTheory.Gal.CertificateRingHomMap.ZetaNonvanishing₂.NormGlob := by
  intro K L _ _ _ _ _
  refine ⟨(continuous_sn K).comp (GroundTheory.Global.continuous_ideleNorm.comp (continuous_fi L)), fun k => ?_, ?_⟩
  · have h : diagF L k = sn L (GroundTheory.Global.IdeleGroup.diagonal L k) := by
      apply Units.ext
      rfl
    rw [h, ← sn_norm, GroundTheory.Global.ideleNorm_diagonal]
    rfl
  · intro M _ _ _ _ _ y
    have h := sn_norm K L (GroundTheory.Global.ideleNorm L M (fi M y))
    rw [GroundTheory.Global.ideleNorm_ideleNorm] at h
    exact h.symm
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.CyclotomicConjugation.QuadConj
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.L2.Host GlobalTheory.HeckeGal
open GlobalTheory.SplitPts (conjE)
open GroundTheory.Global.AdeleBaseChange (finiteAdeleMap)
open UpperTheory.Gal.CertificateRingHomMap UpperTheory.Gal.CertificateRingHomMap.ZetaNonvanishing₂
open scoped NumberField.AdeleRing

noncomputable section
open GroundTheory.Global GroundTheory.Global.AdeleBaseChange
open scoped Classical
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

private theorem conj_alt_bis {d : ℕ} {x : E} (hd : 0 < d) (hx : x ^ 2 = -(d : E)) : conjE E x = -x :=
  _root_.UpperTheory.Reformulated.B.CMConjugationOfSqrtNeg.conj_alt_bis hd hx

private theorem conj_conj' (a : E) : conjE E (conjE E a) = a := IsCMField.complexConj_apply_apply E a

private theorem conj_mem {d : ℕ} {x : E} (hd : 0 < d) (hx : x ^ 2 = -(d : E)) (a : E)
    (ha : a ∈ IntermediateField.adjoin ℚ {x}) : conjE E a ∈ IntermediateField.adjoin ℚ {x} := by
  induction ha using IntermediateField.adjoin_induction with
  | mem a h =>
    rw [Set.mem_singleton_iff.1 h, conj_alt_bis hd hx]
    exact neg_mem (IntermediateField.mem_adjoin_simple_self ℚ x)
  | algebraMap q =>
    have : conjE E (algebraMap ℚ E q) = algebraMap ℚ E q := by simp
    rw [this]
    exact IntermediateField.algebraMap_mem _ q
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | inv a _ ha => rw [map_inv₀]; exact inv_mem ha
  | mul a b _ _ ha hb => rw [map_mul]; exact mul_mem ha hb

private def cK {d : ℕ} {x : E} (hd : 0 < d) (hx : x ^ 2 = -(d : E)) : Kx x ≃ₐ[ℚ] Kx x :=
  let c0 : Kx x →ₐ[ℚ] Kx x :=
    { toFun := fun a => ⟨conjE E a, conj_mem hd hx a a.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun a b => Subtype.ext (by simp)
      commutes' := fun q => Subtype.ext (by
        change conjE E ((algebraMap ℚ (Kx x) q : Kx x) : E) = ((algebraMap ℚ (Kx x) q : Kx x) : E)
        simp) }
  AlgEquiv.ofAlgHom c0 c0 (AlgHom.ext fun a => Subtype.ext (conj_conj' _))
    (AlgHom.ext fun a => Subtype.ext (conj_conj' _))

private theorem cK_coe {d : ℕ} {x : E} (hd : 0 < d) (hx : x ^ 2 = -(d : E)) (a : Kx x) :
    ((cK hd hx a : Kx x) : E) = conjE E a := rfl

private theorem aut_cases {d : ℕ} {x : E} (hd : 0 < d) (hx : x ^ 2 = -(d : E)) (σ : Kx x ≃ₐ[ℚ] Kx x) :
    σ = 1 ∨ σ = cK hd hx := by
  have hmem : x ∈ IntermediateField.adjoin ℚ {x} := IntermediateField.mem_adjoin_simple_self ℚ x
  let xk : Kx x := ⟨x, hmem⟩
  have hxk : xk ^ 2 = algebraMap ℚ (Kx x) (-(d : ℚ)) := Subtype.ext (by
    change x ^ 2 = algebraMap ℚ E (-(d : ℚ))
    rw [hx]; simp)
  have hsq : (σ xk) ^ 2 = xk ^ 2 := by rw [← map_pow, hxk, AlgEquiv.commutes]
  have ext' : ∀ τ : Kx x ≃ₐ[ℚ] Kx x, σ xk = τ xk → σ = τ := fun τ h => by
    have : (σ : Kx x →ₐ[ℚ] Kx x) = (τ : Kx x →ₐ[ℚ] Kx x) := IntermediateField.adjoin_algHom_ext ℚ (by
      intro a ha
      obtain rfl : a = x := Set.mem_singleton_iff.1 ha
      exact h)
    exact AlgEquiv.coe_toAlgHom_injective this
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq with h | h
  · exact Or.inl (ext' 1 h)
  · refine Or.inr (ext' _ (h.trans (Subtype.ext ?_)))
    change -x = conjE E x
    rw [conj_alt_bis hd hx]

private theorem cK_ne {d : ℕ} {x : E} (hd : 0 < d) (hx : x ^ 2 = -(d : E)) : cK hd hx ≠ 1 := by
  intro h
  have hmem : x ∈ IntermediateField.adjoin ℚ {x} := IntermediateField.mem_adjoin_simple_self ℚ x
  have h1 : conjE E x = x := congrArg (fun σ : Kx x ≃ₐ[ℚ] Kx x => ((σ ⟨x, hmem⟩ : Kx x) : E)) h
  rw [conj_alt_bis hd hx] at h1
  have h0 : x = 0 := by
    have : (2 : E) * x = 0 := by linear_combination -h1
    simpa using this
  rw [h0] at hx
  have : (d : E) = 0 := by simpa using hx.symm
  exact hd.ne' (by exact_mod_cast this)

private theorem finrank_K {d : ℕ} {x : E} (hd : 0 < d) (hx : x ^ 2 = -(d : E)) :
    Module.finrank ℚ (Kx x) = 2 := by
  have hint : IsIntegral ℚ x := Algebra.IsIntegral.isIntegral x
  have hmonic : (Polynomial.X ^ 2 + Polynomial.C (d : ℚ)).Monic := Polynomial.monic_X_pow_add_C _ (by norm_num)
  have hdeg : (Polynomial.X ^ 2 + Polynomial.C (d : ℚ)).natDegree = 2 := Polynomial.natDegree_X_pow_add_C
  have hirr : Irreducible (Polynomial.X ^ 2 + Polynomial.C (d : ℚ)) := by
    refine Polynomial.irreducible_of_degree_le_three_of_not_isRoot (by rw [hdeg]; simp) fun q hq => ?_
    have hd' : (0 : ℚ) < d := by exact_mod_cast hd
    simp only [Polynomial.IsRoot, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C] at hq
    nlinarith [sq_nonneg q]
  have hmin : Polynomial.X ^ 2 + Polynomial.C (d : ℚ) = minpoly ℚ x :=
    minpoly.eq_of_irreducible_of_monic hirr (by simp [hx]) hmonic
  have := IntermediateField.adjoin.finrank hint
  rw [← hmin, hdeg] at this
  exact this

private theorem univ_eq {d : ℕ} {x : E} (hd : 0 < d) (hx : x ^ 2 = -(d : E)) :
    (Finset.univ : Finset (Kx x ≃ₐ[ℚ] Kx x)) = {1, cK hd hx} := by
  ext σ
  simpa using aut_cases hd hx σ

private theorem isGalois_K {d : ℕ} {x : E} (hd : 0 < d) (hx : x ^ 2 = -(d : E)) : IsGalois ℚ (Kx x) := by
  refine IsGalois.of_card_aut_eq_finrank ℚ (Kx x) ?_
  rw [finrank_K hd hx, Nat.card_eq_fintype_card, ← Finset.card_univ, univ_eq hd hx, Finset.card_pair (cK_ne hd hx).symm]

private theorem conjFin_rat (a : Af ℚ) : conjFin (conjE E) (finiteAdeleMap ℚ E a) = finiteAdeleMap ℚ E a := by
  have h := (GroundTheory.Automorphic.AdelicGLn.denseRange_algebraMap_finiteAdeleRing ℚ).equalizer
    ((continuous_conjFin (conjE E)).comp continuous_finiteAdeleMap)
    (continuous_finiteAdeleMap (K := ℚ) (L := E)) (funext fun q => ?_)
  · exact congrFun h a
  · simp only [Function.comp_apply]
    rw [finiteAdeleMap_algebraMap, conjFin_algebraMap]
    simp

private theorem fin_conj {d : ℕ} {x : E} (hd : 0 < d) (hx : x ^ 2 = -(d : E)) (y : 𝔸[Kx x]) :
    finiteAdeleMap (Kx x) E ((cK hd hx • y).2) = conjFin (conjE E) (finiteAdeleMap (Kx x) E y.2) := by
  let Φ : 𝔸[Kx x] →+* Af E := (finiteAdeleMap (Kx x) E).comp
    ((RingHom.snd _ _).comp (adeleRingEquiv ((cK hd hx : Kx x ≃ₐ[ℚ] Kx x) : Kx x ≃+* Kx x)).toRingHom)
  let Ψ : 𝔸[Kx x] →+* Af E := ((conjFin (conjE E)).comp (finiteAdeleMap (Kx x) E)).comp (RingHom.snd _ _)
  have h : Φ = Ψ := by
    refine adeleRingHom_ext_rat (fun l => ?_) (fun a => ?_)
    · change finiteAdeleMap (Kx x) E ((adeleRingEquiv ((cK hd hx : Kx x ≃ₐ[ℚ] Kx x) : Kx x ≃+* Kx x) (algebraMap (Kx x) 𝔸[Kx x] l)).2) =
        conjFin (conjE E) (finiteAdeleMap (Kx x) E ((algebraMap (Kx x) 𝔸[Kx x] l).2))
      rw [adeleRingEquiv_algebraMap]
      change finiteAdeleMap (Kx x) E (algebraMap (Kx x) (FiniteAdeleRing (𝓞 (Kx x)) (Kx x)) _) =
        conjFin (conjE E) (finiteAdeleMap (Kx x) E (algebraMap (Kx x) (FiniteAdeleRing (𝓞 (Kx x)) (Kx x)) l))
      rw [finiteAdeleMap_algebraMap, finiteAdeleMap_algebraMap, conjFin_algebraMap]
      rfl
    · change finiteAdeleMap (Kx x) E ((adeleRingEquiv ((cK hd hx : Kx x ≃ₐ[ℚ] Kx x) : Kx x ≃+* Kx x) (adeleMap ℚ (Kx x) a)).2) =
        conjFin (conjE E) (finiteAdeleMap (Kx x) E ((adeleMap ℚ (Kx x) a).2))
      rw [adeleRingEquiv_adeleMap_rat]
      change finiteAdeleMap (Kx x) E (finiteAdeleMap ℚ (Kx x) a.2) =
        conjFin (conjE E) (finiteAdeleMap (Kx x) E (finiteAdeleMap ℚ (Kx x) a.2))
      rw [finiteAdeleMap_finiteAdeleMap, conjFin_rat]
  exact congrArg (· y) h

theorem UpperTheory.Gal.CertificateRingHomMap.ZetaNonvanishing₂.quadConj :
    UpperTheory.Gal.CertificateRingHomMap.ZetaNonvanishing₂.QuadConj := by
  intro E _ _ _ d x hd hx z
  haveI := isGalois_K hd hx
  let y : IdeleGroup (Kx x) := Units.map (MonoidHom.inr (InfiniteAdeleRing (Kx x)) (FiniteAdeleRing (𝓞 (Kx x)) (Kx x))) z
  have h1 := ideleEmbedding_ideleNorm (K := ℚ) y
  have h2 : (∏ σ : Kx x ≃ₐ[ℚ] Kx x, σ • y) = y * cK hd hx • y := by
    rw [univ_eq hd hx, Finset.prod_pair (cK_ne hd hx).symm, one_smul]
  rw [h2] at h1
  have h3 := congrArg (fun u : IdeleGroup (Kx x) => ((u : 𝔸[Kx x]).2)) h1
  have h4 : finiteAdeleMap ℚ (Kx x) ((fN ℚ (Kx x) z : (Af ℚ)ˣ) : Af ℚ) =
      (z : Af (Kx x)) * ((cK hd hx • (y : 𝔸[Kx x])).2) := h3
  have h5 := congrArg (finiteAdeleMap (Kx x) E) h4
  rw [finiteAdeleMap_finiteAdeleMap, map_mul, fin_conj] at h5
  exact h5.symm

end
end

