module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0385
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAuxiliaryPrimesPrescribedFrobenius
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0696
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1135
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0244
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0159
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0264
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0061
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0695
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0094
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0095
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsDualDualRep
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CocycleFormsSpanOddResidueChar
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanTwoOfGaloisHypothesis
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidualSelmerFinrankEqDual
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FirstHalfLocalCohomologyVanishingOfLocalDualityT
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ReciprocityAuxiliaryPlacesSecondHalf
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0427
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsElementsSelmerFormsSmallCorank

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNewPlaceFrobeniusConjugateModOpenNormalSub
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate
open GlobalTheory.ChosenPrimes

namespace GlobalTheory.NewPrimePick

theorem exists_newPlace : Cheb → ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (i : X.Tw) (s : X.Sig i), ∀ (M R n : ℕ) (d : PlE D.host → (GE N →* Multiplicative (ZMod (X.l i ^ M)))) (A₀ : Finset (PlE D.host)) (L : Subgroup (GE N)) (z : GE N) (P : Fin R ⊕ Fin n → PlE D.host), 1 ≤ M → IsTameInertiaElementAtTwistPrime X i z → Small2 i s M L z → PiLocalization₂ i M d A₀ L z P → n < R → ∀ (H : Subgroup (GE N)) (S : Finset (PlE D.host)), AdmFam X i M H S d → L ≤ H → ∀ (U : Subgroup (GE N)) (h : GE N), IsOpen (U : Set (GE N)) → U.Normal → U ≤ L → h ∈ L → (∀ b : Fin R, b.val < n → d (P (.inl b)) h = 1) → (∀ b : Fin R, n ≤ b.val → Ine (F := D.host.E) (N.plOm.1 (P (.inl b))) ≤ U) → ∃ P' : Fin R ⊕ Fin (n + 1) → PlE D.host, Ext P P' ∧ PiLocalization₂ i M d A₀ L z P' ∧ ∃ σ γ g : GE N, NewPl i M L (P' (.inr (Fin.last n))) (d (P' (.inr (Fin.last n)))) σ γ ∧ d (P' (.inr (Fin.last n))) σ = 1 ∧ g * σ * g⁻¹ * h⁻¹ ∈ U := by
  intro hC D N X i s M R n d A L z P _ _ hsm hst _ H S hA hLH U h hU hUn hUL hh hh1 hIU
  classical
  obtain ⟨-, -, -, hd⟩ := hA
  obtain ⟨⟨hL, hLn, -⟩, hLr, -⟩ := hsm
  obtain ⟨⟨ha1, ha2, ha3⟩, hs1, hs2⟩ := hst
  have hl := (X.lPrime i).out
  set m := 2 * X.l i ^ M with hm
  have hn1 : 1 < m := by have := Nat.pow_pos (n := M) hl.pos; omega
  have hn0 : m ≠ 0 := by omega
  have hval := exists_values (U ⊓ ⨅ b : {b : Fin R // b.val < n}, (d (P (.inl b.1))).ker)
    (fun b : {b : Fin R // n ≤ b.val} => d (P (.inl b.1))) (fun b c => by
      obtain ⟨γ, hγ, e⟩ := (ha3 (.inl b.1)).2.2.2.2 _ (over_refl _) _ (N.plOm.2 (P (.inl b.1))) c
      have key : ∀ b' : Fin R, b' ≠ b.1 → d (P (.inl b')) γ = 1 := fun b' hb' =>
        (ha3 (.inl b')).2.2.2.1 _ (fun h => hb' (Sum.inl_injective (ha2 _ _ h))) _ (N.plOm.2 (P (.inl b.1))) γ hγ
      refine ⟨γ, ⟨hIU b.1 b.2 hγ, Subgroup.mem_iInf.2 fun b' => key b'.1 fun h => ?_⟩, e,
        fun b' hb' => key b'.1 fun h => hb' (Subtype.ext h)⟩
      have h1 := b'.2
      have h2 := b.2
      rw [h] at h1
      omega)
  obtain ⟨γ₀, hγ₀, hγd⟩ := hval fun b =>
    Multiplicative.ofAdd (if n = b.1.val then 1 else 0) * (d (P (.inl b.1)) h)⁻¹
  have hγh : ∀ b : Fin R, d (P (.inl b)) (γ₀ * h) = Multiplicative.ofAdd (if n = b.val then 1 else 0) := by
    intro b
    rw [map_mul]
    rcases lt_or_ge b.val n with hb | hb
    · have h1 : d (P (.inl b)) γ₀ = 1 := Subgroup.mem_iInf.1 hγ₀.2 ⟨b, hb⟩
      rw [h1, hh1 b hb, if_neg (by omega), mul_one]
      rfl
    · rw [hγd ⟨b, hb⟩, inv_mul_cancel_right]
  let V : Subgroup (GE N) := U ⊓ ⨅ b, (d (P (.inl b))).ker
  have hV : IsOpen (V : Set (GE N)) := by
    refine hU.inter ?_
    show IsOpen ((⨅ b, (d (P (.inl b))).ker : Subgroup (GE N)) : Set (GE N))
    rw [Subgroup.coe_iInf]
    exact isOpen_iInter_of_finite fun b => (ha3 (.inl b)).1
  have hVn : V.Normal := by
    have : (⨅ b, (d (P (.inl b))).ker).Normal := Subgroup.normal_iInf_normal fun b => inferInstance
    infer_instance
  obtain ⟨T₀, hT₀, hsp⟩ := GlobalTheory.FrobDense.exists_finite_split D.host
  let T : Set (PlE D.host) := ((↑A ∪ ↑S ∪ ↑(X.S0 i)) ∪ (T₀ ∪ {P | P.asIdeal.ramificationIdx ℤ ≠ 1}) ∪
    ({v | ((m : ℕ) : 𝓞 D.host.E) ∈ v.asIdeal} ∪
      {v | ∃ B : ValuationSubring N.Om, IsPlaceOver B v ∧ ¬ Ine (F := D.host.E) B ≤ U})) ∪ Set.range P
  have hT : T.Finite :=
    ((((A.finite_toSet.union S.finite_toSet).union (X.S0 i).finite_toSet).union
      (hT₀.union (GlobalTheory.absNorm_prime_iff_inertiaDeg_eq_one_and_finite_ramified D.host.E).2)).union
      ((finite_mem hn0).union (finite_ram hU))).union (Set.finite_range P)
  obtain ⟨p, hp⟩ := exists_pick hC hV hVn (γ₀ * h) hT
  have h1 : ∀ v, Over p v → ((((v ∉ A ∧ v ∉ S) ∧ v ∉ X.S0 i) ∧ v ∉ T₀ ∧ v.asIdeal.ramificationIdx ℤ = 1) ∧
      ((m : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal ∧
      ∀ B : ValuationSubring N.Om, IsPlaceOver B v → Ine (F := D.host.E) B ≤ U) ∧ v ∉ Set.range P := fun v hv => by
    have : v ∉ T := (hp.1 v hv).1
    simpa only [T, Set.mem_union, not_or, Finset.mem_coe, Set.mem_ofPred_eq, not_exists, not_and, not_not] using this
  obtain ⟨σ, hσ⟩ := exists_isFrob (N.plOm.2 p)
  obtain ⟨k, hk⟩ := hp.2 σ hσ
  have hσL : σ ∈ L := by
    have h2 := hLn.conj_mem _ (L.mul_mem (hUL hk.1) (L.mul_mem (hUL hγ₀.1) hh)) k⁻¹
    have e : k⁻¹ * (k * σ * k⁻¹ * (γ₀ * h)⁻¹ * (γ₀ * h)) * k⁻¹⁻¹ = σ := by group
    rwa [e] at h2
  have hP0 := h1 p (over_refl p)
  have hq := norm_mod (N.plOm.2 p) hn1 hP0.1.2.1 hσ (hLr σ hσL)
  have hIp : Ine (F := D.host.E) (N.plOm.1 p) ≤ U := hP0.1.2.2 _ (N.plOm.2 p)
  have hdec : DecV N p ≤ L := dec_le (N.plOm.2 p) hL (hIp.trans hUL) hσ hσL
  have hspl : IsSplitPl D.host p := hsp p hP0.1.1.2.1 (hp.1 p (over_refl p)).2
  have hgood : GoodChar X i M p (d p) := hd p hP0.1.1.1.1.2 hspl (hdec.trans hLH)
  have haux : ∀ v, Over p v → IsSplitPl D.host v ∧ v.asIdeal.inertiaDeg ℤ = 1 ∧ Formalism.BasicNotions.eWL D.host.E v = 1 ∧
      v ∉ X.S0 i ∧ v ∉ A ∧ normV v % m = 1 := by
    refine fun v hv => ⟨hsp v (h1 v hv).1.1.2.1 (hp.1 v hv).2, (hp.1 v hv).2, (h1 v hv).1.1.2.2, (h1 v hv).1.1.1.2,
      (h1 v hv).1.1.1.1.1, ?_⟩
    rcases hv with rfl | hv
    · exact hq
    · rwa [normV_conj hv]
  let P' : Fin R ⊕ Fin (n + 1) → PlE D.host :=
    Sum.elim (fun a => P (.inl a)) (Fin.snoc (α := fun _ => PlE D.host) (fun a => P (.inr a)) p)
  have e1 : P' (.inr (Fin.last n)) = p := by simp [P']
  have e2 : ∀ q, P' (Sum.map id Fin.castSucc q) = P q := by
    rintro (a | a) <;> simp [P']
  have cases : ∀ q : Fin R ⊕ Fin (n + 1), q = .inr (Fin.last n) ∨ ∃ q₀, q = Sum.map id Fin.castSucc q₀ := by
    rintro (a | a)
    · exact Or.inr ⟨.inl a, rfl⟩
    · refine Fin.lastCases (Or.inl rfl) (fun a => Or.inr ⟨.inr a, rfl⟩) a
  refine ⟨P', e2, ⟨⟨fun q => ?_, fun q q' => ?_, fun q => ?_⟩, hs1, fun a => ?_⟩, ?_⟩
  · rcases cases q with rfl | ⟨q, rfl⟩
    · rw [e1]; exact haux
    · rw [e2]; exact ha1 q
  · rcases cases q with rfl | ⟨q, rfl⟩ <;> rcases cases q' with rfl | ⟨q', rfl⟩
    · exact fun _ => rfl
    · rw [e1, e2]; exact fun h => ((h1 _ h).2 ⟨q', rfl⟩).elim
    · rw [e1, e2]; exact fun h => ((h1 _ (over_symm h)).2 ⟨q, rfl⟩).elim
    · rw [e2, e2]; exact fun h => by rw [ha2 _ _ h]
  · show GoodChar X i M (P' q) (d (P' q))
    rcases cases q with rfl | ⟨q, rfl⟩
    · rw [e1]; exact hgood
    · rw [e2]; exact ha3 q
  · refine Fin.lastCases ?_ (fun a => ?_) a
    · rw [e1]
      refine ⟨hdec, fun b τ hτ => ?_⟩
      obtain ⟨k', hk'⟩ := hp.2 τ hτ
      have h2 : d (P (.inl b)) _ = 1 := Subgroup.mem_iInf.1 hk'.2 b
      rw [map_mul, map_inv, hγh] at h2
      simp only [map_mul, map_inv, mul_inv_cancel_comm, mul_inv_eq_one] at h2
      exact h2
    · have e3 : P' (.inr a.castSucc) = P (.inr a) := e2 (.inr a)
      rw [e3]
      exact hs2 a
  · rw [e1]
    obtain ⟨γ, hγ, hγ1⟩ := hgood.2.2.2.2 p (over_refl p) _ (N.plOm.2 p) (Multiplicative.ofAdd 1)
    obtain ⟨τ, hτ, hτ1⟩ := hgood.2.2.2.2 p (over_refl p) _ (N.plOm.2 p) (d p σ)⁻¹
    refine ⟨σ * τ, γ, k, ⟨fun v hv => (haux v hv).2.2.2.1, hspl, hq, hdec, hgood.1, ?_, hγ, hγ1⟩, ?_, ?_⟩
    · first | exact isFrob_mul_of_mem_Ine hσ hτ | exact isFrob_mul_of_mem_Ine hτ hσ
    · rw [map_mul, hτ1, mul_inv_cancel]
    · have h2 := U.mul_mem (U.mul_mem (hUn.conj_mem _ (hIp hτ) (k * σ)) hk.1) hγ₀.1
      have e : k * σ * τ * (k * σ)⁻¹ * (k * σ * k⁻¹ * (γ₀ * h)⁻¹) * γ₀ = k * (σ * τ) * k⁻¹ * h⁻¹ := by group
      rwa [e] at h2

end GlobalTheory.NewPrimePick
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSmoothWhittakerBumpAdelicGL
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology


open NumberField IsDedekindDomain GlobalTheory.CuspRep Matrix MeasureTheory GlobalTheory.WhitBump in
theorem GlobalTheory.WhitBump.exists_bump_glob : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), ∃ b : GA E (a + 1) → ℂ, b 1 = 1 ∧ (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (a + 1)), ∀ g, b (u * g) = GlobalTheory.JSW.psiN u * b g) ∧ (∃ C : Set (GA E (a + 1)), IsCompact C ∧ ∀ p, b p ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (a + 1)), u⁻¹ * p ∈ C) ∧ (∃ U : Subgroup (GL (Fin (a + 1)) (Af E)), IsOpen (U : Set (GL (Fin (a + 1)) (Af E))) ∧ ∀ u ∈ U, ∀ g, b (g * finGL E (a + 1) u) = b g) ∧ ∀ g, ContDiffOn ℝ ∞ (chart b g) (invSet E (a + 1)) := by
  intro E _ _ _ m
  obtain ⟨f, hf, hfc, hfs, hf1⟩ := exists_bumpInf_ne (E := E) (n := m + 1)
  obtain ⟨h1, hN, hK, hsupp⟩ := bumpFin_spec (E := E) (n := m + 1) fun u hu hk => psiFin_integral u hu hk
  set c := bumpInf f (oneL E (m + 1)) with hc
  let pI : GA E (m + 1) → GL (Fin (m + 1)) (Cinf E) := fun g => GeneralLinearGroup.map (pInf E) g
  let pF : GA E (m + 1) → GL (Fin (m + 1)) (Af E) := fun g => GeneralLinearGroup.map (pFin E) g
  refine ⟨fun g => bumpInf f (toL (pI g : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E))) / c * bumpFin (pF g),
    ?_, ?_, ?_, ?_, ?_⟩
  · simp only [pI, pF, map_one, Units.val_one, h1, mul_one]
    exact div_self hf1
  · intro u hu g
    simp only [pI, pF, map_mul, Units.val_mul]
    have e := bumpInf_mul f _ (pInf_mem_unipB hu) (toL ((GeneralLinearGroup.map (pInf E) g : GL (Fin (m + 1)) (Cinf E)) : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E)))
    erw [e]
    rw [hN _ (pFin_mem_unipB hu), psiN_eq]
    ring
  · let T := tsupport f
    let C : Set (GA E (m + 1)) := (fun q : GL (Fin (m + 1)) (Cinf E) × GL (Fin (m + 1)) (Af E) =>
      infGL E (m + 1) q.1 * finGL E (m + 1) q.2) ''
        ({y : GL (Fin (m + 1)) (Cinf E) | toL (y : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E)) ∈ T} ×ˢ
          (GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E (m + 1) : Set (GL (Fin (m + 1)) (Af E))))
    refine ⟨C, ?_, ?_⟩
    · refine ((isCompact_setOf_toL T hfc hfs).prod
        (GroundTheory.Automorphic.AdelicGLn.isCompact_integralFiniteGL E (m + 1))).image ?_
      exact ((GlobalTheory.ConstTermSmooth.continuous_infGL).comp continuous_fst).mul
        (continuous_finGL_bump.comp continuous_snd)
    · intro p hp
      have hI : bumpInf f (toL (pI p : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E))) ≠ 0 := by
        intro h; apply hp; simp only [h, zero_div, zero_mul]
      have hF : bumpFin (pF p) ≠ 0 := by
        intro h; apply hp; simp only [h, mul_zero]
      obtain ⟨t, ht⟩ : ∃ t, f (toL (nu t * Matrix.of (toL (pI p : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E))))) ≠ 0 := by
        by_contra hall
        push_neg at hall
        have hall' : ∀ t, f (toL (nu t * (pI p : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E)))) = 0 := hall
        apply hI
        unfold bumpInf
        simp [hall']
      obtain ⟨uf, huf, hk⟩ := hsupp _ hF
      refine ⟨infGL E (m + 1) (nuGL t)⁻¹ * finGL E (m + 1) uf,
        mem_NA_of (inv_mem (nuGL_mem t)) huf, ⟨(nuGL t * pI p, uf⁻¹ * pF p), ⟨?_, hk⟩, ?_⟩⟩
      · exact subset_tsupport f ht
      · refine ga_ext ?_ ?_ <;> simp [pI, pF]
  · refine ⟨GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E (m + 1),
      GroundTheory.Automorphic.AdelicGLn.isOpen_integralFiniteGL E (m + 1), fun k hk g => ?_⟩
    simp only [pI, pF, map_mul, pInf_finGL, pFin_finGL, mul_one]
    rw [hK k hk]
  · intro g
    have hsm := contDiffOn_bumpInf f hf hfc hfs
    set L := lmul (toL (pI g : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E))) with hL
    have hmaps : Set.MapsTo L (invSet E (m + 1)) (invSet E (m + 1)) := fun x hx => by
      have hx' : IsUnit (Matrix.of x) := hx
      change IsUnit ((pI g : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E)) * Matrix.of x)
      exact (pI g).isUnit.mul hx'
    have h2 : ContDiffOn ℝ ∞ (fun x : Lie E (m + 1) => bumpInf f (L x)) (invSet E (m + 1)) :=
      hsm.comp (L.contDiff.contDiffOn) hmaps
    have hl : ContDiffOn ℝ ∞ (fun x : Lie E (m + 1) => bumpInf f (L x) / c * bumpFin (pF g))
        (invSet E (m + 1)) := (h2.div_const c).mul contDiffOn_const
    refine hl.congr fun x hx => ?_
    have hx' : IsUnit (Matrix.of x) := hx
    rw [chart, dite_eq_left hx']
    simp only [pI, pF, map_mul, pInf_infGL, pFin_infGL, mul_one, Units.val_mul, IsUnit.unit_spec]
    rfl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FirstCharacterTrivialWildInertiaTypePrime
section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.ChiTame

theorem main : ∀ (D : D7) (i : D.nd.Loc) (k : Fin 2) (v : D.nd.PlG k), D.nd.l i ≠ D.host.g k → ∀ s ∈ wildSet D.nd (D.nd.plOm.1 (D.naut.plGw k v)), D.nd.chi i 1 s = 1 := by
  intro D i k v hne s hs
  have hwg : D.naut.plGw k v ∈ placesOver D.host.E (D.host.g k) := D.naut.plGw_over k v
  have hpl := D.nd.plOm.2 (D.naut.plGw k v)
  have hI : s ∈ Ine (F := D.host.E) (D.nd.plOm.1 (D.naut.plGw k v)) := GlobalTheory.TameGenPowers.wild_mem_Ine hs
  have hcop : (D.nd.l i).Coprime (D.host.g k) :=
    (Nat.coprime_primes (D.nd.lPrime i).out (D.host.g_prime k)).2 hne
  have hgv : (D.nd.plOm.1 (D.naut.plGw k v)).valuation ((D.host.g k : ℕ) : D.nd.Om) < 1 := by
    have h2 := (hpl _).2 hwg
    simpa using h2
  have hvl : D.naut.plGw k v ∉ placesOver D.host.E (D.nd.l i) := by
    intro hl
    have h2 := (hpl _).2 hl
    exact GlobalTheory.WildKill.not_lt_one_of_coprime _ hcop hgv (by simpa using h2)
  have hl : D.ntw.l (D.ntw.twOf i) = D.nd.l i := D.ntw.twOf_l i
  have ht := D.ntw.twistCharacterFamily_tame (D.ntw.twOf i) (D.nd.j i) (D.ntw.twSide i) k _ hwg (by rw [hl]; exact hvl)
    _ hpl s hI
  obtain ⟨n, hn⟩ := D.ntw.psiL_ord i s
  have h1 : ((Units.map (D.ntw.twist₂ i).toMonoidHom).comp
      (D.ntw.chi1 (D.ntw.twOf i) (D.nd.j i) (D.ntw.twSide i))) s ^ (D.host.g k - 1) = 1 := by
    rw [MonoidHom.comp_apply, ← map_pow, ht, map_one]
  have hpow : D.nd.chi i 1 s ^ ((D.host.g k - 1) * D.nd.l i ^ n) = 1 := by
    rw [D.ntw.chi_tw i, MonoidHom.mul_apply, mul_pow, pow_mul, h1, one_pow, one_mul, pow_mul', hn, one_pow]
  have := D.nd.trO i
  exact GlobalTheory.WildSetSQ.char_eq_one_of_wild (D.nd.plOm.1 (D.naut.plGw k v)) (D.nd.O_adic i) (D.nd.chi i 1)
    (D.nd.chi_cont i 1) s hs _
    (GlobalTheory.WildKill.not_lt_one_of_coprime _
      (Nat.Coprime.mul_left (GlobalTheory.WildSetSQ.coprime_pred _ (D.host.g_prime k).one_lt.le)
        (Nat.Coprime.pow_left n hcop)) hgv) hpow

end GlobalTheory.ChiTame
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeisenbergRealPointFockVacuumPairingScalar
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor

noncomputable section

namespace GlobalTheory.RealVacScalar

variable {D : D7}

theorem sum_wAt_real {S T : HSp D} (w : WO S T) (hw : w.map (finPart D) = 0) :
    ∑ τ : D.what₂.Tau, wAt (.inr τ) w = w := by
  ext i j
  rw [Matrix.sum_apply]
  show ∑ τ : D.what₂.Tau, idem D (.inr τ) * w i j = w i j
  rw [← Finset.sum_mul]
  refine GlobalTheory.SplitScalar.adele_ext ?_ ?_
  · rw [RingHom.map_mul, (_root_.GlobalTheory.PlaceTensor.idem_spec D).2.2.2.2.2.1, one_mul]
  · have h0 : finPart D (w i j) = 0 := congrFun (congrFun hw i) j
    rw [RingHom.map_mul, h0, mul_zero]

theorem wAt_sum_real_notMem {S T : HSp D} (w : WO S T) {r : D.what₂.Tau} {P : Finset D.what₂.Tau} (hr : r ∉ P) :
    wAt (.inr r) (∑ τ ∈ P, wAt (.inr τ) w) = 0 := by
  rw [wAt_eq_smul, Finset.smul_sum]
  refine Finset.sum_eq_zero fun τ hτ => ?_
  rw [← wAt_eq_smul]
  exact GlobalTheory.PlaceStable.wAt_wAt_ne (fun h => hr (by rw [Sum.inr_injective h]; exact hτ)) w

theorem thetaIP_eq_ipO {S T : HSp D} (μ : Measure (WO S T)) (𝓕 : Set (WO S T)) (a b : WO S T → ℂ) :
    thetaIP μ 𝓕 a b = ipO μ 𝓕 b a := by
  unfold thetaIP ipO
  congr 1
  funext x
  rw [Complex.star_def, mul_comm]

theorem ipO_conj {S T : HSp D} (μ : Measure (WO S T)) (𝓕 : Set (WO S T)) (a b : WO S T → ℂ) :
    ipO μ 𝓕 a b = starRingEnd ℂ (ipO μ 𝓕 b a) := by
  unfold ipO
  rw [← integral_conj]
  congr 1
  funext x
  simp [mul_comm]

theorem ip_sum {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
    {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)) (w : WO S T)
    (γ : D.what₂.Tau → ℂ)
    (hγ : ∀ τ (f g : WO S T → ℂ), IsThetaFunO ψ S T f → IsThetaFunO ψ S T g →
      IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f → IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) g →
      ipO μ 𝓕 g (heisO ψ S T (wAt (.inr τ) w) f) = γ τ * ipO μ 𝓕 g f)
    (P : Finset D.what₂.Tau) : ∀ f g : WO S T → ℂ, IsThetaFunO ψ S T f → IsThetaFunO ψ S T g →
      (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f) →
      (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) g) →
      ipO μ 𝓕 g (heisO ψ S T (∑ τ ∈ P, wAt (.inr τ) w) f) = (∏ τ ∈ P, γ τ) * ipO μ 𝓕 g f := by
  classical
  induction P using Finset.induction_on with
  | empty =>
    intro f g _ _ _ _
    rw [Finset.sum_empty, Finset.prod_empty, GlobalTheory.SplitScalar.heisO_zero, one_mul]
  | insert r P hr ih =>
    intro f g hf hg vf vg
    have h0 := wAt_sum_real_notMem w hr
    rw [Finset.sum_insert hr, Finset.prod_insert hr,
      GlobalTheory.SplitScalar.heisO_add_of_orth ψ S T (GlobalTheory.LocalPure.symplO_wAt S T w h0),
      hγ r _ g ((GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T).1 _ _ hf) hg
        (GlobalTheory.PlaceStable.isFockVacAt_heisO hθ h0 (vf r)) (vg r),
      ih f g hf hg vf vg, mul_assoc]

theorem compress_real : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D), IsStdChar D ψ (-1) →
    IsInfFam θ → ∀ (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ),
    (∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) →
    ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 →
    ∀ w : WO S T, w.map (finPart D) = 0 → ∃ κ : ℂ, ∀ h e : WO S T → ℂ, IsThetaFunO ψ S T h → IsThetaFunO ψ S T e →
    (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) h) →
    (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) e) →
    thetaIP μ 𝓕 h (heisO ψ S T w e) = κ * thetaIP μ 𝓕 h e := by
  intro D ψ θ S T hψ hθ sS sT hsS hsT μ 𝓕 hμ w hw
  choose γ hγ using fun τ =>
    GlobalTheory.VacCompress.compress D ψ θ S T μ 𝓕 hψ hθ hμ τ (sS τ) (sT τ) (hsS τ) (hsT τ) w
  refine ⟨starRingEnd ℂ (∏ τ, γ τ), fun h e hh he vh ve => ?_⟩
  have key := ip_sum hψ hθ μ 𝓕 w γ hγ Finset.univ e h he hh ve vh
  rw [sum_wAt_real w hw] at key
  rw [thetaIP_eq_ipO, thetaIP_eq_ipO, ipO_conj, key, map_mul, ← ipO_conj]

end GlobalTheory.RealVacScalar

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCSDOfIsEtaT
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial Formalism.L2.Host GlobalTheory.Pst GlobalTheory.GalOfCusp GlobalTheory.TripleLocal GlobalTheory.TypeLeaf

namespace GlobalTheory.EtaSelfDual

theorem ordF_unif {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) : ordF w (unif w) = 1 := by
  have h := unif_spec w
  have h1 : Valued.v ((atFin w (unif w) : (w.adicCompletion K)ˣ) : w.adicCompletion K) = w.valuation K (unif w : K) :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w (unif w : K)
  have h0 : w.valuation K (unif w : K) ≠ 0 := (Valuation.ne_zero_iff _).2 (unif w).ne_zero
  unfold IsUnifAt at h
  rw [h1, ← WithZero.exp_log h0, WithZero.exp_inj] at h
  unfold ordF
  omega

theorem ordF_conj {R : Ranks} (H : Formalism.BasicNotions.Host R) {w w' : HeightOneSpectrum (𝓞 H.E)} (h : IsConjPl H w w') (k : H.Eˣ) :
    ordF w' (Units.map (MonoidHomClass.toMonoidHom H.conj) k) = ordF w k := by
  have hc := (GlobalTheory.Mem.Chr.conjPl_main.2.1 R H w w').1 h (k : H.E)
  unfold ordF
  congr 2

theorem val_mul_val {R : Ranks} (H : Formalism.BasicNotions.Host R) (χ : HChar H.E) (hχ : IsEtaT H χ)
    {w w' : HeightOneSpectrum (𝓞 H.E)} (h : IsConjPl H w w') : χ.val w * χ.val w' = 1 := by
  classical
  obtain ⟨c, hc, hcm, ho, -⟩ := GlobalTheory.Mem.HostCM.host_cm R H
  have hC : GlobalTheory.Mem.Chr.ConjPl H.conj.toRingEquiv w w' := (GlobalTheory.Mem.Chr.conjPl_main.2.1 R H w w').1 h
  have hC' : GlobalTheory.Mem.Chr.ConjPl c.toRingEquiv w w' := fun x => by
    have := hC x
    simpa [hc] using this
  set v := w.under (𝓞 H.F) with hv
  have hmem : ∀ P, P ∈ aboveF (L := H.E) H.F v ↔ P = w ∨ P = w' := by
    intro P
    rw [aboveF, Set.Finite.mem_toFinset, Set.mem_setOf_eq, GlobalTheory.Mem.Chr.under_eq_iff_conjPl c hcm.rank hcm.ne]
    constructor
    · rintro (h1 | h1)
      · exact Or.inl h1
      · exact Or.inr ((GlobalTheory.Mem.Chr.existsUnique_conjPl c.toRingEquiv w).unique h1 hC')
    · rintro (h1 | h1)
      · exact Or.inl h1
      · exact Or.inr (h1 ▸ hC')
  have hab : aboveF (L := H.E) H.F v = insert w {w'} := by
    ext P
    rw [hmem P, Finset.mem_insert, Finset.mem_singleton]
  have hloc : ∀ P ∈ aboveF (L := H.E) H.F v, χ.locK P (upF H.F (unif v)) = χ.val P := fun P hP => by
    have hPv : P.under (𝓞 H.F) = v := by
      rw [aboveF, Set.Finite.mem_toFinset] at hP
      exact hP
    rw [GlobalTheory.HeckeProduct.locK_unr χ (hχ.unr P), ho, hPv, ordF_unif, zpow_one]
  have hwm : w ∈ aboveF (L := H.E) H.F v := (hmem w).2 (Or.inl rfl)
  have hwm' : w' ∈ aboveF (L := H.E) H.F v := (hmem w').2 (Or.inr rfl)
  have hr := hχ.res.1 v (unif v)
  simp only [HChar.resFin] at hr
  by_cases hw : w = w'
  · subst hw
    rw [hab, Finset.insert_eq_of_mem (Finset.mem_singleton_self _), Finset.prod_singleton, etaFin, hab,
      Finset.insert_eq_of_mem (Finset.mem_singleton_self _), if_pos (Finset.card_singleton _), ordF_unif, zpow_one] at hr
    change χ.locK w (upF H.F (unif v)) = -1 at hr
    rw [hloc w hwm] at hr
    rw [hr]
    simp
  · rw [hab, Finset.prod_insert (by simpa using hw), Finset.prod_singleton, etaFin, hab,
      if_neg (by rw [Finset.card_insert_of_notMem (by simpa using hw), Finset.card_singleton]; omega)] at hr
    change χ.locK w (upF H.F (unif v)) * χ.locK w' (upF H.F (unif v)) = 1 at hr
    rw [hloc w hwm, hloc w' hwm'] at hr
    exact hr

theorem isCSD_of_isEtaT : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (χ : HChar H.E), IsEtaT H χ → IsCSD H χ := by
  intro R H χ hχ
  refine ⟨fun w w' h k => ?_, fun k => ?_⟩
  · rw [GlobalTheory.HeckeProduct.locK_unr χ (hχ.unr w'), GlobalTheory.HeckeProduct.locK_unr χ (hχ.unr w), ordF_conj H h,
      eq_inv_of_mul_eq_one_left (val_mul_val H χ hχ h), inv_zpow, inv_inv]
  · refine eq_inv_of_mul_eq_one_left (Units.ext ?_)
    rw [Units.val_mul, Units.val_one, hχ.inf, hχ.inf, ← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun g _ => ?_
    have hz : embPsi H g (k : H.E) ≠ 0 := (_root_.map_ne_zero _).2 k.ne_zero
    have e1 : embPsi H g ((Units.map (MonoidHomClass.toMonoidHom H.conj) k : H.Eˣ) : H.E) =
        starRingEnd ℂ (embPsi H g (k : H.E)) := H.conjE_apply _ _
    rw [e1, Complex.norm_conj, zpow_one, zpow_one, div_mul_div_comm, Complex.conj_mul', ← Complex.ofReal_pow,
      ← Complex.ofReal_mul, ← sq, div_self]
    exact Complex.ofReal_ne_zero.2 (pow_ne_zero _ (norm_ne_zero_iff.2 hz))

end GlobalTheory.EtaSelfDual
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidualSelmerBoundOfAuxiliaryPrimesOdd
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel

namespace GlobalTheory.ResSel

theorem residual_bound_of_parts : Cheb → PoitouTateTotallyComplex → CohDimTwo → TameLocal → LocalFiniteness → LocalTateDuality → LocalEulerChar → GlobalFiniteness → GlobalEulerChar → UnramifiedOrthogonality → Gen.ArchimedeanSignatureMatching → GreenbergWiles → ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X), ResidualBoundOddPrimes bkP := by
  intro hC hPT hCD hT hLF hLT hLE hGF hGE hU hA _ D N X bkP
  have hgw : ∀ i s, GalHyp bkP i s → EqDim bkP i s := fun i s h =>
    _root_.GlobalTheory.ResDual.eqDim hC hPT hCD hT hLF hLT hLE hGF hGE hU hA D N X bkP i s h
  refine _root_.GlobalTheory.ResSel.OddBound.residual_bound_of_parts D N X bkP (fun i => _root_.GlobalTheory.ChosenPrimes.stepAB hC D N X i)
    (fun i => _root_.GlobalTheory.ChooseForms.chooseH hGF D N X bkP i fun s h =>
      ⟨_root_.GlobalTheory.ResSel.SpanOddPf.spanOdd D N X bkP i s h, _root_.GlobalTheory.ResSel.AltSpan.spanTwo_of_galHyp D N X bkP i s h, hgw i s h⟩)
    (fun i s h => ?_)
  have hk := _root_.GlobalTheory.ScalarFrob.firstHalf hLF hLT hLE hT D N X bkP i s h
  exact GlobalTheory.T.residual_selmer_determinant_order_bound hT D N X bkP i s h hk
    (_root_.GlobalTheory.ResRecip.reciprocity hC hPT hCD hT hLF hLT hLE hGF hGE hU hA D N X bkP i s h hk) (hgw i s h)

end GlobalTheory.ResSel
end

