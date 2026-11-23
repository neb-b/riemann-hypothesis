module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.GelfandKazhdanDual
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1178
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankOfMulEqOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0002
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.ExistsDvdQKPowSubOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1176
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0291
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatAevalDvrPlaceRingUniformiserResidueLifts
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1122
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1131
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1183
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1139
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0291
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GraphIdealLocalizationMaximalIdealEqSpan

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTwistCuspidalTrivialOnSplitCentre
section
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair

namespace GlobalTheory.GKNorm

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem exists_splitCentre_eigen (π : CuspSub E a) : ∃ c : ℂ, ∀ φ ∈ π.V, ∀ (t : ℝ) (g : GA E a),
    φ.1 (GlobalTheory.UnitaryBC.splitCentre E a t * g) = Complex.exp (c * t) * φ.1 g := by
  obtain ⟨c, hc⟩ := GlobalTheory.CuspRep.Central.lie_scalar π (1 : Cinf E)
  refine ⟨c, fun φ hφ t g => ?_⟩
  have e3 : GlobalTheory.CuspRep.Central.scL a (fun _ : InfinitePlace E => (t : ℂ)) =
      t • GlobalTheory.CuspRep.Central.scL (E := E) a 1 := by
    ext i j w
    by_cases hij : i = j <;> simp [hij]
  have h1 := GlobalTheory.CuspRep.Central.rs_exp (fun _ : InfinitePlace E => (t : ℂ)) (c * t) φ (by
    rw [e3, map_smul, LinearMap.smul_apply, hc φ hφ, mul_comm, mul_smul, Complex.coe_smul])
  rw [GlobalTheory.CuspRep.CuspidalL2GL.splitCentre_comm, GlobalTheory.CuspRep.CuspidalL2GL.splitCentre_eq_scalar]
  exact congrFun (congrArg Subtype.val h1) g

theorem exists_twist_isNormalised : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), 1 ≤ a →
    ∀ π : CuspSub E a, ∃ χ : HChar E, GlobalTheory.DiscSpec.IsNormalised (π.twist χ) := by
  intro E _ _ _ a ha π
  obtain ⟨c, hs⟩ := exists_splitCentre_eigen π
  obtain ⟨χ, hχ⟩ := GlobalTheory.CuspQuot.exists_chiDet_splitCentre (E := E) (a := a) (by omega) (-c)
  refine ⟨χ, ?_⟩
  rintro _ ⟨φ, hφ, rfl⟩ t g
  change (mulChi a χ φ).1 _ = (mulChi a χ φ).1 _
  rw [mulChi_apply, mulChi_apply, map_mul, Units.val_mul, hχ, hs φ hφ, mul_mul_mul_comm, ← Complex.exp_add]
  simp

end GlobalTheory.GKNorm

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnramifiedLocalSituationOfEmbedding
section
set_option autoImplicit false

noncomputable section

open NumberField PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors Formalism.CohomologicalDescent.FrobeniusPeriodChange IsLocalRing GlobalTheory.WachPlace

namespace GlobalTheory.PlaceLetters

variable {l : ℕ} [Fact l.Prime] {E : Type} [Field E] [NumberField E]

theorem norm_emb_le (σ : E →+* Om l) (b : 𝓞 E) : ‖σ (b : E)‖ ≤ 1 :=
  GlobalTheory.SplitEmbSep.norm_le_one_of_isIntegral (map_isIntegral_int σ b.isIntegral_coe)

theorem emb_eq_of_congr (hE : ¬ (l : ℤ) ∣ discr E) (τ τ' : E →+* Om l)
    (hlt : ∀ b : 𝓞 E, ‖τ (b : E) - τ' (b : E)‖ < 1) : τ = τ' := by
  classical
  by_contra hne
  have hd := GlobalTheory.SplitEmbSep.one_le_norm_intCast (C := Om l) Fact.out GlobalTheory.PlaceBridge.norm_l_lt_one hE
  let b := integralBasis E
  have e : Module.Free.ChooseBasisIndex ℤ (𝓞 E) ≃ (E →ₐ[ℚ] Om l) :=
    Fintype.equivOfCardEq (by rw [AlgHom.card, Module.finrank_eq_card_basis b])
  have hdet := Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two ℚ (Om l) b e
  rw [← coe_discr, map_intCast] at hdet
  set M := Algebra.embeddingsMatrixReindex ℚ (Om l) b e with hM
  have hMij : ∀ i j, M i j = (e j).toRingHom ((RingOfIntegers.basis E i : 𝓞 E) : E) := by
    intro i j
    simp [hM, b, Algebra.embeddingsMatrixReindex, Algebra.embeddingsMatrix, integralBasis_apply]
  set k := e.symm τ.toRatAlgHom with hk
  set k' := e.symm τ'.toRatAlgHom with hk'
  have hkk : k ≠ k' := fun h => hne (by
    have := e.symm.injective h
    exact RingHom.ext fun x => DFunLike.congr_fun this x)
  have hcol : ∀ i, M i k + (-1 : Om l) • M i k' =
      τ ((RingOfIntegers.basis E i : 𝓞 E) : E) - τ' ((RingOfIntegers.basis E i : 𝓞 E) : E) := by
    intro i
    rw [hMij, hMij, hk, hk', e.apply_symm_apply, e.apply_symm_apply, neg_one_smul,
      ← sub_eq_add_neg]
    rfl
  have hlt' : ‖M.det‖ < 1 := by
    rw [← Matrix.det_updateCol_add_smul_self M hkk (-1)]
    refine GlobalTheory.SplitEmbSep.norm_det_lt_one _ (fun i j => ?_) k fun i => ?_
    · by_cases hj : j = k
      · rw [hj, Matrix.updateCol_self, hcol]; exact (hlt _).le
      · rw [Matrix.updateCol_ne hj, hMij]; exact norm_emb_le _ _
    · rw [Matrix.updateCol_self, hcol]; exact hlt _
  rw [hdet, norm_pow] at hd
  exact absurd (hd.trans_lt (pow_lt_one₀ (norm_nonneg _) hlt' two_ne_zero)) (lt_irrefl _)

theorem norm_algHom {K : IntermediateField ℚ_[l] (Om l)} (f : ↥K →ₐ[ℚ_[l]] Om l) (x : ↥K) :
    ‖f x‖ = ‖(x : Om l)‖ := by
  rw [← PadicAlgCl.spectralNorm_eq, ← PadicAlgCl.spectralNorm_eq, spectralNorm, spectralNorm]
  have h1 := minpoly.algHom_eq f f.toRingHom.injective x
  have h2 := minpoly.algHom_eq K.val K.val.toRingHom.injective x
  exact congrArg spectralValue (h1.trans h2.symm)

theorem norm_gal (g : GQ l) (x : Om l) : ‖g x‖ = ‖x‖ := by
  rw [← PadicAlgCl.spectralNorm_eq, ← PadicAlgCl.spectralNorm_eq, spectralNorm, spectralNorm,
    minpoly.algEquiv_eq]

theorem norm_sub_lt_one {x y : Om l} (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) : ‖x - y‖ < 1 := by
  rw [sub_eq_add_neg]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt hx (by rwa [norm_neg]))

theorem inertia_of_fix (g : GQ l) (hg : ∀ x ∈ MaximalUnramifiedExtension l, g x = x) (x : Om l) (hx : ‖x‖ ≤ 1) : ‖g x - x‖ < 1 := by
  rcases lt_or_eq_of_le hx with hlt | heq
  · exact norm_sub_lt_one (by rwa [norm_gal]) hlt
  · obtain ⟨ζ, m, hm, hζ, hxζ⟩ := ReciprocityTheory.DiscreteGroups.LocalClassField.exists_teichmuller_bar x heq
    have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; exact hm (dvd_zero l))
    have h1 : g ζ = ζ := hg ζ (IntermediateField.subset_adjoin _ _ ⟨m, hm0, hm, hζ⟩)
    have h2 : g x - x = g (x - ζ) - (x - ζ) := by rw [map_sub, h1]; ring
    rw [h2]
    exact norm_sub_lt_one (by rwa [norm_gal]) hxζ

theorem emb_mem_Kur (hE : ¬ (l : ℤ) ∣ discr E) (τ : E →+* Om l) (x : E) : τ x ∈ MaximalUnramifiedExtension l := by
  have : IsGalois ℚ_[l] (Om l) := {}
  rw [← InfiniteGalois.fixedField_fixingSubgroup (MaximalUnramifiedExtension l), IntermediateField.mem_fixedField_iff]
  intro g hg
  have h := emb_eq_of_congr hE ((g : Om l →+* Om l).comp τ) τ fun b =>
    inertia_of_fix g ((IntermediateField.mem_fixingSubgroup_iff _ _).mp hg) _ (norm_emb_le τ b)
  exact DFunLike.congr_fun h x

theorem exists_extend {K : IntermediateField ℚ_[l] (Om l)} (f : ↥K →ₐ[ℚ_[l]] Om l) :
    ∃ g : Om l →ₐ[ℚ_[l]] Om l, ∀ x : ↥K, g x = f x :=
  ⟨f.liftNormal (Om l), fun x => f.liftNormal_commutes (Om l) x⟩

section Bridge

variable {Ω : Type} [Field Ω] [Algebra E Ω] {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type} [CommRing O] [Algebra ℤ_[l] O]
  [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O)

theorem kw_le (M : IntermediateField ℚ_[l] (Om l)) (h : ∀ x : E, Bw.j (algebraMap E Ω x) ∈ M) : Bw.Kw.1 ≤ M := by
  have hfin := GlobalTheory.PlaceBridge.finiteDimensional_adjoin_range (Bw.j.comp (algebraMap E Ω))
  have hcl := Submodule.closed_of_finiteDimensional (𝕜 := ℚ_[l])
    (IntermediateField.adjoin ℚ_[l] (Set.range (Bw.j.comp (algebraMap E Ω)))).toSubmodule
  refine le_trans (fun y hy => ?_) (IntermediateField.adjoin_le_iff.2 (Set.range_subset_iff.2 h))
  exact closure_minimal (IntermediateField.subset_adjoin ℚ_[l] _) hcl (Bw.j_dense hy)

theorem kw_le_comap (LL : FinExt l) (hL : ∀ (τ : E →+* Om l) (x : E), τ x ∈ LL.1) (g : Om l →ₐ[ℚ_[l]] Om l) :
    Bw.Kw.1 ≤ LL.1.comap g :=
  kw_le Bw _ fun x => hL ((g : Om l →+* Om l).comp (Bw.j.comp (algebraMap E Ω))) x

theorem caseA (hl : l ≠ 2) (hE : ¬ (l : ℤ) ∣ discr E) (LL : FinExt l) (hζ : ∃ ζ : ↥LL.1, IsPrimitiveRoot ζ l)
    (hL : ∀ (τ : E →+* Om l) (x : E), τ x ∈ LL.1) : CaseA Bw.Kw LL := by
  have hK : Bw.Kw.1 ≤ MaximalUnramifiedExtension l := kw_le Bw _ fun x => emb_mem_Kur hE (Bw.j.comp (algebraMap E Ω)) x
  refine ⟨hK, hl, le_rfl, fun h => absurd h hl, (le_inf le_rfl hK).trans le_sup_left, fun τ x => ?_⟩
  obtain ⟨g, hg⟩ := exists_extend τ
  obtain ⟨ζ, hζ⟩ := hζ
  have hζ' : IsPrimitiveRoot (ζ : Om l) l := hζ.map_of_injective (f := LL.1.val) Subtype.val_injective
  have hle : Ks Bw.Kw 1 ≤ LL.1.comap g := by
    refine sup_le (inf_le_left.trans (kw_le_comap Bw LL hL g)) (IntermediateField.adjoin_le_iff.2 fun y hy => ?_)
    have hy' : g y ^ l = 1 := by
      have : y ^ l = 1 := by simpa using hy
      rw [← map_pow, this, map_one]
    haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
    obtain ⟨i, -, hi⟩ := hζ'.eq_pow_of_pow_eq_one hy'
    change g y ∈ LL.1
    rw [← hi]
    exact pow_mem ζ.2 i
  rw [← hg]
  exact hle x.2

end Bridge

section Letters

variable {Ω : Type} [Field Ω] [Algebra E Ω] {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type} [CommRing O] [Algebra ℤ_[l] O]
  [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O) (hK : Bw.Kw.1 ≤ K0 Bw.Kw) {LL : FinExt l}

def toK0 : E →+* ↥(K0 Bw.Kw) :=
  (Bw.j.comp (algebraMap E Ω)).codRestrict (K0 Bw.Kw) fun x => hK (Bw.j_E x)

def embOf (e : ↥(K0 Bw.Kw) →ₐ[ℚ_[l]] ↥LL.1) : E →+* Om l :=
  ((LL.1.val.comp e : ↥(K0 Bw.Kw) →ₐ[ℚ_[l]] Om l) : ↥(K0 Bw.Kw) →+* Om l).comp (toK0 Bw hK)


omit [NumberField E] in
theorem isInduced_embOf (e : ↥(K0 Bw.Kw) →ₐ[ℚ_[l]] ↥LL.1) (τ : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL.1)
    (hτ : ∀ x : ↥(K0 Bw.Kw), τ (algebraMap ↥(K0 Bw.Kw) ↥Bw.Kw.1 x) = e x) :
    GlobalTheory.Pst.IsInduced Bw (embOf Bw hK e) τ := fun x =>
  congrArg Subtype.val (hτ (toK0 Bw hK x)).symm


omit [NumberField E] in
theorem embOf_injective : Function.Injective (embOf Bw hK (LL := LL)) := by
  intro e e' h
  have h1 := isInduced_embOf Bw hK e (e.comp (IntermediateField.inclusion hK)) fun _ => rfl
  have h2 := isInduced_embOf Bw hK e' (e'.comp (IntermediateField.inclusion hK)) fun _ => rfl
  rw [← h] at h2
  have h3 := h1.unique h2
  exact AlgHom.ext fun x => DFunLike.congr_fun h3 (algebraMap ↥(K0 Bw.Kw) ↥Bw.Kw.1 x)

theorem embOf_frob (P : LocPrime l) (hE : ¬ (l : ℤ) ∣ discr E) {σ : Equiv.Perm (E →+* PadicAlgCl l)}
    (hσ : GlobalTheory.ExpFrame.IsFrobPerm σ) (e : ↥(K0 Bw.Kw) →ₐ[ℚ_[l]] ↥LL.1) :
    embOf Bw hK (e.comp (P.PD Bw.Kw).σ) = σ (embOf Bw hK e) := by
  refine emb_eq_of_congr hE _ _ fun b => ?_
  have h1 := hσ (embOf Bw hK e) b
  have h2 := P.PD_σ Bw.Kw (toK0 Bw hK b) (norm_emb_le (Bw.j.comp (algebraMap E Ω)) b)
  have h3 := norm_algHom (LL.1.val.comp e) ((P.PD Bw.Kw).σ (toK0 Bw hK b) - toK0 Bw hK b ^ l)
  rw [map_sub, map_pow] at h3
  have h4 : ‖embOf Bw hK (e.comp (P.PD Bw.Kw).σ) b - embOf Bw hK e b ^ l‖ < 1 := h3.trans_lt h2
  have h5 := norm_sub_lt_one h4 h1
  rwa [sub_sub_sub_cancel_right] at h5

end Letters

theorem exists_bridge_over (Ω : Type) [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (LL : FinExt l)
    (hL : ∀ (τ : E →+* Om l) (x : E), τ x ∈ LL.1) (τ : E →+* Om l) :
    ∃ (w : IsDedekindDomain.HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (_ : Formalism.ConjugateSelfDual.IsPlaceOver A w)
      (Bw : LocBridge l E Ω (ReciprocityTheory.Gal.Dec (F := E) A) ↥(OL LL)), GlobalTheory.Pst.Induces Bw ∧ Bw.LL.1 ≤ LL.1 ∧
        ∀ x, τ x = Bw.j (algebraMap E Ω x) := by
  obtain ⟨w, A, hA, L0, Bw, hI, hτ⟩ := GlobalTheory.ExpFrame.Tests.exists_bridge Ω τ
  refine ⟨w, A, hA, { Bw with
    LL := LL
    LL_split := fun f x => ?_
    eO := RingEquiv.refl _
    eO_alg := fun _ => rfl
    eO_cont := continuous_id
    eO_symm_cont := continuous_id }, hI, le_rfl, hτ⟩
  obtain ⟨g, hg⟩ := exists_extend f
  rw [← hg]
  exact kw_le_comap Bw LL hL g x.2

theorem exists_place : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (H : LocHW l P) (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω], l ≠ 2 → ¬ (l : ℤ) ∣ NumberField.discr E → ∀ (σ : Equiv.Perm (E →+* PadicAlgCl l)), GlobalTheory.ExpFrame.IsFrobPerm σ → ∀ LL : FinExt l, (∃ ζ : ↥LL.1, IsPrimitiveRoot ζ l) → (∀ (τ : E →+* PadicAlgCl l) (x : E), τ x ∈ LL.1) → ∀ i₀ : E →+* PadicAlgCl l, ∃ (K : FinExt l) (hA : CaseA K LL) (ι : ↥(GK K) →* (Ω ≃ₐ[E] Ω)) (κ : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → (E →+* PadicAlgCl l)), Function.Injective κ ∧ (∀ i, κ (i - 1) = σ (κ i)) ∧ i₀ ∈ Set.range κ ∧ ∀ (n : ℕ) (r : (Ω ≃ₐ[E] Ω) →* GL (Fin n) ↥(OL LL)) (J : (E →+* PadicAlgCl l) → Multiset ℤ), GlobalTheory.ExpFrame.CrysWith ((Matrix.GeneralLinearGroup.map (toOm LL)).comp r) J → MatGood P (H.W K 1 LL hA.2.2).emb (r.comp ι) (fun i => J (κ i)) := by
  intro l _ P AI hT H E Ω _ _ _ _ _ hl hE σ hσ LL hζ hL i₀
  obtain ⟨w, A, hA, Bw, hI, hLL, hi₀⟩ := exists_bridge_over Ω LL hL i₀
  have hC := caseA Bw hl hE LL hζ hL
  have hK0 : Bw.Kw.1 ≤ K0 Bw.Kw := le_inf le_rfl hC.1
  have hbij := (H.W Bw.Kw 1 LL hC.2.2).emb_bij
  have hembσ := (H.W Bw.Kw 1 LL hC.2.2).emb_σ
  let emb := (H.W Bw.Kw 1 LL hC.2.2).emb
  have hK0L : K0 Bw.Kw ≤ LL.1 := inf_le_left.trans (kw_le Bw _ fun x => hL (Bw.j.comp (algebraMap E Ω)) x)
  refine ⟨Bw.Kw, hC, (ReciprocityTheory.Gal.Dec (F := E) A).subtype.comp Bw.e.symm.toMonoidHom, fun i => embOf Bw hK0 (emb i),
    (embOf_injective Bw hK0).comp hbij.1, fun i => ?_, ?_, fun n r J hr => ?_⟩
  · have h := hembσ (i - 1)
    rw [sub_add_cancel] at h
    exact (congrArg (embOf Bw hK0) h.symm).trans (embOf_frob Bw hK0 P hE hσ (emb i))
  · obtain ⟨i, hi⟩ := hbij.2 (IntermediateField.inclusion hK0L)
    refine ⟨i, RingHom.ext fun x => ?_⟩
    change embOf Bw hK0 ((H.W Bw.Kw 1 LL hC.2.2).emb i) x = _
    rw [hi, hi₀]
    rfl
  · obtain ⟨hc, hj⟩ := hr.2 P AI ⟨hT⟩ w A hA _ Bw hI
    have hM : GlobalTheory.Pst.IsModel Bw (((Matrix.GeneralLinearGroup.map (toOm LL)).comp r).comp
        (ReciprocityTheory.Gal.Dec (F := E) A).subtype) LL
        (Formalism.MainNotions.N.mapRep (algebraMap ↥(OL LL) ↥LL.1) (r.comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype)) :=
      ⟨hLL, by ext g a b; rfl⟩
    refine ⟨fun a b => ?_, (hM.isCrysAt_iff P).1 hc, fun i τ hτ a => ?_⟩
    · have h1 : Continuous fun g : ↥(GK Bw.Kw) => ((Bw.e.symm g : ↥(ReciprocityTheory.Gal.Dec (F := E) A)) : Ω ≃ₐ[E] Ω) :=
        continuous_subtype_val.comp Bw.e_symm_cont
      have h2 := (Units.continuous_val.comp (hr.1.comp h1)).matrix_elem a b
      exact continuous_induced_rng.2 h2
    · have hτ' := isInduced_embOf Bw hK0 (emb i) τ hτ
      exact (GlobalTheory.Pst.IsJumpsAt.count_eq P hM hτ' (hj _ _ _ hτ') a).symm

end GlobalTheory.PlaceLetters

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExpGLImageBallMemNhds
section
open NumberField MeasureTheory Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CuspQuot GlobalTheory.GLFin

noncomputable section

namespace GlobalTheory.GLFin

theorem expGL_image_ball_mem_nhds : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), ∀ ε : ℝ, 0 < ε →
    (fun X : Lie E a => GlobalTheory.ExpDeriv.expGL X 1) '' {X | ‖X‖ < ε} ∈ nhds (1 : GL (Fin a) (Cinf E)) := by
  intro E _ _ _ a ε hε
  letI : NormedRing (Matrix (Fin a) (Fin a) (Cinf E)) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix (Fin a) (Fin a) (Cinf E)) := Matrix.linftyOpNormedAlgebra
  haveI : CompleteSpace (Matrix (Fin a) (Fin a) (Cinf E)) := FiniteDimensional.complete ℝ _
  have hd : HasStrictFDerivAt (NormedSpace.exp : Matrix (Fin a) (Fin a) (Cinf E) → _)
      ((ContinuousLinearEquiv.refl ℝ (Matrix (Fin a) (Fin a) (Cinf E)) : Matrix (Fin a) (Fin a) (Cinf E) →L[ℝ] _)) 0 :=
    hasStrictFDerivAt_exp_zero
  have hmap0 := hd.map_nhds_eq_of_equiv
  rw [NormedSpace.exp_zero] at hmap0
  have hmap : Filter.map (NormedSpace.exp : Matrix (Fin a) (Fin a) (Cinf E) → _) (nhds 0) =
      nhds (1 : Matrix (Fin a) (Fin a) (Cinf E)) := hmap0
  have hopen : IsOpen {X : Matrix (Fin a) (Fin a) (Cinf E) | ‖(Matrix.of.symm X : Lie E a)‖ < ε} :=
    isOpen_lt (continuous_norm.comp (continuous_id : Continuous fun X : Lie E a => X)) continuous_const
  have hball : {X : Matrix (Fin a) (Fin a) (Cinf E) | ‖(Matrix.of.symm X : Lie E a)‖ < ε} ∈
      nhds (0 : Matrix (Fin a) (Fin a) (Cinf E)) := hopen.mem_nhds (by simpa using hε)
  have himg : (NormedSpace.exp : Matrix (Fin a) (Fin a) (Cinf E) → _) ''
      {X : Matrix (Fin a) (Fin a) (Cinf E) | ‖(Matrix.of.symm X : Lie E a)‖ < ε} ∈
      nhds (1 : Matrix (Fin a) (Fin a) (Cinf E)) := hmap ▸ Filter.image_mem_map hball
  have hpre := Units.continuous_val.continuousAt.preimage_mem_nhds (x := (1 : GL (Fin a) (Cinf E))) himg
  refine Filter.mem_of_superset hpre ?_
  rintro u ⟨X, hX, hXu⟩
  refine ⟨Matrix.of.symm X, hX, Units.ext ?_⟩
  rw [GlobalTheory.ExpDeriv.expGL_val, one_smul]
  exact hXu

end GlobalTheory.GLFin

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtremalVectorsHolomorphicModelUniqueUpToPhase
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolLowOnce

open GlobalTheory.HolDict.HolTo GlobalTheory.HolDict.CoefExt

theorem extLine_of_holShape : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S),
    GlobalTheory.HolDict.HolShape M → ExtLine M := by
  intro D V S M hM v v' hv hv' τ
  obtain ⟨θ, hθ⟩ := GlobalTheory.DualPairCompare.exists_infFam D

  have h1 : ∀ ρ, M.σ ρ 1 = 1 := fun ρ => (M.ds ρ).2.2.1.1.1
  have hv0 : ∀ ρ, ((v ρ : M.sm ρ) : M.H ρ) ≠ 0 := by
    intro ρ h0
    have hn := (hv ρ).1
    rw [h0, norm_zero] at hn
    exact zero_ne_one hn
  choose w hw using fun ρ c => wt_int (h1 ρ) (hv0 ρ) (hv ρ).2.2 (arr (nNeg (M.ε ρ)) c)
  have hW : WtIs M w := fun ρ c => hw ρ c
  obtain ⟨hsm, hk⟩ := GlobalTheory.T.baseFrameBorel_acts_extremalVector_by_weight D θ V S M w v hθ hM hW hv τ
  obtain ⟨hC, hU, hI, hO⟩ := _root_.GlobalTheory.HolDict.ModelRep.model_rep D V S M τ
  haveI := hC
  have hOF := (hO hM).1

  have hdet : (x0Mat M τ).det ≠ 0 := by
    intro h0
    have hd := congrArg Matrix.det hOF.2
    rw [Matrix.det_mul, Matrix.det_mul, h0, mul_zero, Matrix.det_diagonal] at hd
    refine (Finset.prod_ne_zero_iff.mpr fun a _ => ?_) hd.symm
    unfold ReciprocityTheory.ChartRestriction.G.FD.sgn
    split_ifs <;> norm_num

  set x : M.H τ := ((v τ : M.sm τ) : M.H τ) with hx
  set y : M.H τ := ((v' τ : M.sm τ) : M.H τ) with hy
  set c : ℂ := ⟪x, y⟫_ℂ with hc
  have hxx : ⟪x, x⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, (hv τ).1]
    norm_num
  have horth : ⟪y - c • x, x⟫_ℂ = 0 := by
    rw [inner_sub_left, inner_smul_left, hxx, mul_one, hc, inner_conj_symm, sub_self]
  have htor : ∀ s, M.rep τ (torEl (fun _ : Unit => x0Mat M τ) s ()) (y - c • x) =
      torCh (fun _ : Unit => w τ) s • (y - c • x) := by
    intro s
    have ex := torus_wt M hW τ (hv τ).2.2 s hdet
    have ey := torus_wt M hW τ (hv' τ).2.2 s hdet
    rw [map_sub, map_smul, ex, ey, smul_sub, smul_comm c]
  have hz := eq_zero_of_orth hOF hU hI hsm (hv0 τ) hk (y - c • x) (fun s => torEl_mem hOF s) htor horth
  have hyx : y = c • x := sub_eq_zero.mp hz
  refine ⟨c, ?_, ?_⟩
  · have hn := congrArg norm hyx
    rw [norm_smul, hy, (hv' τ).1, hx, (hv τ).1, mul_one] at hn
    exact hn.symm
  · exact Subtype.ext hyx

end GlobalTheory.HolLowOnce
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatAevalDvrPlaceRingUniformiserResidueLiftsStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair GlobalTheory.GraphLocal
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_aeval_dvrPlaceRing_uniformiser_residueLifts : ∀ {K κ : Type} [Field K] [Field κ] [Algebra ℂ K] [Algebra ℂ κ] (k : ℕ) (R : Subring K)
    (π : R →+* κ) (E : Place (algebraMap ℂ K)) (hER : E.Contains R) (t : E.ring) (zR : Fin k → R),
    (∀ a (h : algebraMap ℂ K a ∈ R), π ⟨algebraMap ℂ K a, h⟩ = algebraMap ℂ κ a) →
    (∀ a, algebraMap ℂ K a ∈ R) →
    (∀ r : R, (r : K) ≠ 0 → (π r = 0 ↔ 0 < E.ord r)) →
    Irreducible t → AlgebraicIndependent ℂ (fun i => π (zR i)) →
    (MvPolynomial.aeval (Fin.cons (⟨(t : K), t.2⟩ : placeAlg E)
        (fun i => (⟨(zR i : K), hER _ (zR i).2⟩ : placeAlg E))) :
        MvPolynomial (Fin (k + 1)) ℂ →ₐ[ℂ] placeAlg E).toRingHom.Flat := by
  first | exact @GlobalTheory.GraphLocal.FlatPlace.flat_aeval_placeAlg | exact GlobalTheory.GraphLocal.FlatPlace.flat_aeval_placeAlg | (intros; apply GlobalTheory.GraphLocal.FlatPlace.flat_aeval_placeAlg <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericMemberSectionNeZeroIsPrimeAffineChartStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.GenericMember
open GlobalTheory.ThickeningDetermines (secIdeal)
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.genericMemberSection_ne_zero_isPrime_affineChart : ∀ (k : Type) [Field k] (N : ℕ) (X X' : Scheme.{0}) [IsIntegral X] (f : X ⟶ Sp k) (f' : X' ⟶ Sp (FractionRing (MvPolynomial (Fin N) k))) (π : X' ⟶ X) (L : LB X) (hL : L.IsLB) (b : Fin N → L.Sec) (V : X.Opens) (hne : (V : Set X).Nonempty) (hW : IsAffineOpen (π ⁻¹ᵁ V)) (c : L.ι) (hVc : V ≤ L.U c) (j : Fin N), IsUnit (resG X hVc ((b j).f c)) → letI : Algebra k Γ(X, V) := ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appLE ⊤ V le_top).hom.toAlgebra; ∀ e : FractionRing (MvPolynomial (Fin N) k) ⊗[k] Γ(X, V) ≃+* Γ(X', π ⁻¹ᵁ V), (∀ a, e (1 ⊗ₜ a) = (π.app V).hom a) → (∀ q, e (q ⊗ₜ 1) = ((Scheme.ΓSpecIso _).inv ≫ f'.appLE ⊤ (π ⁻¹ᵁ V) le_top).hom q) → (genSec k N f' π L b).f (fun _ => c) ≠ 0 ∧ ((secIdeal (LB.isLB_pull hL π) (genSec k N f' π L b)).ideal ⟨π ⁻¹ᵁ V, hW⟩ = ⊤ ∨ ((secIdeal (LB.isLB_pull hL π) (genSec k N f' π L b)).ideal ⟨π ⁻¹ᵁ V, hW⟩).IsPrime ∧ ((secIdeal (LB.isLB_pull hL π) (genSec k N f' π L b)).ideal ⟨π ⁻¹ᵁ V, hW⟩).comap (π.app V).hom = ⊥) := by
  first | exact @GlobalTheory.GenericMember.genSec_chart_ne_zero_and_isPrime | exact GlobalTheory.GenericMember.genSec_chart_ne_zero_and_isPrime | (intros; apply GlobalTheory.GenericMember.genSec_chart_ne_zero_and_isPrime <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricExpansionOfParts
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TrMult

theorem strictAnti_of_gap {r : ℕ} (hr : Odd r) {lam : Fin r → ℤ} (h : Gap lam) : StrictAnti lam := by
  obtain ⟨n, rfl⟩ : ∃ n, r = n + 1 := ⟨r - 1, by obtain ⟨k, hk⟩ := hr; omega⟩
  rw [Fin.strictAnti_iff_succ_lt]
  intro i
  have := h i.castSucc i.succ (by simp)
  push_cast at this
  omega

end GlobalTheory.TrMult

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GraphIdealLocalizationMaximalIdealEqSpanStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair GlobalTheory.GraphLocal
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.graphIdeal_localization_maximalIdeal_eq_span : ∀ {K κ κ' L : Type} [Field K] [Field κ] [Field κ'] [Field L] [Algebra ℂ K] [Algebra ℂ κ] [Algebra ℂ κ']
    [Algebra (K ⊗[ℂ] κ') L] [IsFractionRing (K ⊗[ℂ] κ') L]
    (k : ℕ) (R : Subring K) (π : R →+* κ) (ρ : κ →ₐ[ℂ] κ') (E : Place (algebraMap ℂ K))
    (hER : E.Contains R) (t : E.ring) (zR : Fin k → R)
    (𝔭 : Ideal (tens (κ' := κ') (placeAlg E))) [𝔭.IsPrime],
  (∃ O' : Subring κ', IsLocModel (algebraMap ℂ κ') O') →
  (∀ a (h : algebraMap ℂ K a ∈ R), π ⟨algebraMap ℂ K a, h⟩ = algebraMap ℂ κ a) →
  (∀ a, algebraMap ℂ K a ∈ R) → (∀ f : κ, ∃ a b : R, π b ≠ 0 ∧ f * π b = π a) →
  (∀ r : R, (r : K) ≠ 0 → (π r = 0 ↔ 0 < E.ord r)) →
  Irreducible t → TrBasis (algebraMap ℂ κ) (fun i => π (zR i)) →
  𝔭 ∈ (graphIdeal E R π ρ).minimalPrimes →
  letI := isLocalRing_locAt (L := L) 𝔭 (IsFractionRing.injective (K ⊗[ℂ] κ') L)
  IsLocalRing.maximalIdeal (locAt (L := L) 𝔭) =
    Ideal.span (Set.range fun i => toQ 𝔭 (gens E R π ρ hER t zR i)) := by
  first | exact @GlobalTheory.GraphLocal.MaxGen.maximalIdeal_locAt_eq_span | exact GlobalTheory.GraphLocal.MaxGen.maximalIdeal_locAt_eq_span | (intros; apply GlobalTheory.GraphLocal.MaxGen.maximalIdeal_locAt_eq_span <;> assumption)
end

