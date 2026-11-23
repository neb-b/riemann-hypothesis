module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0047
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1507
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0293
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Bundle0016
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1502
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1508
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1332
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HasSignatureComplement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0082
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatPath

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasArchimedeanCharExponentsConjOfHasInfExp
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.ConjInfExp

open GlobalTheory.FockCompare GlobalTheory.AdelicU

theorem conj_div_norm_zpow (u : ℂ) (hu : u ≠ 0) (k : ℤ) :
    (starRingEnd ℂ u / ((‖starRingEnd ℂ u‖ : ℝ) : ℂ)) ^ (-k) = (u / ((‖u‖ : ℝ) : ℂ)) ^ k := by
  have h0 : ((‖u‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 hu)
  rw [Complex.norm_conj, _root_.zpow_neg, ← _root_.inv_zpow]
  congr 1
  rw [inv_div, div_eq_div_iff ((map_ne_zero _).2 hu) h0, Complex.mul_conj', sq]

theorem piInf_eq {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (hθ : IsInfFam θ)
    (τ : D.what₂.Tau) (w : InfinitePlace D.host.F)
    (h : ((starRingEnd ℂ).comp (tauE D τ)).comp (algebraMap D.host.F D.host.E) = w.embedding) (y : AE D) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (⟨(starRingEnd ℂ).comp (tauE D τ), h⟩ : EmbOver D.host.E w) y = starRingEnd ℂ (θ τ (infPart D y)) := by
  have hr : ∀ a : Ainf D.host.F, InfinitePlace.Completion.extensionEmbedding w (GlobalTheory.AutFunCompare.evW w a) =
      starRingEnd ℂ (θ τ (a ⊗ₜ[D.host.F] (1 : D.host.E))) := by
    intro a
    refine DenseRange.induction_on (InfiniteAdeleRing.denseRange_algebraMap D.host.F) a (isClosed_eq ?_ ?_) fun f => ?_
    · exact (InfinitePlace.Completion.isometry_extensionEmbedding w).continuous.comp (continuous_apply w)
    · exact Complex.continuous_conj.comp (hθ τ).2
    · rw [(GlobalTheory.AutFunCompare.evW w).commutes]
      have e1 := InfinitePlace.Completion.extensionEmbedding_coe w ((WithAbs.equiv w.1).symm f)
      have e2 : θ τ (algebraMap D.host.F (Ainf D.host.F) f ⊗ₜ[D.host.F] (1 : D.host.E)) = tauE D τ (algebraMap D.host.F D.host.E f) := by
        rw [← (hθ τ).1, ← Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply']
      rw [e2]
      rw [AbsoluteValue.Completion.algebraMap_def, WithAbs.algebraMap_right_apply,
        Algebra.algebraMap_self_apply]
      refine e1.trans ?_
      exact (RingHom.congr_fun h f).symm
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add a b ha hb => rw [RingHom.map_add (f := _), RingHom.map_add (f := _), RingHom.map_add (f := _), ha, hb, map_add (starRingEnd ℂ)]
  | tmul a x =>
    have e : θ τ (fstA D.host.F a ⊗ₜ[D.host.F] x) = θ τ (fstA D.host.F a ⊗ₜ[D.host.F] (1 : D.host.E)) * tauE D τ x := by
      rw [← (hθ τ).1 x, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    have l1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (⟨(starRingEnd ℂ).comp (tauE D τ), h⟩ : EmbOver D.host.E w) (a ⊗ₜ[D.host.F] x) =
        infEmb (⟨(starRingEnd ℂ).comp (tauE D τ), h⟩ : EmbOver D.host.E w) (evInf D.host.F w a ⊗ₜ[D.host.F] x) := by
      simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf, compInf, RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
        AlgHom.coe_toRingHom, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq]
    have l2 : infPart D (a ⊗ₜ[D.host.F] x) = fstA D.host.F a ⊗ₜ[D.host.F] x := by
      simp only [infPart, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq]
    rw [l1, l2, infEmb_tmul, e, map_mul, ← hr]
    rfl

end GlobalTheory.ConjInfExp

namespace GlobalTheory.ConjInfExp

theorem finPart_eq_one {D : D7} (z : AE D) (hz : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (z - 1)) : finPart D z = 1 := by
  let u : AF D.host.F := ⟨0, 1⟩
  have hu0 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F u = 0 := by
    show InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F (0 : Ainf D.host.F) = 0
    exact map_zero _
  have h1 := hz u hu0
  have key : ∀ y : AE D, finPart D (u • y) = finPart D y := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => rw [smul_zero]
    | add a b ha hb => rw [smul_add, RingHom.map_add (f := _), RingHom.map_add (f := _), ha, hb]
    | tmul a x =>
      rw [TensorProduct.smul_tmul']
      simp only [finPart, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq, smul_eq_mul, map_mul]
      congr 1
      show (1 : Af D.host.F) * sndA D.host.F a = sndA D.host.F a
      exact one_mul _
  rw [← sub_eq_zero, ← RingHom.map_one (finPart D), ← RingHom.map_sub, ← key, h1, RingHom.map_zero]
end GlobalTheory.ConjInfExp

namespace GlobalTheory.ConjInfExp

open GlobalTheory.FockCompare GlobalTheory.AdelicU


set_option maxHeartbeats 1000000 in
theorem hasExp_conj_of_hasInfExp : ∀ {D : D7} (c : (AE D)ˣ →* Circle) (a : D.what₂.Tau → ℚ), (∀ τ, HasInfExp D c τ (a τ)) →
    ∀ (τf : InfinitePlace D.host.F → D.what₂.Tau)
    (hτf : ∀ w, ((starRingEnd ℂ).comp (tauE D (τf w))).comp (algebraMap D.host.F D.host.E) = w.embedding),
    ∃ m : InfinitePlace D.host.F → ℤ,
      HasExp (fun w => ⟨(starRingEnd ℂ).comp (tauE D (τf w)), hτf w⟩) c m ∧ ∀ w, (m w : ℚ) = -2 * a (τf w) := by
  intro D c a ha τf hτf
  choose n hn hθ using ha
  refine ⟨fun w => -n (τf w), ?_, fun w => by push_cast; rw [hn]; ring⟩
  intro z hz
  have hf : finPart D (z : AE D) = 1 := finPart_eq_one _ hz
  obtain ⟨⟨θ', hθ'⟩, -⟩ := GlobalTheory.Member.infiniteAdele_bijective D
  let θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) := fun τ => θ' (tauE D τ)
  have hθ0 : IsInfFam θ := fun τ => hθ' _
  obtain ⟨ρ, hρ, r1, r0⟩ := exists_real_chart D θ hθ0 (GlobalTheory.CMTypePlaces.places_bijective D)
  obtain ⟨s, hs⟩ := RealChart.exists_chart D θ hθ0 ρ hρ r1 r0
  have ext : ∀ a b : AE D, finPart D a = finPart D b → (∀ τ, θ τ (infPart D a) = θ τ (infPart D b)) → a = b := by
    intro a b h1 h2
    rw [← sub_eq_zero]
    exact hs.ext _ (by rw [RingHom.map_sub, h1, sub_self]) fun τ => by
      rw [RingHom.map_sub, RingHom.map_sub, h2, sub_self]
  let t : (D.what₂.Tau → ℂˣ) → AE D := fun z => s (fun τ => (z τ : ℂ)) + (1 - s 1)
  have tf : ∀ z, finPart D (t z) = 1 := fun z => by
    simp only [t, RingHom.map_add (f := _), RingHom.map_sub, RingHom.map_one, hs.fin, zero_add, sub_zero]
  have ti : ∀ z τ, θ τ (infPart D (t z)) = z τ := fun z τ => by
    simp only [t, RingHom.map_add (f := _), RingHom.map_sub, RingHom.map_one, hs.comp, Pi.one_apply, sub_self, add_zero]
  let T : (D.what₂.Tau → ℂˣ) →* AE D :=
    { toFun := t
      map_one' := ext _ _ (by rw [tf, RingHom.map_one]) fun τ => by
        rw [ti, RingHom.map_one, RingHom.map_one]; rfl
      map_mul' := fun x y => ext _ _ (by rw [RingHom.map_mul, tf, tf, tf, mul_one]) fun τ => by
        rw [RingHom.map_mul, RingHom.map_mul, ti, ti, ti]; rfl }
  let zx : D.what₂.Tau → ℂˣ := fun τ => Units.map ((θ τ).comp (infPart D)).toMonoidHom z
  have hzx : ∀ τ, ((zx τ : ℂˣ) : ℂ) = θ τ (infPart D (z : AE D)) := fun τ => rfl
  have hT : z = T.toHomUnits zx :=
    Units.ext (ext _ _ (hf.trans (tf _).symm) fun τ => (ti zx τ).symm)
  have single : ∀ τ (v : ℂˣ), ((c (T.toHomUnits (Pi.mulSingle τ v)) : Circle) : ℂ) =
      ((v : ℂ) / ((‖(v : ℂ)‖ : ℝ) : ℂ)) ^ n τ := by
    intro τ v
    have h := (hθ τ).2 θ hθ0 (T.toHomUnits (Pi.mulSingle τ v)) (tf _) fun τ' hτ' => by
      show θ τ' (infPart D (t _)) = 1
      rw [ti, Pi.mulSingle_eq_of_ne hτ', Units.val_one]
    rw [h]
    show ((θ τ (infPart D (t _))) / ((‖θ τ (infPart D (t _))‖ : ℝ) : ℂ)) ^ n τ = _
    rw [ti, Pi.mulSingle_eq_same]
  have hprod : ((c z : Circle) : ℂ) = ∏ τ, ((zx τ : ℂ) / ((‖(zx τ : ℂ)‖ : ℝ) : ℂ)) ^ n τ := by
    have e1 : T.toHomUnits zx = ∏ τ, T.toHomUnits (Pi.mulSingle τ (zx τ)) := by
      rw [← map_prod]; congr 1; exact (Finset.univ_prod_mulSingle zx).symm
    have e2 : ((c z : Circle) : ℂ) = Circle.coeHom (∏ τ, c (T.toHomUnits (Pi.mulSingle τ (zx τ)))) := by
      rw [← map_prod, ← e1, ← hT]; rfl
    rw [e2, map_prod]
    exact Finset.prod_congr rfl fun τ _ => single τ (zx τ)
  have hinj : Function.Injective τf := fun w1 w2 h => by
    have e : w1.embedding = w2.embedding := by rw [← hτf w1, ← hτf w2, h]
    rw [← InfinitePlace.mk_embedding w1, ← InfinitePlace.mk_embedding w2, e]
  have hbij : Function.Bijective τf := (Fintype.bijective_iff_injective_and_card τf).2
    ⟨hinj, (Fintype.card_of_bijective (GlobalTheory.CMTypePlaces.places_bijective D)).symm⟩
  rw [hprod]
  symm
  refine Fintype.prod_bijective τf hbij _ _ fun w => ?_
  beta_reduce
  rw [piInf_eq θ hθ0 (τf w) w (hτf w), ← hzx]
  exact conj_div_norm_zpow _ (zx (τf w)).ne_zero _

end GlobalTheory.ConjInfExp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCompactSupportFinprodSchwartzBruhatFiniteAdel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

namespace GlobalTheory.AdelicCoordSupport

theorem hasCompactSupport_finprod : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (φ : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), (κ → Fv F v) → ℂ), (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) →
    (∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) →
    HasCompactSupport (fun y : κ → FiniteAdeleRing (𝓞 F) F => ∏ᶠ v, φ v fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i)) := by
  intro F _ _ κ _ φ hSB hae
  classical
  let L : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), Set (κ → Fv F v) :=
    fun v => {x | ∀ i, x i ∈ v.adicCompletionIntegers F}
  have hLc : ∀ v, IsClosed (L v) := fun v => by
    have e : L v = Set.pi Set.univ fun _ => (v.adicCompletionIntegers F : Set (Fv F v)) := by
      ext x; simp [L]
    rw [e]
    exact isClosed_set_pi fun _ _ => (ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isCompact_integers v).isClosed
  have hint : ∀ y : κ → FiniteAdeleRing (𝓞 F) F, ∀ᶠ v in Filter.cofinite,
      (fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i)) ∈ L v := fun y =>
    Filter.eventually_all.2 fun i => (y i).2
  have hfac : ∀ y : κ → FiniteAdeleRing (𝓞 F) F,
      (∏ᶠ v, φ v fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i)) ≠ 0 →
      ∀ v, φ v (fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i)) ≠ 0 := by
    intro y h v
    have hfin : (Function.mulSupport fun v => φ v fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i)).Finite := by
      refine (Filter.eventually_cofinite.1 (hae.and (hint y))).subset ?_
      intro w hw h'
      apply hw
      simp only
      rw [h'.1, Set.indicator_of_mem h'.2]
      rfl
    rw [finprod_eq_prod _ hfin] at h
    by_cases hv : v ∈ hfin.toFinset
    · exact Finset.prod_ne_zero_iff.1 h v hv
    · rw [Set.Finite.mem_toFinset, Function.mem_mulSupport, not_not] at hv
      rw [hv]
      exact one_ne_zero
  let D : κ → ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), Set (Fv F v) := fun i v =>
    ((fun Z : κ → Fv F v => Z i) '' tsupport (φ v)) ∪ (v.adicCompletionIntegers F : Set (Fv F v))
  have hD : ∀ i v, IsCompact (D i v) := fun i v =>
    ((hSB v).2.isCompact.image (continuous_apply i)).union (ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isCompact_integers v)
  have hDe : ∀ i, ∀ᶠ v in Filter.cofinite,
      D i v = (v.adicCompletionIntegers F : Set (Fv F v)) := by
    intro i
    filter_upwards [hae] with v hv
    refine Set.union_eq_right.2 ?_
    rintro _ ⟨Z, hZ, rfl⟩
    have hsub : tsupport (φ v) ⊆ L v := by
      rw [hv]
      exact closure_minimal Set.support_indicator_subset (hLc v)
    exact hsub hZ i
  let Box : Set (κ → FiniteAdeleRing (𝓞 F) F) :=
    Set.pi Set.univ fun i => {x | ∀ v, x v ∈ D i v}
  have hbox : IsCompact Box :=
    isCompact_univ_pi fun i => PI.VolStabS.AdmissibleCompactSupport.isCompact_finBox (hD i) (hDe i)
  refine HasCompactSupport.intro hbox fun y hy => ?_
  by_contra h
  apply hy
  intro i _ v
  exact Or.inl ⟨_, subset_tsupport _ (hfac y h v), rfl⟩

end GlobalTheory.AdelicCoordSupport
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasHermitianSignatureComplementHyperbolicPlane
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

noncomputable section

namespace GlobalTheory.PlaneSig

open Matrix

theorem hasSig_map_conj_of_hasSignature {n r s : ℕ} {G : Matrix (Fin n) (Fin n) ℂ}
    (h : Formalism.UG.HasSignature G r s) : HasSig (G.map (starRingEnd ℂ)) r s := by
  obtain ⟨e, P, hP⟩ := h
  have hc := Fintype.card_congr e
  simp only [Fintype.card_sum, Fintype.card_fin] at hc
  refine ⟨hc.symm, (P : Matrix _ _ ℂ).submatrix e id, ?_⟩
  have hG : G.map (starRingEnd ℂ) = ((G.map (starRingEnd ℂ)).submatrix e.symm e.symm).submatrix e e := by
    ext i j; simp
  have hL : ((P : Matrix _ _ ℂ).submatrix e id)ᵀ * G.map (starRingEnd ℂ) * ((P : Matrix _ _ ℂ).submatrix e id).map star =
      ((P : Matrix _ _ ℂ)ᵀ * (G.map (starRingEnd ℂ)).submatrix e.symm e.symm * (P : Matrix _ _ ℂ).map star) := by
    conv_lhs => rw [hG, transpose_submatrix, submatrix_mul_equiv, ← Matrix.submatrix_map, submatrix_mul_equiv,
      submatrix_id_id]
  have h3 : (P : Matrix _ _ ℂ)ᵀ * (G.map (starRingEnd ℂ)).submatrix e.symm e.symm * (P : Matrix _ _ ℂ).map star =
      (Formalism.UG.cT (starRingEnd ℂ) (P : Matrix _ _ ℂ) * G.reindex e e * (P : Matrix _ _ ℂ)).map (starRingEnd ℂ) := by
    ext i j; simp [Matrix.mul_apply, map_sum, Formalism.UG.cT]
  rw [hL, h3, hP]
  ext (a | a) (b | b) <;> simp [Formalism.UG.Jpq, Matrix.one_apply] <;> split_ifs <;> simp

theorem gram_conj {k l : Type} [Fintype k] [Fintype l] {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ)
    (A : Matrix (Fin n) k ℂ) (B : Matrix (Fin n) l ℂ) :
    Aᴴ * M.map (starRingEnd ℂ) * B = (Aᵀ * M * B.map star).map (starRingEnd ℂ) := by
  ext i j; simp [Matrix.mul_apply, map_sum, Finset.sum_mul]

abbrev colM {n : ℕ} (x : Fin n → ℂ) : Matrix (Fin n) (Fin 1) ℂ := Matrix.of fun i _ => x i

theorem gram_col {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (x y : Fin n → ℂ) :
    (colM x)ᵀ * M * (colM y).map star = Matrix.of fun _ _ => x ⬝ᵥ M *ᵥ star y := by
  ext i j
  simp [Matrix.mul_apply, dotProduct, mulVec, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  exact Finset.sum_comm

theorem gram_col_right {n m : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (ι : Matrix (Fin n) (Fin m) ℂ) (x : Fin n → ℂ) :
    ιᵀ * M * (colM x).map star = Matrix.of fun j _ => (ιᵀ *ᵥ (M *ᵥ star x)) j := by
  ext i j
  simp [Matrix.mul_apply, dotProduct, mulVec, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  exact Finset.sum_comm

theorem hasSig_complement_plane : ∀ (n n₁ : ℕ) (M : Matrix (Fin n) (Fin n) ℂ) (X Yv : Fin n → ℂ) (ι : Matrix (Fin n) (Fin n₁) ℂ)
    (P : Matrix (Fin n₁) (Fin n) ℂ) (r s : ℕ), n = n₁ + 2 → Mᴴ = M →
    X ⬝ᵥ M *ᵥ star X = 0 → Yv ⬝ᵥ M *ᵥ star Yv = 0 → X ⬝ᵥ M *ᵥ star Yv = 1 →
    ιᵀ *ᵥ (M *ᵥ star X) = 0 → ιᵀ *ᵥ (M *ᵥ star Yv) = 0 → P * ι = 1 →
    HasSig M r s → HasSig (ιᵀ * M * ι.map star) (r - 1) (s - 1) := by
  intro n n₁ M X Yv ι P r s hn hM hXX hYY hXY hιX hιY hP hs
  set J := M.map (starRingEnd ℂ) with hJdef
  have hJJ : J.map (starRingEnd ℂ) = M := by ext i j; simp [J]
  have hJ : Jᴴ = J := by
    ext i j
    have := congrFun (congrFun hM i) j
    simp [conjTranspose_apply] at this
    simp [J, conjTranspose_apply, ← this]
  have hJs : Formalism.UG.HasSignature J r s := GlobalTheory.FunObj.hasSignature_of_hasSig_conj (by rw [hJJ]; exact hs)
  set T := colM X
  set T' := colM Yv
  have h1 : Tᴴ * J * T = 0 := by
    rw [gram_conj, gram_col, hXX]; ext i j; simp
  have h2 : T'ᴴ * J * T' = 0 := by
    rw [gram_conj, gram_col, hYY]; ext i j; simp
  have h3 : Tᴴ * J * T' = 1 := by
    rw [gram_conj, gram_col, hXY]; ext i j; fin_cases i; fin_cases j; simp
  have h4' : ιᴴ * J * T = 0 := by
    rw [gram_conj, gram_col_right, hιX]; ext i j; simp
  have h5' : ιᴴ * J * T' = 0 := by
    rw [gram_conj, gram_col_right, hιY]; ext i j; simp
  have h4 : Tᴴ * J * ι = 0 := by rw [GlobalTheory.AdaptedExists.gram_swap hJ, h4', conjTranspose_zero]
  have h5 : T'ᴴ * J * ι = 0 := by rw [GlobalTheory.AdaptedExists.gram_swap hJ, h5', conjTranspose_zero]
  have h3' : T'ᴴ * J * T = 1 := by rw [GlobalTheory.AdaptedExists.gram_swap hJ, h3, conjTranspose_one]
  have hGι : ιᴴ * J * ι = (ιᵀ * M * ι.map star).map (starRingEnd ℂ) := gram_conj M ι ι

  set Q : Matrix (Fin n) ((Fin 1 ⊕ Fin 1) ⊕ Fin n₁) ℂ := fromCols (fromCols T T') ι with hQ
  set L : Matrix ((Fin 1 ⊕ Fin 1) ⊕ Fin n₁) (Fin n) ℂ :=
    fromRows (fromRows (T'ᴴ * J) (Tᴴ * J)) (P * (1 - T * (T'ᴴ * J) - T' * (Tᴴ * J))) with hL
  have hLQ : L * Q = 1 := by
    rw [Matrix.mul_assoc] at h1 h2 h3 h4 h5 h3'
    simp only [hL, hQ, fromRows_mul, mul_fromCols, Matrix.mul_assoc, Matrix.mul_sub, Matrix.sub_mul, Matrix.one_mul,
      Matrix.mul_one, h1, h2, h3, h4, h5, h3', hP, Matrix.mul_zero, sub_zero, sub_self, zero_sub]
    ext ((a | a) | a) ((b | b) | b) <;> simp [Matrix.one_apply]
  obtain ⟨f⟩ : Nonempty (Fin n ≃ (Fin 1 ⊕ Fin 1) ⊕ Fin n₁) := Fintype.card_eq.1 (by simp; omega)
  set Q' : Matrix (Fin n) (Fin n) ℂ := Q.submatrix id f with hQ'
  have hLQ' : L.submatrix f id * Q' = 1 := by
    have := Matrix.submatrix_mul_equiv L Q f (Equiv.refl (Fin n)) f
    rw [hLQ, submatrix_one_equiv] at this
    exact this
  have hdQ : Matrix.det Q' ≠ (0 : ℂ) := Matrix.det_ne_zero_of_left_inverse hLQ'
  have hdM : M.det ≠ 0 := GlobalTheory.LeviUnitary.det_ne_zero_of_hasSig hs
  have hdJ : J.det ≠ 0 := by
    rw [hJdef, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    simpa using hdM
  have hQJQ : Qᴴ * J * Q = fromBlocks (fromBlocks 0 1 1 0) 0 0 (ιᴴ * J * ι) := by
    rw [Matrix.mul_assoc] at h1 h2 h3 h4 h5 h3' h4' h5'
    simp only [hQ, conjTranspose_fromCols_eq_fromRows_conjTranspose, Matrix.mul_assoc, mul_fromCols, fromRows_mul,
      h1, h2, h3, h4, h5, h3', h4', h5']
    ext ((a | a) | a) ((b | b) | b) <;> simp [Matrix.mul_assoc]
  have h6 : (ιᴴ * J * ι).det ≠ 0 := by
    have h7 : (Q'ᴴ * J * Q').det ≠ 0 := by
      rw [det_mul, det_mul, det_conjTranspose]
      exact mul_ne_zero (mul_ne_zero (by simpa using hdQ) hdJ) hdQ
    have h8 : Q'ᴴ * J * Q' = (Qᴴ * J * Q).submatrix f f := by
      ext i j; simp [Q', Matrix.mul_apply]
    have : (Qᴴ * J * Q).det ≠ 0 := by rwa [h8, det_submatrix_equiv_self] at h7
    rw [hQJQ, det_fromBlocks_zero₂₁] at this
    exact right_ne_zero_of_mul this
  have hc := GlobalTheory.AdaptedExists.hasSignature_complement n n₁ r s (Fin 1) J T T' ι hJ hJs (by simp; omega)
    h1 h2 h3 h4 h5 h6
  simp only [Fintype.card_fin] at hc
  have := hasSig_map_conj_of_hasSignature hc
  rwa [hGι, Matrix.map_map, show (starRingEnd ℂ) ∘ (starRingEnd ℂ) = id from funext fun z => Complex.conj_conj z,
    Matrix.map_id] at this

end GlobalTheory.PlaneSig
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasHermitianSignaturePosSmulBlockDiagonalReindex
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open scoped nonZeroDivisors

namespace GlobalTheory.SigBlockSum

lemma cT_eq_conjTranspose {m p : Type} (M : Matrix m p ℂ) :
    Formalism.UG.cT (starRingEnd ℂ) M = Mᴴ := by
  ext i j; simp [Formalism.UG.cT, Matrix.conjTranspose]

def sgn (p q : ℕ) : Fin p ⊕ Fin q → ℂ := Sum.elim (fun _ => 1) (fun _ => -1)

lemma fromBlocks_one_neg_one (p q : ℕ) :
    (Matrix.fromBlocks 1 0 0 (-1) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) = Matrix.diagonal (sgn p q) := by
  ext i j; rcases i with i | i <;> rcases j with j | j <;>
    simp [sgn, Matrix.one_apply, Matrix.diagonal_apply] <;> split_ifs <;> simp

lemma rows_reindex {n : Type} [Fintype n] [DecidableEq n] {p q : ℕ} (G : Matrix n n ℂ) (e : n ≃ Fin p ⊕ Fin q)
    (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)
    (h : Pᴴ * G.reindex e e * P = Matrix.fromBlocks 1 0 0 (-1)) :
    (P.submatrix e id)ᴴ * G * P.submatrix e id = Matrix.diagonal (sgn p q) := by
  have hG : G = (G.reindex e e).submatrix e e := by ext i j; simp
  rw [hG, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, h,
    fromBlocks_one_neg_one]
  simp

def sortCols (pa qa pb qb : ℕ) :
    Fin (pa + pb) ⊕ Fin (qa + qb) ≃ (Fin pa ⊕ Fin qa) ⊕ (Fin pb ⊕ Fin qb) :=
  (Equiv.sumCongr finSumFinEquiv.symm finSumFinEquiv.symm).trans (Equiv.sumSumSumComm _ _ _ _)

lemma sgn_sortCols (pa qa pb qb : ℕ) :
    Sum.elim (sgn pa qa) (sgn pb qb) ∘ sortCols pa qa pb qb = sgn (pa + pb) (qa + qb) := by
  funext x
  rcases x with i | i
  · rcases h : (finSumFinEquiv.symm i : Fin pa ⊕ Fin pb) with k | k <;>
      simp [sortCols, sgn, h]
  · rcases h : (finSumFinEquiv.symm i : Fin qa ⊕ Fin qb) with k | k <;>
      simp [sortCols, sgn, h]

theorem hasSig_smul_blk : ∀ {a b d : ℕ} (e : Fin a ⊕ Fin b ≃ Fin d) (GA : Matrix (Fin a) (Fin a) ℂ) (GB : Matrix (Fin b) (Fin b) ℂ) {pa qa pb qb : ℕ} {κ : ℝ},
    0 < κ → Formalism.UG.HasSignature GA pa qa → Formalism.UG.HasSignature GB pb qb →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.HasSig ((κ : ℂ) • GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e GA GB) (pa + pb) (qa + qb) := by
  intro a b d e GA GB pa qa pb qb κ hκ hA hB
  obtain ⟨eA, PA, hPA⟩ := hA
  obtain ⟨eB, PB, hPB⟩ := hB
  rw [cT_eq_conjTranspose] at hPA hPB
  have hQA := rows_reindex GA eA _ hPA
  have hQB := rows_reindex GB eB _ hPB
  set QA := (PA : Matrix (Fin pa ⊕ Fin qa) (Fin pa ⊕ Fin qa) ℂ).submatrix eA id
  set QB := (PB : Matrix (Fin pb ⊕ Fin qb) (Fin pb ⊕ Fin qb) ℂ).submatrix eB id
  have hca : a = pa + qa := by simpa using Fintype.card_congr eA
  have hcb : b = pb + qb := by simpa using Fintype.card_congr eB
  have hcd : a + b = d := by simpa using Fintype.card_congr e
  let τ := sortCols pa qa pb qb
  let Q0 : Matrix (Fin a ⊕ Fin b) ((Fin pa ⊕ Fin qa) ⊕ (Fin pb ⊕ Fin qb)) ℂ := Matrix.fromBlocks QA 0 0 QB
  let Q : Matrix (Fin d) (Fin (pa + pb) ⊕ Fin (qa + qb)) ℂ := Q0.submatrix e.symm τ
  have hQ : Qᴴ * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e GA GB * Q = Matrix.fromBlocks 1 0 0 (-1) := by
    have h0 : Q0ᴴ * Matrix.fromBlocks GA 0 0 GB * Q0 =
        Matrix.diagonal (Sum.elim (sgn pa qa) (sgn pb qb)) := by
      simp only [Q0, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]
      simp [hQA, hQB, Matrix.fromBlocks_diagonal]
    have hb : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e GA GB = (Matrix.fromBlocks GA 0 0 GB).submatrix e.symm e.symm := rfl
    rw [hb, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, h0,
      Matrix.submatrix_diagonal_equiv, sgn_sortCols, fromBlocks_one_neg_one]
  refine ⟨by omega, ((((Real.sqrt κ)⁻¹ : ℝ) : ℂ)) • Q.map star, ?_⟩
  set c : ℂ := (((Real.sqrt κ)⁻¹ : ℝ) : ℂ)
  have h1 : (c • Q.map star)ᵀ = c • Qᴴ := by
    ext i j; simp [Matrix.conjTranspose]
  have h2 : (c • Q.map star).map star = c • Q := by
    ext i j; simp [c, Complex.conj_ofReal]
  have h3 : c * (κ : ℂ) * c = 1 := by
    have hs : Real.sqrt κ ≠ 0 := (Real.sqrt_pos.2 hκ).ne'
    have : (Real.sqrt κ)⁻¹ * κ * (Real.sqrt κ)⁻¹ = 1 := by
      field_simp; nlinarith [Real.mul_self_sqrt hκ.le, Real.sq_sqrt hκ.le]
    simp only [c]; exact_mod_cast this
  rw [h1, h2]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hQ]
  convert one_smul ℂ (Matrix.fromBlocks 1 0 0 (-1) : Matrix (Fin (pa + pb) ⊕ Fin (qa + qb)) (Fin (pa + pb) ⊕ Fin (qa + qb)) ℂ) using 2
  linear_combination h3

end GlobalTheory.SigBlockSum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSquaringPathsRigidDescendsFieldMapStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalSquaringPathsRigid_descends_field_map : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], ∀ (F Ω : Type) [Field F] [Field Ω] (φ : F →+* Ω) (b : Sp F ⟶ S), RatRigid G (spMap φ ≫ b) → RatRigid G b := by
  first | exact @GlobalTheory.Nef.ratRigid_of_field_map | exact GlobalTheory.Nef.ratRigid_of_field_map | (intros; apply GlobalTheory.Nef.ratRigid_of_field_map <;> assumption)
end

