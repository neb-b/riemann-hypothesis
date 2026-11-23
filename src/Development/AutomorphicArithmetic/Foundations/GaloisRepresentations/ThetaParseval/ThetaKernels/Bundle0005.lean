module

public import Development.WeilBound.ThetaLifts.TowerModels.TwistedSums.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1422
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumTwistByHeckeCharactersTrivialBase
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.PrSingle
public import Development.WeilBound.CoreStatements.AutomorphicKernels.ArchimedeanJacquetFirstTerm.ArchimedeanWhittakerTrace.LZfcCore
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1475
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1489

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ExistsRationalDarbouxK
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace Tw.RatDarboux
open _root_.GlobalTheory
section General
open scoped TensorProduct
open Matrix Module GlobalTheory.WeilM
variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
variable (R : Type) [CommRing R] [Algebra F R]
end General
end Tw.RatDarboux
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory in
theorem Tw.RatDarboux.exists_rational_darboux_k : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    {n d : ℕ} (X : Spc F E n) (Y : Spc F E d) (r s r' s' : ℕ), _root_.UpperTheory.TP.W.GoodK σ B → X.IsHerm σ B r s → Y.IsSkew σ B r' s' →
    ∃ co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (-1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J)) (Fin n × Fin d),
      ∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F,
        co.e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F x) = (fun k => algebraMap F (AF F) (y k), fun k => algebraMap F (AF F) (z k)) := by
  intro F E _ _ _ _ _ σ B n d X Y r s r' s' hB hX hY
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hσ : ∀ x, σ (σ x) = x := fun x => by
    apply ((B.emb w).1 : E →+* ℂ).injective
    rw [hB.cm.2.2.2, hB.cm.2.2.2, star_star]
  have hX' : X.J.det ≠ 0 := fun h0 => by
    apply Tw.RatDarboux.det_ne_zero_of_isCartan (hX.cartan w)
    have := ((B.emb w).1 : E →+* ℂ).map_det X.J
    rw [h0, map_zero] at this
    exact this.symm
  have hY' : Y.J.det ≠ 0 := fun h0 => by
    apply Tw.RatDarboux.det_ne_zero_of_isCartan (hY.cartan w)
    have := ((B.emb w).1 : E →+* ℂ).map_det Y.J
    rw [h0, map_zero] at this
    rw [Matrix.det_smul]
    exact mul_eq_zero_of_right _ this.symm
  exact Tw.RatDarboux.exists_darboux (AF F) hB.cm.2.2.1 σ hσ hX.herm hY.skew hX' hY'
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ExistsWeilCharK
section
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
noncomputable section
namespace GlobalTheory.WeilTypeChar
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
theorem exists_weil_char_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∃ ξ : (AF F ⊗[F] E)ˣ →* Circle, IsHeckeCharF ξ ∧ HasExp B.emb ξ (fun _ => 1) := by
  intro F E _ _ _ _ _ σ B hB
  haveI : IsCMField E := isCMField_of_cmExt hB.cm
  haveI : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  obtain ⟨q, hq1, hq⟩ := Nat.exists_infinite_primes (max 3 (Nat.card (Units.torsion E) + 1))
  have hq2 : 2 < q := by omega
  have htq : Nat.card (Units.torsion E) < q := by omega
  have ht : ¬ q ∣ Nat.card (Units.torsion E) := fun h => absurd (Nat.le_of_dvd Nat.card_pos h) (by omega)
  obtain ⟨U, hU, hUinf, hUk⟩ := _root_.GlobalTheory.OpenCongrIdele.exists_open_congr F E q hq.ne_zero
  obtain ⟨χ, hχc, hχ1, hχU, hχk⟩ := GlobalTheory.exists_unitary_char_of_open_subgroup_and_hom (AF F ⊗[F] E)ˣ Eˣ U hU
    (Units.map (incAF F E).toMonoidHom) 1 (chiInf B.emb) (continuous_chiInf B.emb) (norm_chiInf B.emb)
    (fun _ => by simp) (fun k hk => by
      obtain ⟨u, hu, hu1⟩ := hUk k hk
      refine Units.ext ?_
      rw [chiInf_apply, MonoidHom.one_apply, Units.val_one]
      have e : ∀ w, piInf (B.emb w) ((Units.map (incAF F E).toMonoidHom k : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) =
          (B.emb w).1 ((u : 𝓞 E) : E) := fun w => by
        rw [hu]
        exact GlobalTheory.ThK.EvAt0.ZPartArc.piInf_inclR' (B.emb w) (k : E)
      simp only [e]
      exact (_root_.GlobalTheory.weil_unit_phase_prod F E σ hB.cm B.emb q hq hq2 ht u hu1).symm)
  refine ⟨GlobalTheory.unitaryCharToCircle χ hχ1, ⟨?_, fun k => ?_⟩, fun z hz => ?_⟩
  · exact Continuous.subtype_mk (Units.continuous_val.comp hχc) _
  · apply Circle.ext
    show ((χ (Units.map (incAF F E).toMonoidHom k) : ℂˣ) : ℂ) = 1
    rw [hχk]; rfl
  · show ((χ z : ℂˣ) : ℂ) = _
    rw [hχU z (hUinf z hz), chiInf_apply]
    simp
end GlobalTheory.WeilTypeChar
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ExistsWeilDatumOFTwistK
section
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix Topology
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
noncomputable section
namespace GlobalTheory.WeilTwistF
open MeasureTheory
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {n : ℕ} {J : Matrix (Fin n) (Fin n) E}
end GlobalTheory.WeilTwistF
namespace GlobalTheory.WeilTwistF
open MeasureTheory
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {n : ℕ} {J : Matrix (Fin n) (Fin n) E}
end GlobalTheory.WeilTwistF
namespace GlobalTheory.WeilTwistF
open MeasureTheory
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E}
theorem exists_weilDatumOF_twist_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (χS χT νS νT : (AF F ⊗[F] E)ˣ →* Circle) ω,
        IsWeilDatumOF σ JS JT (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS χT ω →
        IsHeckeCharF νS → IsHeckeCharF νT → ResEtaF νS 0 → ResEtaF νT 0 →
        ∃ ω', IsWeilDatumOF σ JS JT (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ (χS * νS) (χT * νT) ω' := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ hξσ χS χT νS νT om ho hνS hνT rS rT
  have hcm := hB.cm
  have hun := hB.unram
  obtain ⟨a, aval, arat, acont⟩ := exists_muF (σ := σ) hcm hun hS.2 νT⁻¹ (heckeF_inv hνT)
    (fun t => by rw [MonoidHom.inv_apply, triv_of_resEtaF rT, inv_one])
  obtain ⟨b, bval, brat, bcont⟩ := exists_muF (σ := σ) hcm hun hT.2 νS hνS (triv_of_resEtaF rS)
  let om' : GAF σ JS × GAF σ JT →* Module.End ℂ (WOF F E nS nT → ℂ) :=
    { toFun := fun p => ((a p.1 * b p.2 : Circle) : ℂ) • om p
      map_one' := by simp
      map_mul' := fun p q => by
        simp only [Prod.fst_mul, Prod.snd_mul, map_mul, smul_mul_smul_comm, Circle.coe_mul]
        congr 1
        ring }
  have happ : ∀ p f, om' p f = ((a p.1 * b p.2 : Circle) : ℂ) • om p f := fun p f => rfl
  have hval : ∀ g h x y, IsRootF σ JS g x → IsRootF σ JT h y →
      ((a g * b h : Circle) : ℂ) = (((νT x)⁻¹ * νS y : Circle) : ℂ) := by
    intro g h x y hx hy
    rw [aval g x hx, bval h y hy, MonoidHom.inv_apply]
  refine ⟨om', ⟨ho.std, heckeF_mul ho.hecS hνS, heckeF_mul ho.hecT hνT, resEtaF_mul ho.resS rS,
    resEtaF_mul ho.resT rT, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro p f hf
    rw [happ]
    exact thetaOF_smul _ (ho.om_pres p f hf)
  · intro g h w₀ f hf
    rw [happ, happ, heisOF_smul, ho.om_heis g h w₀ f hf]
  · intro γ hγ γ' hγ' f hf
    rw [happ]
    change ((a γ * b γ' : Circle) : ℂ) * om (γ, γ') f 0 = f 0
    rw [arat γ hγ, brat γ' hγ', mul_one, Circle.coe_one, one_mul]
    exact ho.om_aut γ hγ γ' hγ' f hf
  · intro f hf w
    exact (continuous_subtype_val.comp ((acont.comp continuous_fst).mul (bcont.comp continuous_snd))).mul
      (ho.om_cont f hf w)
  · intro μ 𝓕 hμ h𝓕 p f hf
    rw [← ho.om_unit μ 𝓕 hμ h𝓕 p f hf]
    refine lintegral_congr fun w => ?_
    have hn : ‖om' p f w‖ = ‖om p f w‖ := by
      rw [happ, Pi.smul_apply, smul_eq_mul, norm_mul, Circle.norm_coe, one_mul]
    rw [← ofReal_norm, ← ofReal_norm, hn]
  · intro e he g h hg hh x y hx hy
    obtain ⟨r, hr, H⟩ := ho.om_split e he g h hg hh x y hx hy
    refine ⟨r, hr, fun ℓ hℓ f hf => ?_⟩
    rw [happ, map_smul, H ℓ hℓ f hf,
      hval g h x y (root_of_detAt hS.2 he g hg x hx) (root_of_detAt hT.2 he h hh y hy)]
    simp only [splitFacOF, MonoidHom.mul_apply, mul_inv, Circle.coe_mul, smul_eq_mul]
    ring
end GlobalTheory.WeilTwistF
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.FinjK
section
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
noncomputable section
namespace PositivityTheory.ThKW.LagrangianProjectionFormula
open PositivityTheory.ThKW.ModulusFactorDefinition PositivityTheory.ThKW.ModulusDerivativeNormalisation PositivityTheory.ThKW.PhaseFourierInjectivity
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
end PositivityTheory.ThKW.LagrangianProjectionFormula
end
open PositivityTheory.ThKW.ModulusFactorDefinition PositivityTheory.ThKW.ModulusDerivativeNormalisation PositivityTheory.ThKW.PhaseFourierInjectivity PositivityTheory.ThKW.LagrangianProjectionFormula in
theorem PositivityTheory.ThKW.PhaseFourierInjectivity.finj_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), ν.IsAddHaarMeasure →
        IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν →
    ∀ N₁ N₂ : WOF F E nS nT → ℂ, Continuous N₁ → Continuous N₂ → Integrable N₁ ν → Integrable N₂ ν →
      (∀ y, ∫ v, phase σ JS JT ξ₀ B.ψ y v * N₁ v ∂ν = ∫ v, phase σ JS JT ξ₀ B.ψ y v * N₂ v ∂ν) → N₁ = N₂ := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ₀ hσ ν 𝓕 hν h𝓕 N₁ N₂ c₁ c₂ i₁ i₂ hN
  have hψ : IsStd B.ψ := hB.std
  have hψn : ∀ a, ‖B.ψ a‖ = 1 := GlobalTheory.StdCharWeilDatum.norm_psi hB.std
  have hcc : ∀ z : AF F ⊗[F] E, cAF σ (cAF σ z) = z :=
    GlobalTheory.HeisLineF.cAF_cAF σ (GlobalTheory.SplitDetCharF.sig_invol hB.cm)
  have he : Continuous (vecE F E nS nT) := by
    show Continuous fun (w : WOF F E nS nT) (k : Fin (nT * nS)) => w (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2
    exact continuous_pi fun k => continuous_id.matrix_elem _ _
  have he' : Continuous (vecE F E nS nT).symm := by
    show Continuous fun (u : Fin (nT * nS) → AF F ⊗[F] E) =>
      ((fun i j => u (finProdFinEquiv (i, j))) : WOF F E nS nT)
    first
      | exact continuous_pi fun i => continuous_pi fun j => continuous_apply _
      | fun_prop
  haveI : IsTopologicalAddGroup (AF F ⊗[F] E) := IsModuleTopology.topologicalAddGroup (AF F) (AF F ⊗[F] E)
  let E' : WOF F E nS nT ≃ₜ+ (Fin (nT * nS) → AF F ⊗[F] E) :=
    { toAddEquiv := vecE F E nS nT, continuous_toFun := he, continuous_invFun := he' }
  letI : MeasurableSpace (Fin (nT * nS) → AF F ⊗[F] E) := borel _
  haveI : BorelSpace (Fin (nT * nS) → AF F ⊗[F] E) := ⟨rfl⟩
  haveI : BorelSpace (WOF F E nS nT) := ⟨rfl⟩
  let em : WOF F E nS nT ≃ᵐ (Fin (nT * nS) → AF F ⊗[F] E) := E'.toHomeomorph.toMeasurableEquiv
  haveI := hν
  have hμ : (ν.map em).IsAddHaarMeasure := ContinuousAddEquiv.isAddHaarMeasure_map ν E'
  have hpc : ∀ a : WOF F E nS nT, Continuous (pr σ JS ξ₀ a) := fun a => IsModuleTopology.continuous_of_linearMap _
  have hph : ∀ a, Continuous (phase σ JS JT ξ₀ B.ψ a) := by
    intro a
    have e : phase σ JS JT ξ₀ B.ψ a = fun v => B.ψ (pr σ JS ξ₀ a (vecE F E nS nT v)) :=
      funext fun v => phase_eq σ JS JT hT.2 ξ₀ B.ψ a v
    rw [e]
    exact hψ.1.comp ((hpc a).comp he)
  have hint : ∀ a (N : WOF F E nS nT → ℂ), Integrable N ν →
      Integrable (fun v => phase σ JS JT ξ₀ B.ψ a v * N v) ν := by
    intro a N hNi
    refine hNi.bdd_mul (c := 1) (hph a).aestronglyMeasurable (Filter.Eventually.of_forall fun v => ?_)
    rw [phase_eq σ JS JT hT.2, hψn]
  set N : (Fin (nT * nS) → AF F ⊗[F] E) → ℂ := fun u => N₁ ((vecE F E nS nT).symm u) - N₂ ((vecE F E nS nT).symm u)
    with hNdef
  have hNc : Continuous N := (c₁.comp he').sub (c₂.comp he')
  have hNi : Integrable N (ν.map em) := by
    rw [integrable_map_equiv em N]
    have : N ∘ em = fun v => N₁ v - N₂ v := by
      funext v
      simp only [hNdef, Function.comp_apply]
      rw [show (vecE F E nS nT).symm (em v) = v from (vecE F E nS nT).symm_apply_apply v]
    rw [this]
    exact i₁.sub i₂
  have key : ∀ a, ∫ u, B.ψ (pr σ JS ξ₀ a u) * N u ∂(ν.map em) = 0 := by
    intro a
    rw [integral_map_equiv em]
    have hx : ∀ v, B.ψ (pr σ JS ξ₀ a (em v)) * N (em v) =
        phase σ JS JT ξ₀ B.ψ a v * N₁ v - phase σ JS JT ξ₀ B.ψ a v * N₂ v := by
      intro v
      have h1 : (vecE F E nS nT).symm (em v) = v := (vecE F E nS nT).symm_apply_apply v
      have h2 : em v = vecE F E nS nT v := rfl
      simp only [hNdef, h2, AddEquiv.symm_apply_apply]
      rw [phase_eq σ JS JT hT.2]
      ring
    simp_rw [hx]
    rw [integral_sub (hint a N₁ i₁) (hint a N₂ i₂), hN a, sub_self]
  have h0 := GlobalTheory.T.eq_zero_of_adelicFourier_separatingChars_vanish F E B.ψ hψ (nT * nS) (WOF F E nS nT) (pr σ JS ξ₀) (pr_add σ JS ξ₀)
    (fun u hu => pr_sep σ hcc hψ JS hS.2 ξ₀ hξ₀ u hu) (ν.map em) hμ N hNc hNi key
  funext v
  have := congrFun h0 (vecE F E nS nT v)
  simp only [hNdef, AddEquiv.symm_apply_apply, Pi.zero_apply] at this
  exact sub_eq_zero.1 this
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.FirstTermPLZfcCore
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.Dbl PositivityTheory.SiegelWeilFormula
namespace PositivityTheory.FTA.ZFC
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
variable {Y : Spc F E n}
theorem chr_ker_k {B : Base F E} (hB : _root_.UpperTheory.TP.W.GoodK σ B) {b : GL (Fin n ⊕ Fin n) E} (hb : IsFrame2 σ Y b)
    (β : nA σ Y b) : (∀ T : nF σ Y b, chr B.ψ b T β = 1) ↔ β ∈ nF σ Y b := by
  have hσ : ∀ a, σ (σ a) = a := GlobalTheory.LeviLine.sigma_invol hB.cm
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hB.cm.2.2.1]; norm_num)
  obtain ⟨ε, hε⟩ := hb.1
  have hβ : β.1 ∈ PositivityTheory.SiegelWeilFormula.kfour.nCond σ n ε := (PositivityTheory.SiegelWeilFormula.kfour.mem_nA_iff hσ hε β.1).1 β.2
  constructor
  · intro h
    refine (PositivityTheory.SiegelWeilFormula.kfour.mem_nF_iff β).2 (rat_of_ker hB.cm hB.std ε β.1 ?_ fun T hT => ?_)
    · have e := hβ
      simp only [PositivityTheory.SiegelWeilFormula.kfour.nCond, AddSubgroup.mem_mk, ] at e
      rw [e, Int.cast_smul_eq_zsmul]
    · have hm : incM F T ∈ nA σ Y b := by
        refine (PositivityTheory.SiegelWeilFormula.kfour.mem_nA_iff hσ hε _).2 ?_
        show (incM F T)ᵀ = -((((ε : ℤ) : AE F E)) • (incM F T).map (cA σ))
        rw [Int.cast_smul_eq_zsmul, ← incM_map_cA]
        ext i j
        have := congrFun (congrFun hT i) j
        simp only [Matrix.transpose_apply, Matrix.neg_apply, Matrix.smul_apply, Matrix.map_apply] at this ⊢
        simp only [incM, Matrix.map_apply, this, map_neg, map_zsmul]
      have hT' : (⟨incM F T, hm⟩ : nA σ Y b) ∈ nF σ Y b := (PositivityTheory.SiegelWeilFormula.kfour.mem_nF_iff _).2 ⟨T, rfl⟩
      exact h ⟨⟨incM F T, hm⟩, hT'⟩
  · intro hβF T
    obtain ⟨T₀, hT₀⟩ := (PositivityTheory.SiegelWeilFormula.kfour.mem_nF_iff β).1 hβF
    obtain ⟨T₁, hT₁⟩ := (PositivityTheory.SiegelWeilFormula.kfour.mem_nF_iff T.1).1 T.2
    unfold chr
    rw [hT₀, hT₁, ← incM_mul, trace_incM_rat, ← map_neg]
    exact hB.std.2.1 _
theorem fc_inj_pt_per_k {B : Base F E} (hB : _root_.UpperTheory.TP.W.GoodK σ B) (b : GL (Fin n ⊕ Fin n) E) (nb : nA σ Y b → G2 σ Y)
    (lam : Measure (nA σ Y b)) (𝓖 : Set (nA σ Y b)) (hb : IsFrame2 σ Y b) (hc : CoefData (σ := σ) (Y := Y) b nb lam 𝓖)
    (f : G2 σ Y → ℂ) (hf : Continuous f) (hper : ∀ β ∈ nF σ Y b, ∀ g, f (nb β * g) = f g) (x : G2 σ Y)
    (hx : ∀ T : nF σ Y b, fc B.ψ b nb lam 𝓖 f T x = 0) : f x = 0 := by
  obtain ⟨hnb, hlam, hFD, -⟩ := hc
  have hσ : ∀ a, σ (σ a) = a := GlobalTheory.LeviLine.sigma_invol hB.cm
  obtain ⟨i1, i2, i3, i4⟩ := PositivityTheory.SiegelWeilFormula.kfour.nA_top hσ hb
  obtain ⟨K, hK, hcov⟩ := PositivityTheory.SiegelWeilFormula.kfour.nF_cocompact hσ hb
  have hψ := GlobalTheory.StdCharFromIsStd.isCharAF hB.std
  have htr : Continuous (Algebra.trace (AF F) (AE F E)) := IsModuleTopology.continuous_of_linearMap _
  have key := GlobalTheory.SeparatingCharacters.eq_zero_of_coefficients_eq_zero (nA σ Y b) (nF σ Y b) K hK hcov
    (nF σ Y b) (chr B.ψ b)
    (fun T => hψ.1.comp (htr.comp ((continuous_const.matrix_mul continuous_subtype_val).matrix_trace)).neg)
    (fun T β β' => by
      unfold chr
      rw [AddSubgroup.coe_add, Matrix.mul_add, Matrix.trace_add, map_add (f := _), neg_add, AddChar.map_add_eq_mul])
    (fun T T' β => by
      unfold chr
      rw [AddSubgroup.coe_add, AddSubgroup.coe_add, Matrix.add_mul, Matrix.trace_add, map_add (f := _), neg_add,
        AddChar.map_add_eq_mul])
    (fun β => by
      unfold chr
      rw [ZeroMemClass.coe_zero, ZeroMemClass.coe_zero, Matrix.zero_mul, Matrix.trace_zero, map_zero, neg_zero,
        AddChar.map_zero_eq_one])
    (fun T β => hψ.2.1 _)
    (_root_.PositivityTheory.FTA.ZFC.chr_ker_k hB hb)
    lam 𝓖 hlam hFD (fun β => f (nb β * x))
    (hf.comp ((PositivityTheory.SiegelWeilFormula.kfour.nb_continuous hσ hb hnb).mul continuous_const))
    (fun γ hγ β => by
      show f (nb (γ + β) * x) = f (nb β * x)
      rw [PositivityTheory.SiegelWeilFormula.kfour.nb_add hnb, mul_assoc]
      exact hper γ hγ _)
    (fun T => (integral_congr_ae (.of_forall fun β => mul_comm _ _)).trans (hx T))
  have h0 := congrFun key 0
  simpa [PositivityTheory.SiegelWeilFormula.kfour.nb_zero hnb] using h0
end PositivityTheory.FTA.ZFC
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.HaarFundDomainTransferK
section
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
noncomputable section
namespace GlobalTheory.RatDarbouxTransferF
open scoped Pointwise
set_option maxHeartbeats 1000000 in
theorem haar_fundDomain_transfer_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
    ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
        ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
        ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
          (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
            co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
          ∀ (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), ν.IsAddHaarMeasure →
            IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν →
            ∃ (ν' : @Measure ((κ → AF F) × (κ → AF F)) (borel _)) (𝓕' : Set ((κ → AF F) × (κ → AF F))),
              @Measure.IsAddHaarMeasure _ _ _ (borel _) ν' ∧
              @IsAddFundamentalDomain (GlobalTheory.WeilUnitaryTransport.ratPair F κ) _ _ _ (borel _) 𝓕' ν' ∧
              ∀ f : (κ → AF F) × (κ → AF F) → ℂ,
                ∫⁻ w in 𝓕, ‖f (co.e w)‖ₑ ^ 2 ∂ν = ∫⁻ w in 𝓕', ‖f w‖ₑ ^ 2 ∂ν' := by
  intro F E _ _ _ _ _ σ B _ _ nS nT JS JT _ _ ξ₀ _ _ JA JB ξ _ _ κ _ co hrat ν 𝓕 hν h𝓕
  obtain ⟨hfr, hfin, -⟩ := finrank_AEF F E
  haveI : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI hMT : IsModuleTopology (AF F) (Matrix (Fin nT) (Fin nS) (AF F ⊗[F] E)) :=
    inferInstanceAs (IsModuleTopology (AF F) (Fin nT → Fin nS → AF F ⊗[F] E))
  letI mP : MeasurableSpace ((κ → AF F) × (κ → AF F)) := borel _
  haveI : BorelSpace ((κ → AF F) × (κ → AF F)) := ⟨rfl⟩
  haveI : BorelSpace (WOF F E nS nT) := ⟨rfl⟩
  let ce : Matrix (Fin nT) (Fin nS) (AF F ⊗[F] E) ≃L[AF F] (κ → AF F) × (κ → AF F) :=
    { co.e with
      continuous_toFun := IsModuleTopology.continuous_of_linearMap co.e.toLinearMap
      continuous_invFun := IsModuleTopology.continuous_of_linearMap co.e.symm.toLinearMap }
  let ca : WOF F E nS nT ≃ₜ+ (κ → AF F) × (κ → AF F) :=
    { co.e.toAddEquiv with
      continuous_toFun := ce.continuous
      continuous_invFun := ce.symm.continuous }
  let me : WOF F E nS nT ≃ᵐ (κ → AF F) × (κ → AF F) := ca.toHomeomorph.toMeasurableEquiv
  have into : ∀ g ∈ ratLF F E nS nT, co.e g ∈ GlobalTheory.WeilUnitaryTransport.ratPair F κ := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨y, z, h⟩ := hrat x
    exact (GlobalTheory.WeilUnitaryTransport.mem_ratPair_iff _).2 ⟨y, z, h⟩
  have onto' : ∀ p ∈ GlobalTheory.WeilUnitaryTransport.ratPair F κ, co.e.symm p ∈ ratLF F E nS nT :=
    onto F E nS nT κ co.e hrat
  refine ⟨ν.map me, me '' 𝓕, ?_, ?_, ?_⟩
  · exact ca.isAddHaarMeasure_map ν
  · refine ⟨?_, ?_, ?_⟩
    · have hqmp : Measure.QuasiMeasurePreserving me.symm (ν.map me) ν :=
        (MeasurePreserving.mk me.symm.measurable (MeasurableEquiv.map_symm_map me)).quasiMeasurePreserving
      have hpre : me '' 𝓕 = me.symm ⁻¹' 𝓕 :=
        Set.ext fun y => ⟨by rintro ⟨w, hw, rfl⟩; simpa using hw, fun hy => ⟨me.symm y, hy, me.apply_symm_apply y⟩⟩
      rw [hpre]
      exact h𝓕.nullMeasurableSet.preimage hqmp
    · rw [me.measurableEmbedding.ae_map_iff]
      filter_upwards [h𝓕.ae_covers] with x ⟨g, hg⟩
      refine ⟨⟨co.e g, into g g.2⟩, g +ᵥ x, hg, ?_⟩
      show co.e ((g : WOF F E nS nT) + x) = co.e g + co.e x
      rw [map_add (f := _)]
    · intro p q hpq
      let g : ratLF F E nS nT := ⟨co.e.symm p, onto' p p.2⟩
      let h : ratLF F E nS nT := ⟨co.e.symm q, onto' q q.2⟩
      have hgh : g ≠ h := by
        intro e
        apply hpq
        apply Subtype.ext
        have := congrArg (fun t : ratLF F E nS nT => co.e (t : WOF F E nS nT)) e
        simpa [g, h] using this
      have himg : ∀ (r : GlobalTheory.WeilUnitaryTransport.ratPair F κ) (k : ratLF F E nS nT),
          (k : WOF F E nS nT) = co.e.symm r → r +ᵥ me '' 𝓕 = me '' (k +ᵥ 𝓕) := by
        intro r k hk
        rw [← Set.image_vadd, ← Set.image_vadd, Set.image_image, Set.image_image]
        refine Set.image_congr fun w _ => ?_
        show (r : (κ → AF F) × (κ → AF F)) + co.e w = co.e ((k : WOF F E nS nT) + w)
        rw [map_add (f := _), hk, LinearEquiv.apply_symm_apply]
      show MeasureTheory.AEDisjoint (ν.map me) (p +ᵥ me '' 𝓕) (q +ᵥ me '' 𝓕)
      rw [himg p g rfl, himg q h rfl, MeasureTheory.AEDisjoint, ← Set.image_inter me.injective, me.map_apply,
        me.preimage_image]
      exact h𝓕.aedisjoint hgh
  · intro f
    rw [MeasurableEquiv.restrict_map, MeasurableEquiv.preimage_image, lintegral_map_equiv]
    rfl
end GlobalTheory.RatDarbouxTransferF
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.HeckeCharEqOneOfSplitK
section
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
noncomputable section
namespace GlobalTheory.HeckeSplitBase
theorem heckeChar_eq_one_of_split_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ ν : (AF F ⊗[F] E)ˣ →* Circle, IsHeckeCharF ν →
      (∀ e, IsSplitIdemF σ e → ∀ x : (AF F ⊗[F] E)ˣ, (e + cAF σ e) * ((x : AF F ⊗[F] E) - 1) = (x : AF F ⊗[F] E) - 1 →
        ν x = 1) → ∀ x, ν x = 1 := by
  intro F E _ _ _ _ _ σ B hB ν hν hs
  exact GlobalTheory.T.heckeChar_eq_one_of_trivial_splitPlaces_CM F E σ hB.cm ν hν hs
end GlobalTheory.HeckeSplitBase
end
end
end

