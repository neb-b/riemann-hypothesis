module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0930
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1674
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1260
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0922
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryOperatorCommutesSchrodinger
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicFourierRealisesWeylElement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1558
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0061

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationDarbouxChangeIntertwine
section
open scoped TensorProduct NNReal ENNReal Matrix Classical
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.TowU

noncomputable section

namespace GlobalTheory.TowU

section Dbl

variable {R : Type} [CommRing R] [Invertible (2 : R)] {E : Type} [CommRing E] [Algebra R E] {c : E →ₐ[R] E}
  {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] {ξ : E} {JA : Matrix α α E} {JB : Matrix β β E}
  {κ κ' : Type} [Fintype κ] [Fintype κ']

end Dbl

section Adelic

variable {F : Type} [Field F] [NumberField F]

theorem adm_of_eqOn_schA {κ : Type} [Fintype κ] {l l' : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ}
    (h : ∀ φ ∈ schA F κ, l φ = l' φ) (hl : l ∈ (adeleClass F).adm κ) : l' ∈ (adeleClass F).adm κ := by
  intro g hg
  obtain ⟨T, hT⟩ := hl g hg
  exact ⟨T, fun f => (h _ (Submodule.subset_span ⟨f, g, hg, rfl⟩)).symm.trans (hT f)⟩

variable {ψ : AddChar (AF F) ℂ} {W : Type} [AddCommGroup W] [Module (AF F) W] {B : W → W → AF F}
  {κ κ' : Type} [Fintype κ] [Fintype κ'] {d : Darboux B κ} {d' : Darboux B κ'}
  {s : (κ → AF F) × (κ → AF F) → (κ' → AF F) × (κ' → AF F)}
  {S : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ' → AF F) → ℂ)} {S' : ((κ' → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)}

theorem IsOp.rho_eq (hs : ∀ w, s (d.e w) = d'.e w) (hS : IsOp ψ s S S') (w : W) {φ : (κ → AF F) → ℂ}
    (hφ : φ ∈ schA F κ) : S (d.rho ψ w φ) = d'.rho ψ w (S φ) := by
  simp only [Darboux.rho]
  rw [hS.Heisenberg₂ _ _ hφ, hs]

theorem isUSplitting_of_isOp (hψ : IsStd ψ) (hs : ∀ w, s (d.e w) = d'.e w) (hS : IsOp ψ s S S')
    {G : Type} [Group G] [TopologicalSpace G] {act : G → W → W}
    {om : G →* Module.End ℂ ((κ → AF F) → ℂ)} {om' : G →* Module.End ℂ ((κ' → AF F) → ℂ)}
    (hom : ∀ g, ∀ φ ∈ schA F κ', om' g φ = S (om g (S' φ)))
    (h : IsUSplitting (adeleClass F) ψ d act om) : IsUSplitting (adeleClass F) ψ d' act om' := by
  have hmem : ∀ (κ₀ : Type) [Fintype κ₀] (p : (κ₀ → AF F) × (κ₀ → AF F)) (φ : (κ₀ → AF F) → ℂ),
      φ ∈ schA F κ₀ → schr ψ p φ ∈ schA F κ₀ := fun κ₀ _ p φ hφ =>
    GlobalTheory.SchrKeepsSchA.schr_mem_schA F ψ hψ κ₀ p φ hφ
  have hrho' : ∀ w, ∀ φ ∈ schA F κ', S' (d'.rho ψ w φ) = d.rho ψ w (S' φ) := fun w φ hφ => by
    have h1 := IsOp.rho_eq hs hS w (hS.pres' φ hφ)
    rw [hS.right φ hφ] at h1
    have hm : d.rho ψ w (S' φ) ∈ schA F κ := hmem _ _ _ (hS.pres' φ hφ)
    rw [← h1, hS.left _ hm]
  refine ⟨⟨fun g φ hφ => ?_, fun g w φ hφ => ?_, fun g l hl => ?_⟩, fun μ' hμ' g φ hφ => ?_, fun l hl φ hφ => ?_⟩
  · rw [hom g φ hφ]
    exact hS.pres _ (h.pres g _ (hS.pres' φ hφ))
  · have hw : d'.rho ψ w φ ∈ schA F κ' := hmem _ _ _ hφ
    rw [hom g _ hw, hrho' w φ hφ, h.impl g w _ (hS.pres' φ hφ),
      IsOp.rho_eq hs hS _ (h.pres g _ (hS.pres' φ hφ)), hom g φ hφ]
  · have h2 := hS.adm' _ (h.adm g _ (hS.adm l hl))
    refine adm_of_eqOn_schA (fun φ hφ => ?_) h2
    simp only [LinearMap.coe_comp, Function.comp_apply]
    rw [hom g φ hφ]
  · letI : MeasurableSpace (κ → AF F) := borel _
    haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
    obtain ⟨c, -, -, hc⟩ := hS.norm Measure.addHaar μ' inferInstance hμ'
    rw [hom g φ hφ, hc _ (h.pres g _ (hS.pres' φ hφ)), h.unit Measure.addHaar inferInstance g _ (hS.pres' φ hφ),
      ← hc _ (hS.pres' φ hφ), hS.right φ hφ]
  · refine (h.cont (l ∘ₗ S) (hS.adm l hl) (S' φ) (hS.pres' φ hφ)).congr fun g => ?_
    simp only [LinearMap.coe_comp, Function.comp_apply]
    rw [hom g φ hφ]

theorem siegelRule_of_isOp {E' : Type} [CommRing E'] [Algebra (AF F) E'] {c : E' →ₐ[AF F] E'} {α β : Type} [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] {ξ : E'} {JA : Matrix α α E'} {JB : Matrix β β E'}
    {d : Darboux (symp c ξ JA JB) κ} {d' : Darboux (symp c ξ JA JB) κ'} (hs : ∀ w, s (d.e w) = d'.e w)
    (hS : IsOp ψ s S S') {χ : E'ˣ →* Circle} {ν : Type} [Fintype ν] [DecidableEq ν] {Cy : Matrix β ν E'}
    {om : UG c JB →* Module.End ℂ ((κ → AF F) → ℂ)} {om' : UG c JB →* Module.End ℂ ((κ' → AF F) → ℂ)}
    (hom : ∀ g, ∀ φ ∈ schA F κ', om' g φ = S (om g (S' φ)))
    (h : SiegelRule c (adeleClass F) ψ ξ JA JB d χ Cy om) : SiegelRule c (adeleClass F) ψ ξ JA JB d' χ Cy om' := by
  intro l hl hinv p t hpt φ hφ
  have key := h (l ∘ₗ S) (hS.adm l hl) (fun z φ' hφ' => by
    simp only [LinearMap.coe_comp, Function.comp_apply]
    rw [IsOp.rho_eq hs hS _ hφ']
    exact hinv z _ (hS.pres _ hφ')) p t hpt (S' φ) (hS.pres' φ hφ)
  simp only [LinearMap.coe_comp, Function.comp_apply, hS.right φ hφ] at key
  rw [hom p φ hφ]
  exact key

end Adelic

end GlobalTheory.TowU

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationUnitaryStandardCharacter
section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

noncomputable section

namespace GlobalTheory.SplitScalar

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]


open scoped Classical in
theorem proj_mem_adm (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (x : κ → AF F) :
    (LinearMap.proj x : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) ∈ (adeleClass F).adm κ := by
  intro g _
  refine ⟨g (fun i => (x i).2) • ((BoundedContinuousFunction.evalCLM ℂ
    (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1)).comp
      (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (κ → mixedEmbedding.mixedSpace F) ℂ)), fun f => ?_⟩
  simp [pureA, mul_comm]

theorem apply_ne_zero {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (T : G →* Module.End ℂ V) (q : G) {f : V}
    (hf : f ≠ 0) : T q f ≠ 0 := fun h => hf (by
  have e : T q⁻¹ (T q f) = f := by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  rw [← e, h, map_zero])

variable {σ : E →ₐ[F] E} {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

theorem at_inv {JB : Matrix β β (AE F E)} {g : UG (cA σ) JB}
    (hg : At (evI F) ((g.1 : Matrix β β (AE F E)) - 1)) : At (evI F) (((g⁻¹).1 : Matrix β β (AE F E)) - 1) := by
  intro u hu
  have e : ((g⁻¹).1 : Matrix β β (AE F E)) - 1 = -(((g⁻¹).1 : Matrix β β (AE F E)) * ((g.1 : Matrix β β (AE F E)) - 1)) := by
    rw [Matrix.mul_sub, Matrix.mul_one]
    have : ((g⁻¹).1 : Matrix β β (AE F E)) * (g.1 : Matrix β β (AE F E)) = 1 := by
      rw [Subgroup.coe_inv, Units.inv_mul]
    rw [this]; abel
  rw [e, smul_neg, ← Matrix.mul_smul, hg u hu, Matrix.mul_zero, neg_zero]

theorem at_mul {JB : Matrix β β (AE F E)} {g h : UG (cA σ) JB}
    (hg : At (evI F) ((g.1 : Matrix β β (AE F E)) - 1)) (hh : At (evI F) ((h.1 : Matrix β β (AE F E)) - 1)) :
    At (evI F) (((g * h).1 : Matrix β β (AE F E)) - 1) := by
  intro u hu
  have e : ((g * h).1 : Matrix β β (AE F E)) - 1 =
      (g.1 : Matrix β β (AE F E)) * ((h.1 : Matrix β β (AE F E)) - 1) + ((g.1 : Matrix β β (AE F E)) - 1) := by
    rw [Subgroup.coe_mul, Units.val_mul, Matrix.mul_sub, Matrix.mul_one]; abel
  rw [e, smul_add, ← Matrix.mul_smul, hh u hu, hg u hu, Matrix.mul_zero, add_zero]

theorem actB_actB_inv {JB : Matrix β β (AE F E)} (g : UG (cA σ) JB) (x : Matrix α β (AE F E)) :
    actB (cA σ) g (actB (cA σ) g⁻¹ x) = x := by
  unfold actB
  rw [Matrix.mul_assoc, ← Matrix.transpose_mul, Subgroup.coe_inv, Units.mul_inv, Matrix.transpose_one, Matrix.mul_one]

theorem splittings_differ_by_character : GlobalTheory.FunPr.Hypotheses₂ →
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (ψ : AddChar (AF F) ℂ) (JA : Matrix α α (AE F E))
    (JB : Matrix β β (AE F E)) (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ)
    (om ω₀ : UG (cA σ) JB →* Module.End ℂ ((κ → AF F) → ℂ)), IsStd ψ →
    IsUSplitting (adeleClass F) ψ d (actB (cA σ)) om →
    (∀ g : UG (cA σ) JB, At (evI F) ((g.1 : Matrix β β (AE F E)) - 1) →
        (∀ φ ∈ schA F κ, ω₀ g φ ∈ schA F κ) ∧
        (∀ w, ∀ φ ∈ schA F κ, ω₀ g (d.rho ψ w φ) = d.rho ψ (actB (cA σ) g w) (ω₀ g φ)) ∧
        ∀ μ : @Measure (κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
          ∀ φ ∈ schA F κ, ∫⁻ x, ‖ω₀ g φ x‖ₑ ^ 2 ∂μ = ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ) →
    (∀ l ∈ (adeleClass F).adm κ, ∀ φ ∈ schA F κ,
        ContinuousOn (fun g => l (ω₀ g φ)) {g : UG (cA σ) JB | At (evI F) ((g.1 : Matrix β β (AE F E)) - 1)}) →
    ∃ ν : UG (cA σ) JB → ℂ,
      (∀ g : UG (cA σ) JB, At (evI F) ((g.1 : Matrix β β (AE F E)) - 1) → ∀ φ ∈ schA F κ, om g φ = ν g • ω₀ g φ) ∧
      (∀ g h : UG (cA σ) JB, At (evI F) ((g.1 : Matrix β β (AE F E)) - 1) → At (evI F) ((h.1 : Matrix β β (AE F E)) - 1) →
        ν (g * h) = ν g * ν h) ∧
      ContinuousOn ν {g : UG (cA σ) JB | At (evI F) ((g.1 : Matrix β β (AE F E)) - 1)} ∧
      ∀ g : UG (cA σ) JB, At (evI F) ((g.1 : Matrix β β (AE F E)) - 1) → ν g ≠ 0 := by
  intro hP F E _ _ _ _ _ σ α β κ _ _ _ _ _ ψ JA JB d om ω₀ hψ hom hω hcont
  have key : ∀ g : UG (cA σ) JB, ∃ z : ℂ, At (evI F) ((g.1 : Matrix β β (AE F E)) - 1) →
      ∀ φ ∈ schA F κ, om g φ = z • ω₀ g φ := by
    intro g
    by_cases hg : At (evI F) ((g.1 : Matrix β β (AE F E)) - 1)
    swap
    · exact ⟨1, fun h => absurd h hg⟩
    have hgi := at_inv hg
    obtain ⟨z, hz⟩ := _root_.GlobalTheory.AdelicSchur.schur hP F κ ψ hψ (om g * ω₀ g⁻¹)
      (fun φ hφ => hom.pres g _ ((hω _ hgi).1 φ hφ))
      (fun w φ hφ => by
        have e1 : schr ψ w φ = d.rho ψ (d.e.symm w) φ := by simp [Darboux.rho]
        rw [Module.End.mul_apply, Module.End.mul_apply, e1, (hω _ hgi).2.1 _ φ hφ,
          hom.impl g _ _ ((hω _ hgi).1 φ hφ), actB_actB_inv]
        simp [Darboux.rho])
      (fun μ hμ φ hφ => by
        rw [Module.End.mul_apply, hom.unit μ hμ g _ ((hω _ hgi).1 φ hφ), (hω _ hgi).2.2 μ hμ φ hφ])
    refine ⟨z, fun _ φ hφ => ?_⟩
    have := hz (ω₀ g φ) ((hω g hg).1 φ hφ)
    rwa [Module.End.mul_apply, ← Module.End.mul_apply (ω₀ g⁻¹), ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply] at this
  choose z hz using key
  by_cases h0 : ∃ φ₀ ∈ schA F κ, φ₀ ≠ 0
  swap
  · push_neg at h0
    refine ⟨fun _ => 1, fun g _ φ hφ => ?_, fun _ _ _ _ => by simp, continuousOn_const, fun _ _ => one_ne_zero⟩
    rw [h0 φ hφ, map_zero, map_zero, smul_zero]
  obtain ⟨φ₀, hφ₀, hne⟩ := h0
  refine ⟨z, hz, fun g h hg hh => ?_, fun g hg => ?_, fun g hg h0 => ?_⟩
  · have hgh := at_mul hg hh
    apply smul_left_injective ℂ (apply_ne_zero ω₀ (g * h) hne)
    show z (g * h) • ω₀ (g * h) φ₀ = (z g * z h) • ω₀ (g * h) φ₀
    rw [← hz _ hgh φ₀ hφ₀, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hz h hh φ₀ hφ₀, map_smul,
      hz g hg _ ((hω h hh).1 φ₀ hφ₀), smul_smul, mul_comm]
  · obtain ⟨x, hx⟩ := Function.ne_iff.1 (apply_ne_zero ω₀ g hne)
    have hl := proj_mem_adm F κ x
    have c1 : ContinuousWithinAt (fun q => (LinearMap.proj x : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) (ω₀ q φ₀))
        {g : UG (cA σ) JB | At (evI F) ((g.1 : Matrix β β (AE F E)) - 1)} g := hcont _ hl φ₀ hφ₀ g hg
    have c2 : ContinuousWithinAt (fun q => (LinearMap.proj x : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) (om q φ₀))
        {g : UG (cA σ) JB | At (evI F) ((g.1 : Matrix β β (AE F E)) - 1)} g :=
      (hom.cont _ hl φ₀ hφ₀).continuousWithinAt
    have hx' : (LinearMap.proj x : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) (ω₀ g φ₀) ≠ 0 := hx
    have c3 := c2.div c1 hx'
    have hq : ∀ q, At (evI F) ((q.1 : Matrix β β (AE F E)) - 1) →
        (LinearMap.proj x : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) (ω₀ q φ₀) ≠ 0 →
        z q = (LinearMap.proj x : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) (om q φ₀) /
          (LinearMap.proj x : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) (ω₀ q φ₀) := by
      intro q hqS hq0
      rw [hz q hqS φ₀ hφ₀, map_smul, smul_eq_mul, mul_div_cancel_right₀ _ hq0]
    refine c3.congr_of_eventuallyEq ?_ (hq g hg hx')
    filter_upwards [Filter.Tendsto.eventually_ne c1 hx', self_mem_nhdsWithin] with q hq0 hqS
    exact hq q hqS hq0
  · have := hz g hg φ₀ hφ₀
    rw [h0, zero_smul] at this
    exact apply_ne_zero om g hne this

end GlobalTheory.SplitScalar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeylElementRealisedByFourierTransforms
section
open scoped TensorProduct NNReal ENNReal Matrix Classical ComplexConjugate
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.TowU

noncomputable section

namespace GlobalTheory.TowU.WeylModel

variable {F : Type} [Field F] [NumberField F]

theorem act_weyl {κ : Type} [Fintype κ] [DecidableEq κ] (w : (κ → AF F) × (κ → AF F)) :
    AdelicSvN.act (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (κ ⊕ κ) (κ ⊕ κ) F) w = (w.2, -w.1) := by
  simp [AdelicSvN.act, Matrix.fromBlocks_map, Matrix.fromBlocks_mulVec, Matrix.map_neg, Matrix.neg_mulVec]

theorem conj_psi {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (t : AF F) : conj (ψ t) = ψ (-t) := by
  rw [AddChar.map_neg_eq_inv, Complex.inv_eq_conj (GlobalTheory.StdCharFromIsStd.norm_psi hψ t)]

end GlobalTheory.TowU.WeylModel


open GlobalTheory.TowU.WeylModel in
theorem GlobalTheory.TowU.realised_weyl2 : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ] [DecidableEq κ], ∃ (S : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)) (S' : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)), IsOp2 ψ (GlobalTheory.AdelicSvN.act (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (κ ⊕ κ) (κ ⊕ κ) F)) S S' := by
  intro F _ _ ψ hψ κ _ _
  haveI : SecondCountableTopology (AF F) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  letI : MeasurableSpace (κ → AF F) := borel _
  haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
  letI : MeasurableSpace (κ ⊕ κ → AF F) := borel _
  haveI : BorelSpace (κ ⊕ κ → AF F) := ⟨rfl⟩
  let μ : Measure (κ → AF F) := Measure.addHaar
  let E : (κ → AF F) × (κ → AF F) ≃+ (κ ⊕ κ → AF F) :=
    { toFun := fun p => Sum.elim p.1 p.2
      invFun := fun x => (x ∘ Sum.inl, x ∘ Sum.inr)
      left_inv := fun p => by simp
      right_inv := fun x => by simp
      map_add' := fun p q => by funext i; cases i <;> rfl }
  have hc : Continuous E := (Homeomorph.sumArrowHomeomorphProdArrow (X := AF F) (ι := κ) (ι' := κ)).symm.continuous
  have hc' : Continuous E.symm := (Homeomorph.sumArrowHomeomorphProdArrow (X := AF F) (ι := κ) (ι' := κ)).continuous
  let H : (κ → AF F) × (κ → AF F) ≃ₜ (κ ⊕ κ → AF F) :=
    { toEquiv := E.toEquiv, continuous_toFun := hc, continuous_invFun := hc' }
  let ν : Measure (κ ⊕ κ → AF F) := Measure.map E (μ.prod μ)
  haveI : ν.IsAddHaarMeasure := E.isAddHaarMeasure_map _ hc hc'
  let ε₁ : κ → ℤˣ := fun _ => 1
  let ε₂ : κ ⊕ κ → ℤˣ := Sum.elim (fun _ => 1) (fun _ => -1)
  obtain ⟨S, S', hS, hSf⟩ := _root_.GlobalTheory.TowU.FourWeyl.isOp_fourier F ψ hψ κ μ inferInstance ε₁
  obtain ⟨Sd, Sd', hSd, hSdf⟩ := _root_.GlobalTheory.TowU.FourWeyl.isOp_fourier F ψ hψ (κ ⊕ κ) ν inferInstance ε₂
  refine ⟨S, S', ?_, Sd, Sd', ?_, fun φ₁ h₁ φ₂ h₂ => ?_⟩
  · convert hS using 1
    funext w
    rw [act_weyl]
    refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;> simp [ε₁]
  · convert hSd using 1
    funext w
    refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;> rcases i with i | i <;>
      simp [dblAct, act_weyl, ε₂]
  · funext y
    have hν : ν = Measure.map H.toMeasurableEquiv (μ.prod μ) := rfl
    have e₂ : star (S (star φ₂)) (y ∘ Sum.inr) =
        ∫ x, φ₂ x * ψ (-(∑ i, ((ε₁ i : ℤ) : AF F) * x i * (y ∘ Sum.inr) i)) ∂μ := by
      rw [Pi.star_apply, hSf (star φ₂) (GlobalTheory.ConjSch.star_mem_schA κ φ₂ h₂), Complex.star_def, ← integral_conj]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      beta_reduce
      rw [map_mul, conj_psi hψ, Pi.star_apply, Complex.star_def, Complex.conj_conj]
    rw [hSdf _ (GlobalTheory.SchwartzBox.boxFun_mem_schA F κ κ φ₁ h₁ φ₂ h₂), hν, integral_map_equiv]
    change _ = S φ₁ (y ∘ Sum.inl) * star (S (star φ₂)) (y ∘ Sum.inr)
    rw [e₂, hSf φ₁ h₁, ← integral_prod_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    change φ₁ p.1 * φ₂ p.2 * ψ (∑ i, ((ε₂ i : ℤ) : AF F) * Sum.elim p.1 p.2 i * y i) = _
    have es : ∑ i, ((ε₂ i : ℤ) : AF F) * Sum.elim p.1 p.2 i * y i =
        ∑ i, ((ε₁ i : ℤ) : AF F) * p.1 i * (y ∘ Sum.inl) i +
          -(∑ i, ((ε₁ i : ℤ) : AF F) * p.2 i * (y ∘ Sum.inr) i) := by
      simp [Fintype.sum_sum_type, ε₁, ε₂]
    rw [es, AddChar.map_add_eq_mul]
    ring

end
end

