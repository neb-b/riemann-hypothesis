module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.SmallSC
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1343
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1376
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1003
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Formalism.LocalToGlobal.IndefiniteReal.DatumF
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1246

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.HaarLc
section
noncomputable section

open scoped TensorProduct NNReal ENNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.ModuLR GlobalTheory.GaugeEx GlobalTheory.JacSubst

namespace PositivityTheory.SiegelWeilFormula.Ald

theorem haarLc : HaarLc := by
  intro F E _ _ _ _ _ σ hcm m J hJ bs g μ hμ f
  letI mA : MeasurableSpace (Fin m × Fin 2 → AF F) := borel _
  haveI : BorelSpace (Fin m × Fin 2 → AF F) := ⟨rfl⟩
  letI mV : MeasurableSpace (Fin m → AE F E) := borel _
  haveI : BorelSpace (Fin m → AE F E) := ⟨rfl⟩
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) (AE F E)
  let e := coordCE F E (Module.finBasis F E)
  haveI : LocallyCompactSpace (AE F E) := e.isOpenEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (AE F E) := e.secondCountableTopology
  haveI : T2Space (AE F E) := e.isEmbedding.t2Space
  haveI : LocallyCompactSpace (Matrix (Fin m) (Fin 1) (AE F E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin m → Fin 1 → AE F E))
  haveI : SecondCountableTopology (Matrix (Fin m) (Fin 1) (AE F E)) :=
    inferInstanceAs (SecondCountableTopology (Fin m → Fin 1 → AE F E))
  letI : MeasurableSpace (Matrix (Fin m) (Fin 1) (AE F E)) := borel _
  haveI : BorelSpace (Matrix (Fin m) (Fin 1) (AE F E)) := ⟨rfl⟩
  set t : GL (Fin m) (AE F E) := (g : GL (Fin m) (AE F E)) with ht
  have hdt : IsUnit (t : Matrix (Fin m) (Fin m) (AE F E)).det := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply]; exact Units.isUnit _
  let φ := mulVecCE (t : Matrix (Fin m) (Fin m) (AE F E)) hdt
  obtain ⟨κ, _, _, Λ, hΛ, hdet, hχ⟩ :=
    @exists_matrix_restrictScalars_lrCE F E _ _ _ _ _ m (1 : ℕ) _ _ _ _ t (1 : GL (Fin 1) (AE F E))

  have hc : addEquivAddHaarChar φ = 1 := by
    have h1 : addEquivAddHaarChar φ = addEquivAddHaarChar (lrCE t (1 : GL (Fin 1) (AE F E))) := by
      rw [← addEquivAddHaarChar_transport (colCE (AE F E) m) φ]
      congr 1
      ext M i j
      rw [Fin.fin_one_eq_zero j]
      show ((t : Matrix (Fin m) (Fin m) (AE F E)) *ᵥ (fun k => M k 0)) i =
        ((t : Matrix (Fin m) (Fin m) (AE F E)) * M * ((1 : GL (Fin 1) (AE F E)) : Matrix (Fin 1) (Fin 1) (AE F E))) i 0
      rw [Units.val_one, Matrix.mul_one]
      simp [Matrix.mulVec, dotProduct, Matrix.mul_apply]
    have hu : hΛ.unit = Units.map (Algebra.norm (AF F) : AE F E →* AF F) (Matrix.GeneralLinearGroup.det t) := by
      ext
      simp only [IsUnit.unit_spec, hdet, Units.coe_map, MonoidHom.coe_coe, map_one, one_pow, mul_one, pow_one]
    rw [h1, hχ, chi_AF_det, hu, ht, norm_det_unitary hcm hJ g, map_one]

  have hV : ∀ (ν : Measure (Fin m → AE F E)), ν.IsAddHaarMeasure → ν.map φ = ν := by
    intro ν hν
    haveI : ν.Regular := inferInstance
    have key := addEquivAddHaarChar_smul_map ν φ
    rwa [hc, one_smul] at key

  let cm : (Fin m × Fin 2 → AF F) ≃ᵐ (Fin m → AE F E) := (colv m bs).toHomeomorph.toMeasurableEquiv
  let pm : (Fin m → AE F E) ≃ᵐ (Fin m → AE F E) := φ.toHomeomorph.toMeasurableEquiv
  haveI : μ.IsAddHaarMeasure := hμ
  have hH : (μ.map cm).IsAddHaarMeasure := ContinuousAddEquiv.isAddHaarMeasure_map μ (colv m bs)
  have hmap : (μ.map cm).map pm = μ.map cm := hV _ hH
  have e1 : ∀ x, Lc bs (mat g) x = cm.symm (pm (cm x)) := fun x => by rw [Lc_eq_colv]; rfl
  calc ∫⁻ x, f (Lc bs (mat g) x) ∂μ = ∫⁻ x, (fun y => f (cm.symm (pm y))) (cm x) ∂μ := by simp_rw [e1]
    _ = ∫⁻ y, f (cm.symm (pm y)) ∂(μ.map cm) := (lintegral_map_equiv (fun y => f (cm.symm (pm y))) cm).symm
    _ = ∫⁻ y, f (cm.symm y) ∂((μ.map cm).map pm) := (lintegral_map_equiv (fun y => f (cm.symm y)) pm).symm
    _ = ∫⁻ y, f (cm.symm y) ∂(μ.map cm) := by rw [hmap]
    _ = ∫⁻ x, f (cm.symm (cm x)) ∂μ := lintegral_map_equiv (fun y => f (cm.symm y)) cm
    _ = ∫⁻ x, f x ∂μ := by simp

end PositivityTheory.SiegelWeilFormula.Ald

end
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.SmallS
section
noncomputable section

open scoped TensorProduct NNReal ENNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Ald

variable {F : Type} [Field F] [NumberField F]

theorem sliceL_mem (hF : SliceFacts) {κ' κ'' : Type} [Fintype κ'] [Fintype κ''] {Ψ : (κ' ⊕ κ'' → AF F) → ℂ}
    (hΨ : Ψ ∈ schA F (κ' ⊕ κ'')) : (fun x'' : κ'' → AF F => Ψ (Sum.elim 0 x'')) ∈ schA F κ'' := by
  have h1 := GlobalTheory.TowU.RealComp.reix_mem_schA (Equiv.sumComm κ'' κ') hΨ
  have h2 := (hF F κ'' κ').1 _ h1
  convert h2 using 1
  funext x''
  simp only [slice0, LinearMap.coe_mk, AddHom.coe_mk, GlobalTheory.TowU.RealComp.reix_apply]
  congr 1
  funext i
  rcases i with i | i <;> rfl

theorem smallS_of (hC : ChartFacts) (hF : SliceFacts) (hU : SubSplit) (hH : HaarLc) : SmallS := by
  intro hT F E _ _ _ _ _ σ d n h Y b j ε hn hs hb e1 e2 hj dd0 dd' had0 had' S1 S1' C hC0 hop hTf
  have hψ : IsStd d.B.ψ := d.ok.good.std
  have hcm : IsCMExt F E σ := d.ok.good.cm
  have hJ : d.A.J.det ≠ 0 := by
    rcases d.ok.sign with ⟨hA, -⟩ | ⟨hA, -⟩
    · exact (_root_.GlobalTheory.isUnit_det_of_isHerm F E σ d.B d.m d.A d.r d.s hA).ne_zero
    · exact (_root_.GlobalTheory.SkewUnit.isUnit_det_of_isSkew F E σ d.B d.m d.A d.r d.s hA).ne_zero
  obtain ⟨hc1, -, -, -, hc5⟩ := hC F E σ d n h Y b j ε hn hs hb e1 e2 hj dd0 dd' had0 had'
  have hlin := d.ok.dbl.lin

  have pres1 : ∀ u : UA σ d.A.J, ∀ φ ∈ schA F (K1 d.m n), (S1 ∘ₗ d.S u ∘ₗ S1') φ ∈ schA F (K1 d.m n) :=
    fun u φ hφ => hop.pres _ (hlin.pres u _ (hop.pres' φ hφ))
  have one1 : ∀ φ ∈ schA F (K1 d.m n), (S1 ∘ₗ d.S 1 ∘ₗ S1') φ = φ := fun φ hφ => by
    simp only [LinearMap.coe_comp, Function.comp_apply, map_one, Module.End.one_apply]
    exact hop.right φ hφ
  have mul1 : ∀ u v : UA σ d.A.J, ∀ φ ∈ schA F (K1 d.m n),
      (S1 ∘ₗ d.S (u * v) ∘ₗ S1') φ = (S1 ∘ₗ d.S u ∘ₗ S1') ((S1 ∘ₗ d.S v ∘ₗ S1') φ) := fun u v φ hφ => by
    simp only [LinearMap.coe_comp, Function.comp_apply, map_mul, Module.End.mul_apply]
    rw [hop.left _ (hlin.pres v _ (hop.pres' φ hφ))]
  obtain ⟨SA1, hSA1⟩ := projHom (fun u => S1 ∘ₗ d.S u ∘ₗ S1') pres1 one1 mul1
  have hsplit : IsUSplitting (adeleClass F) d.B.ψ (GlobalTheory.TowU.reindexD dd0 (eK d.m h).symm)
      (fun (g : UA σ d.A.J) (x : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)) => mat g * x) SA1 :=
    GlobalTheory.TowU.isUSplitting_of_isOp hψ (fun w => by simp) hop hSA1 hlin

  have hexp : ∀ u : UA σ d.A.J, ∀ Ψ ∈ schA F (K1 d.m n), ∀ x : K1 d.m n → AF F,
      SA1 u Ψ x = Ψ (Sum.elim (Lk d.bs (mat u⁻¹) (x ∘ Sum.inl)) (Lc d.bs (mat u⁻¹) (x ∘ Sum.inr))) := by
    intro u Ψ hΨ x
    set X : Mx F E d.m d.n := cmbB d.bs (x ∘ (eK d.m h).symm) with hX
    have hx : crdB d.bs X ∘ eK d.m h = x := by
      rw [hX, crdB_cmbB]; funext k; simp
    have hΦ : S1' Ψ ∈ d.sch := hop.pres' Ψ hΨ
    have hTP := (hT.2.1 F E σ d (S1' Ψ) hΦ).2.2 u X
    rw [hTf _ (hlin.pres u _ hΦ), hTf _ hΦ, hop.right Ψ hΨ] at hTP
    have key := mul_left_cancel₀ hC0 hTP
    calc SA1 u Ψ x = S1 (d.S u (S1' Ψ)) x := by rw [hSA1 u Ψ hΨ]; rfl
      _ = S1 (d.S u (S1' Ψ)) (crdB d.bs X ∘ eK d.m h) := by rw [hx]
      _ = Ψ (crdB d.bs (mat u⁻¹ * X) ∘ eK d.m h) := key
      _ = _ := by rw [← Lk_crdB, hX, crdB_cmbB, Lk_eK]
  have hbox : ∀ u : UA σ d.A.J, ∀ φ' ∈ schA F (Fin d.m × Fin n × Fin 2), ∀ φ'' ∈ schA F (Fin d.m × Fin 2),
      SA1 u (boxFun φ' φ'') = boxFun (φ' ∘ Lk d.bs (mat u⁻¹)) (φ'' ∘ Lc d.bs (mat u⁻¹)) := by
    intro u φ' h' φ'' h''
    funext x
    rw [hexp u _ (GlobalTheory.SchwartzBox.boxFun_mem_schA F _ _ φ' h' φ'' h'')]
    rfl
  obtain ⟨φ₀, hφ₀, hφ₀1, hφ₀n⟩ := (hF F (Fin d.m × Fin n × Fin 2) (Fin d.m × Fin 2)).2.2.1
  obtain ⟨φa, hφa, hφa1, -⟩ := (hF F (Fin d.m × Fin 2) (Fin d.m × Fin n × Fin 2)).2.2.1

  let c : UA σ d.A.J → ((Fin d.m × Fin n × Fin 2 → AF F) → ℂ) →ₗ[ℂ] ((Fin d.m × Fin n × Fin 2 → AF F) → ℂ) :=
    fun u => LinearMap.funLeft ℂ ℂ (Lk d.bs (mat u⁻¹))
  have hc : ∀ u φ, c u φ = φ ∘ Lk d.bs (mat u⁻¹) := fun _ _ => rfl
  have presS : ∀ u, ∀ φ ∈ schA F (Fin d.m × Fin n × Fin 2), c u φ ∈ schA F (Fin d.m × Fin n × Fin 2) := by
    intro u φ hφ
    have := (hF F (Fin d.m × Fin n × Fin 2) (Fin d.m × Fin 2)).1 _
      (hsplit.pres u _ (GlobalTheory.SchwartzBox.boxFun_mem_schA F _ _ φ hφ φ₀ hφ₀))
    rw [hbox u φ hφ φ₀ hφ₀, slice0_box, Function.comp_apply, Lc_zero, hφ₀1, one_smul] at this
    exact this
  have oneS : ∀ φ ∈ schA F (Fin d.m × Fin n × Fin 2), c 1 φ = φ := by
    intro φ _
    have hm : mat (1 : UA σ d.A.J)⁻¹ = 1 := by rw [inv_one]; rfl
    rw [hc, hm]
    funext x
    simp only [Function.comp_apply, Lk_one]
  have mulS : ∀ u v, ∀ φ ∈ schA F (Fin d.m × Fin n × Fin 2), c (u * v) φ = c u (c v φ) := by
    intro u v φ _
    rw [hc, hc, hc, mul_inv_rev, show mat (v⁻¹ * u⁻¹) = mat v⁻¹ * mat u⁻¹ from rfl]
    funext x
    simp only [Function.comp_apply, Lk_mul]
  obtain ⟨S', hS'⟩ := projHom c presS oneS mulS

  have hφ₁ : ∀ g : UA σ d.A.J, φ₀ ∘ Lc d.bs (mat g⁻¹) ∈ schA F (Fin d.m × Fin 2) := by
    intro g
    have := sliceL_mem hF (hsplit.pres g _ (GlobalTheory.SchwartzBox.boxFun_mem_schA F _ _ φa hφa φ₀ hφ₀))
    rw [hbox g φa hφa φ₀ hφ₀] at this
    convert this using 1
    funext x''
    simp only [boxFun, Function.comp_apply, Sum.elim_comp_inl, Sum.elim_comp_inr, Lk_zero, hφa1, one_mul]
  have hsplitS : IsUSplitting (adeleClass F) d.B.ψ dd' (fun (g : UA σ d.A.J) x => mat g * x) S' :=
    hU F d.B.ψ hψ (Fin d.m × Fin n × Fin 2) (Fin d.m × Fin 2) (Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E))
      (Matrix (Fin d.m) (Fin n ⊕ Fin n) (AE F E)) _ _ (GlobalTheory.TowU.reindexD dd0 (eK d.m h).symm) dd' (emb h b d.b) hc1
      (UA σ d.A.J) (UA σ d.A.J) (fun g x => mat g * x) (fun g x => mat g * x) (MonoidHom.id _) continuous_id
      (fun g w' => hc5 g w') SA1 S' hsplit φ₀ hφ₀ hφ₀1 hφ₀n (fun g => ⟨φ₀ ∘ Lc d.bs (mat g⁻¹), hφ₁ g,
        by rw [Function.comp_apply, Lc_zero, hφ₀1],
        fun μ'' hμ'' => hH F E σ hcm d.m d.A.J hJ d.bs g⁻¹ μ'' hμ'' (fun x => ‖φ₀ x‖ₑ ^ 2),
        fun φ' hφ' => by
          show SA1 g (boxFun φ' φ₀) = _
          rw [hbox g φ' hφ' φ₀ hφ₀, hS' g φ' hφ', hc]⟩)
  refine ⟨S', hsplitS, fun g Φ hΦ => ?_⟩
  show S' g Φ 0 = Φ 0
  rw [hS' g Φ hΦ, hc, Function.comp_apply, Lk_zero]

end PositivityTheory.SiegelWeilFormula.Ald

end
end

