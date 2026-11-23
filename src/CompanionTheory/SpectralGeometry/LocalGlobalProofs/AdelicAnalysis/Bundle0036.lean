module

public import Mathlib
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0019
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0016
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HermitianOrbitLocalSectionSubgroup
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.DisintegrationDensityFormula
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0010
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0029
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0014
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0031

@[expose] public section

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberMeasureDisintegrationFormula
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.GramNear

theorem fibre_on_orbit (V X Y : Type) [AddCommGroup V] [TopologicalSpace V] [LocallyCompactSpace V]
    [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V] [IsTopologicalAddGroup V]
    [AddCommGroup X] [TopologicalSpace X] [LocallyCompactSpace X]
    [SecondCountableTopology X] [T2Space X] [MeasurableSpace X] [BorelSpace X] [IsTopologicalAddGroup X]
    (μ : Measure V) (ν : Measure X) [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure]
    (f : V → Y) (g : V → X) (ι : X → Y) (hι : Function.Injective ι) (hg : Continuous g)
    (hf : ∀ v, f v = ι (g v))
    (Q : Type) [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q] [LocallyCompactSpace Q]
    [SecondCountableTopology Q] [T2Space Q] [DistribMulAction Q V] [ContinuousSMul Q V]
    [DistribMulAction Q X] [ContinuousSMul Q X]
    (heq : ∀ (q : Q) (v : V), g (q • v) = q • g v) (b₀ : X)
    (ho : IsOpenEmbedding (fun q : Q => q • b₀)) :
    ∃ fib : X → Measure V, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι (g ⁻¹' (Set.range fun q : Q => q • b₀)) ν
      (Set.range fun q : Q => q • b₀) fib := by
  obtain ⟨χ, hχ, hμ⟩ := _root_.GlobalTheory.CompanionTheory.SW.exists_continuous_modulus_of_continuous_action V μ Q
  obtain ⟨χ', hχ', hν⟩ := _root_.GlobalTheory.CompanionTheory.SW.exists_continuous_modulus_of_continuous_action X ν Q
  exact _root_.GlobalTheory.CompanionTheory.SW.Slice.exists_isFibreFamily_openOrbit V X Y μ ν f g ι hι hg hf Q heq χ χ' hχ hχ' hμ hν b₀ ho

theorem exists_fibre_near : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n : ℕ) (μ : Measure (Fin n → Fin M → R ⊗[F] E)) (ν : Measure (HermR R σ n)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → ∀ S : HermR R σ n, IsUnit (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det → ∃ B : Set (HermR R σ n), IsOpen B ∧ S ∈ B ∧ (∀ S' ∈ B, IsUnit (S' : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det) ∧ ∃ fib, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ (gramR R σ J) Subtype.val (gramR R σ J ⁻¹' (Subtype.val '' B)) ν B fib := by
  intro F E _ _ _ _ _ σ hσ M J hJ R _ _ _ _ _ hR n μ ν hμ hν S hS
  have hR' := hR
  obtain ⟨_, _, _, _, -, -, -, -⟩ := hR'
  obtain ⟨_, _, _, _, hsig, -, -, hbor, -, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ R
  have hbor' := hbor n M
  obtain ⟨_, _, _, _, hlift⟩ := _root_.GlobalTheory.CompanionTheory.SW.HermTop.herm_top F E σ hσ R n
  obtain ⟨g, hgc, hgf⟩ := hlift M J hJ
  obtain ⟨hgram, hmul, hone, hherm, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.GramAlg.gram_algebra F E σ hσ M J hJ R n
  obtain ⟨Q, o, _, _, hoe, ho⟩ := _root_.GlobalTheory.CompanionTheory.SW.tri_slice F E σ hσ R hR n S hS

  let c : Q → Matrix (Fin n) (Fin n) (R ⊗[F] E) := fun q => (((q⁻¹ : Q) : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E))
  have hc1 : c 1 = 1 := by simp [c]
  have hcm : ∀ a b : Q, c (a * b) = c b * c a := by
    intro a b
    simp only [c, mul_inv_rev]
    rfl
  have hcc : Continuous c := Units.continuous_val.comp (continuous_subtype_val.comp continuous_inv)
  letI actV : DistribMulAction Q (Fin n → Fin M → R ⊗[F] E) :=
    { smul := fun q X => rmul R X (c q)
      one_smul := fun X => by
        change rmul R X (c 1) = X
        rw [hc1, hone]
      mul_smul := fun a b X => by
        change rmul R X (c (a * b)) = rmul R (rmul R X (c b)) (c a)
        rw [hcm, hmul]
      smul_zero := fun q => by
        change rmul R 0 (c q) = 0
        funext a i; simp [rmul]
      smul_add := fun q X Y => by
        change rmul R (X + Y) (c q) = rmul R X (c q) + rmul R Y (c q)
        funext a i; simp [rmul, add_mul, Finset.sum_add_distrib] }
  have hsmulV : ∀ (q : Q) (X : Fin n → Fin M → R ⊗[F] E), q • X = rmul R X (c q) := fun _ _ => rfl
  letI actH : DistribMulAction Q (HermR R σ n) :=
    { smul := fun q T => ⟨cT (sigR R σ) (c q) * (T : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * c q, hherm T (c q)⟩
      one_smul := fun T => by
        apply Subtype.ext
        change cT (sigR R σ) (c 1) * (T : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * c 1 = T
        rw [hc1]; simp [cT]
      mul_smul := fun a b T => by
        apply Subtype.ext
        change cT (sigR R σ) (c (a * b)) * (T : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * c (a * b) =
          cT (sigR R σ) (c a) * (cT (sigR R σ) (c b) * (T : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * c b) * c a
        rw [hcm]
        simp only [cT, Matrix.map_mul, Matrix.transpose_mul, Matrix.mul_assoc]
      smul_zero := fun q => by
        apply Subtype.ext
        change cT (sigR R σ) (c q) * (0 : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * c q = 0
        simp
      smul_add := fun q T T' => by
        apply Subtype.ext
        change cT (sigR R σ) (c q) * ((T : Matrix (Fin n) (Fin n) (R ⊗[F] E)) + T') * c q =
          cT (sigR R σ) (c q) * (T : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * c q +
            cT (sigR R σ) (c q) * (T' : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * c q
        rw [Matrix.mul_add, Matrix.add_mul] }
  have hsmulH : ∀ (q : Q) (T : HermR R σ n), ((q • T : HermR R σ n) : Matrix (Fin n) (Fin n) (R ⊗[F] E)) =
      cT (sigR R σ) (c q) * (T : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * c q := fun _ _ => rfl
  have hcontV : ContinuousSMul Q (Fin n → Fin M → R ⊗[F] E) := by
    refine ⟨?_⟩
    change Continuous fun p : Q × (Fin n → Fin M → R ⊗[F] E) => rmul R p.2 (c p.1)
    refine continuous_pi fun a => continuous_pi fun i => ?_
    simp only [rmul]
    refine continuous_finsetSum _ fun b _ => Continuous.mul ?_ ?_
    · exact (continuous_apply i).comp ((continuous_apply b).comp continuous_snd)
    · exact (hcc.comp continuous_fst).matrix_elem b a
  have hcontH : ContinuousSMul Q (HermR R σ n) := by
    refine ⟨?_⟩
    refine Continuous.subtype_mk (f := fun p : Q × HermR R σ n => cT (sigR R σ) (c p.1) * (p.2 : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * c p.1) ?_ _
    have h1 : Continuous fun p : Q × HermR R σ n => c p.1 := hcc.comp continuous_fst
    have h2 : Continuous fun p : Q × HermR R σ n => cT (sigR R σ) (c p.1) :=
      (h1.matrix_map hsig).matrix_transpose
    exact (h2.matrix_mul (continuous_subtype_val.comp continuous_snd)).matrix_mul h1
  have heq : ∀ (q : Q) (X : Fin n → Fin M → R ⊗[F] E), g (q • X) = q • g X := by
    intro q X
    apply Subtype.ext
    rw [hsmulV, hsmulH, ← hgf, ← hgf, hgram]
  have horb : IsOpenEmbedding (fun q : Q => q • S) := by
    have : (fun q : Q => q • S) = o ∘ (Homeomorph.inv Q) := by
      funext q
      apply Subtype.ext
      rw [hsmulH]
      exact (ho q⁻¹).symm
    rw [this]
    exact hoe.comp (Homeomorph.inv Q).isOpenEmbedding
  obtain ⟨fib, hfib⟩ := fibre_on_orbit (Fin n → Fin M → R ⊗[F] E) (HermR R σ n) (Matrix (Fin n) (Fin n) (R ⊗[F] E))
    μ ν (gramR R σ J) g Subtype.val Subtype.val_injective hgc hgf Q heq S horb
  refine ⟨Set.range fun q : Q => q • S, horb.isOpen_range, ⟨1, one_smul _ _⟩, ?_, fib, ?_⟩
  · rintro _ ⟨q, rfl⟩
    change IsUnit ((q • S : HermR R σ n) : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det
    rw [hsmulH]
    have hdc : IsUnit (c q).det := Matrix.isUnits_det_units _
    have hdc' : IsUnit (cT (sigR R σ) (c q)).det := by
      simp only [cT, Matrix.det_transpose]
      have := hdc.map (sigR R σ)
      rwa [RingHom.map_det] at this
    rw [Matrix.det_mul, Matrix.det_mul]
    exact (hdc'.mul hS).mul hdc
  · have hpre : gramR R σ J ⁻¹' (Subtype.val '' (Set.range fun q : Q => q • S)) = g ⁻¹' (Set.range fun q : Q => q • S) := by
      ext X
      simp only [Set.mem_preimage, hgf X]
      exact Subtype.val_injective.mem_set_image
    rw [hpre]
    exact hfib

end GlobalTheory.CompanionTheory.SW.GramNear
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberMeasuresChangeOfForm
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.LocIsom

theorem fibre_map_isometry : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (J' : Matrix (Fin M) (Fin M) E), IsHermND σ J' → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n : ℕ), ∀ (μ : Measure (Fin n → Fin M → R ⊗[F] E)) (ν : Measure (HermR R σ n)) (m : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → IsGramFib R σ J n μ ν m → ∀ (μ' : Measure (Fin n → Fin M → R ⊗[F] E)) m', μ'.IsAddHaarMeasure → IsGramFib R σ J' n μ' ν m' → ∀ g : GL (Fin M) (R ⊗[F] E), JR R J' = cT (sigR R σ) (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) * JR R J * (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) → ∀ a : ℝ≥0, μ'.map (actTup R g) = a • μ → ∀ S, (m' S).map (actTup R g) = a • m S := by
  intro F E _ _ _ _ _ σ hcm M J hJ J' hJ' R _ _ _ _ _ hR n μ ν m hμ hν hm μ' m' hμ' hm' g hg a ha S
  have hR' := hR
  obtain ⟨hTR, hLC, hSC, hT2, -, -, -, -⟩ := hR'
  obtain ⟨hK1, hK2, hK3, hK4, -, -, -, hK8, -, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hcm R
  haveI := hK8 n M
  obtain ⟨hH1, hH2, hH3, hH4, hlift⟩ := GlobalTheory.CompanionTheory.SW.HermTop.herm_top F E σ hcm R n
  obtain ⟨l, hlc, hl⟩ := hlift M J hJ
  obtain ⟨l', hlc', hl'⟩ := hlift M J' hJ'
  have hact : ∀ X, gramR R σ J (actTup R g X) = gramR R σ J' X :=
    (GlobalTheory.CompanionTheory.SW.GramAlg.gram_algebra F E σ hcm M J hJ R n).2.2.2.2 J' g hg
  have hcont : ∀ h : GL (Fin M) (R ⊗[F] E),
      Continuous (actTup R h : (Fin n → Fin M → R ⊗[F] E) → (Fin n → Fin M → R ⊗[F] E)) := by
    intro h
    refine continuous_pi fun b => ?_
    exact continuous_const.matrix_mulVec (continuous_apply b)
  let e : (Fin n → Fin M → R ⊗[F] E) ≃ₜ (Fin n → Fin M → R ⊗[F] E) :=
    { toFun := actTup R g
      invFun := actTup R g⁻¹
      left_inv := fun X => by
        funext b
        simp [actTup, Matrix.mulVec_mulVec]
      right_inv := fun X => by
        funext b
        simp [actTup, Matrix.mulVec_mulVec]
      continuous_toFun := hcont g
      continuous_invFun := hcont g⁻¹ }
  have he : (e : (Fin n → Fin M → R ⊗[F] E) → _) = actTup R g := rfl
  let B : Set (HermR R σ n) := {S | IsUnit (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det}
  have hB : IsOpen B := by
    have hu := (_root_.GlobalTheory.CompanionTheory.SW.KUnits.units_val_isOpenEmbedding F E σ hcm R hR).isOpen_range
    have hd : Continuous fun S : HermR R σ n => (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det :=
      Continuous.matrix_det continuous_subtype_val
    have := hu.preimage hd
    convert this using 1
    ext S
    simp [B, IsUnit]
  have hset : {X | IsUnit (gramR R σ J X).det} = l ⁻¹' B := by
    ext X
    simp [B, hl X]
  have hset' : {X | IsUnit (gramR R σ J' X).det} = l' ⁻¹' B := by
    ext X
    simp [B, hl' X]
  have hm'' : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ' (gramR R σ J') Subtype.val (l' ⁻¹' B) ν B m' := by
    have := hm'
    unfold IsGramFib at this
    rw [hset'] at this
    exact this
  have hcompat : ∀ X, l (e X) = (Homeomorph.refl _) (l' X) := by
    intro X
    apply Subtype.ext
    show ((l (e X) : HermR R σ n) : Matrix (Fin n) (Fin n) (R ⊗[F] E)) = (l' X : HermR R σ n)
    rw [← hl, ← hl']
    exact hact X
  have hT := GlobalTheory.CompanionTheory.SW.isFibreFamily_transport _ _ _ μ' ν (gramR R σ J') l' Subtype.val
    Subtype.val_injective hlc' hl' _ (gramR R σ J) l hlc hl e (Homeomorph.refl _) hcompat B hB m' hm''
  have himg : (Homeomorph.refl (HermR R σ n)) '' B = B := by simp
  have hνm : ν.map (Homeomorph.refl (HermR R σ n)) = ν := by
    simp
  rw [himg, hνm, he, ha, ← hset] at hT
  have hfib : IsGramFib R σ J n (a • μ) ν (fun S => (m' S).map (actTup R g)) := hT
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [zero_smul] at ha
    have h0 : μ' ≠ 0 := by
      intro h
      have := isOpen_univ.measure_pos μ' Set.univ_nonempty
      simp [h] at this
    apply h0
    rw [← he] at ha
    have := congrArg (fun ρ : Measure _ => ρ Set.univ) ha
    simp only [Measure.coe_zero, Pi.zero_apply] at this
    rw [Measure.map_apply e.continuous.measurable MeasurableSet.univ] at this
    simpa using this
  have hHaar : (a • μ).IsAddHaarMeasure := Measure.IsAddHaarMeasure.nnreal_smul μ ha0
  have h1 := _root_.GlobalTheory.CompanionTheory.SW.Rescale.isGramFib_rescale F E σ hcm M J hJ R hR n μ ν m hμ hν hm a 1 ha0 one_ne_zero
  rw [one_smul] at h1
  simp only [div_one] at h1
  exact _root_.GlobalTheory.CompanionTheory.SW.GramFib.fibre_unique F E σ hcm M J hJ R hR n (a • μ) ν _ hHaar hν hfib _ h1 S

end GlobalTheory.CompanionTheory.SW.LocIsom
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberMeasuresSupport
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.FibScale

theorem fib_rmul : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n : ℕ), ∀ (μ : Measure (Fin n → Fin M → R ⊗[F] E)) (ν : Measure (HermR R σ n)) (m : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → IsGramFib R σ J n μ ν m → ∀ (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)), IsUnit g.det → ∀ τ : HermR R σ n → HermR R σ n, (∀ S, (τ S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) = cT (sigR R σ) g * S * g) → ∀ a c : ℝ≥0, μ.map (fun X => rmul R X g) = a • μ → ν.map τ = c • ν → ∀ S, a • m (τ S) = c • (m S).map (fun X => rmul R X g) := by
  intro F E _ _ _ _ _ σ hσ M J hJ R _ _ _ _ _ hR n μ ν m hμ hν hm g hg τ hτ a c hmu hnu S
  obtain ⟨hTR, hLC, hSC, hT2, -⟩ := id hR
  haveI := hTR
  haveI := hLC
  haveI := hSC
  haveI := hT2
  obtain ⟨hTK, hLK, hSK, hTK2, -, -, -, hBor, -, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ R
  haveI := hTK
  haveI := hLK
  haveI := hSK
  haveI := hTK2
  haveI := hBor n M
  obtain ⟨hLH, hSH, hT2H, hBH, hG⟩ := GlobalTheory.CompanionTheory.SW.HermTop.herm_top F E σ hσ R n
  haveI := hLH
  haveI := hSH
  haveI := hT2H
  haveI := hBH
  obtain ⟨G, hGc, hGe⟩ := hG M J hJ
  obtain ⟨halg, hcomp, hone, hmem, -⟩ := GlobalTheory.CompanionTheory.SW.GramAlg.gram_algebra F E σ hσ M J hJ R n
  have hKu := GlobalTheory.CompanionTheory.SW.KUnits.units_val_isOpenEmbedding F E σ hσ R hR
  have hg1 : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv g hg
  have hg2 : g⁻¹ * g = 1 := Matrix.nonsing_inv_mul g hg
  have hgi : IsUnit (g⁻¹).det := Matrix.isUnit_nonsing_inv_det g hg
  have hrc : ∀ h : Matrix (Fin n) (Fin n) (R ⊗[F] E),
      Continuous fun X : Fin n → Fin M → R ⊗[F] E => rmul R X h := by
    intro h
    refine continuous_pi fun b => continuous_pi fun i => ?_
    simp only [rmul]
    refine continuous_finsetSum _ fun k _ => ?_
    have h1 : Continuous fun Y : Fin n → Fin M → R ⊗[F] E => Y k i :=
      (continuous_apply i).comp (continuous_apply k)
    exact h1.mul continuous_const
  let e : (Fin n → Fin M → R ⊗[F] E) ≃ₜ (Fin n → Fin M → R ⊗[F] E) :=
    { toFun := fun X => rmul R X g
      invFun := fun X => rmul R X g⁻¹
      left_inv := fun X => by simp only [hcomp, hg1, hone]
      right_inv := fun X => by simp only [hcomp, hg2, hone]
      continuous_toFun := hrc g
      continuous_invFun := hrc g⁻¹ }
  have hc1 : cT (sigR R σ) (1 : Matrix (Fin n) (Fin n) (R ⊗[F] E)) = 1 := by
    unfold cT
    rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one]
  have key : ∀ (h h' A : Matrix (Fin n) (Fin n) (R ⊗[F] E)), h * h' = 1 →
      cT (sigR R σ) h' * (cT (sigR R σ) h * A * h) * h' = A := by
    intro h h' A hh
    have h1 : cT (sigR R σ) h' * cT (sigR R σ) h = 1 := by
      rw [← cT_mul, hh, hc1]
    calc cT (sigR R σ) h' * (cT (sigR R σ) h * A * h) * h'
        = (cT (sigR R σ) h' * cT (sigR R σ) h) * A * (h * h') := by
          simp only [Matrix.mul_assoc]
      _ = A := by rw [h1, hh, Matrix.one_mul, Matrix.mul_one]
  let τ' : HermR R σ n → HermR R σ n := fun S =>
    ⟨cT (sigR R σ) g⁻¹ * (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * g⁻¹, hmem S g⁻¹⟩
  have hcj : ∀ h : Matrix (Fin n) (Fin n) (R ⊗[F] E), Continuous fun S : HermR R σ n =>
      cT (sigR R σ) h * (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * h := fun h =>
    (continuous_const.matrix_mul continuous_subtype_val).matrix_mul continuous_const
  let τh : HermR R σ n ≃ₜ HermR R σ n :=
    { toFun := τ
      invFun := τ'
      left_inv := fun S => Subtype.ext (by
        show cT (sigR R σ) g⁻¹ * ((τ S : HermR R σ n) : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * g⁻¹ = S
        rw [hτ]
        exact key _ _ _ hg1)
      right_inv := fun S => Subtype.ext (by
        rw [hτ]
        exact key _ _ _ hg2)
      continuous_toFun := by
        refine Topology.IsInducing.subtypeVal.continuous_iff.2 ?_
        exact (hcj g).congr fun S => (hτ S).symm
      continuous_invFun := (hcj g⁻¹).subtype_mk _ }
  let B : Set (HermR R σ n) := {S | IsUnit (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det}
  have hBo : IsOpen B := by
    have : B = (fun S : HermR R σ n => (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det) ⁻¹'
        Set.range (Units.val : (R ⊗[F] E)ˣ → R ⊗[F] E) := by
      ext S
      rfl
    rw [this]
    exact hKu.isOpen_range.preimage continuous_subtype_val.matrix_det
  have hdet : ∀ h A : Matrix (Fin n) (Fin n) (R ⊗[F] E), IsUnit h.det → IsUnit A.det →
      IsUnit (cT (sigR R σ) h * A * h).det := by
    intro h A hh hA
    have h1 : (cT (sigR R σ) h).det = sigR R σ h.det := by
      rw [RingHom.map_det]
      simp [cT, Matrix.det_transpose]
    rw [Matrix.det_mul, Matrix.det_mul, h1]
    exact ((hh.map (sigR R σ)).mul hA).mul hh
  have hBτ : τh '' B = B := by
    ext S'
    constructor
    · rintro ⟨S, hS, rfl⟩
      show IsUnit ((τ S : HermR R σ n) : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det
      rw [hτ]
      exact hdet _ _ hg hS
    · intro hS'
      exact ⟨τh.symm S', hdet _ _ hgi hS', τh.apply_symm_apply _⟩
  have hU : G ⁻¹' B = {X | IsUnit (gramR R σ J X).det} := by
    ext X
    show IsUnit _ ↔ IsUnit _
    rw [hGe]
  have hfam : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ (gramR R σ J) Subtype.val (G ⁻¹' B) ν B m := by
    rw [hU]
    exact hm
  have hcomm : ∀ X, G (e X) = τh (G X) := by
    intro X
    apply Subtype.ext
    show ((G (rmul R X g) : HermR R σ n) : Matrix (Fin n) (Fin n) (R ⊗[F] E)) =
      ((τ (G X) : HermR R σ n) : Matrix (Fin n) (Fin n) (R ⊗[F] E))
    rw [← hGe, hτ, ← hGe]
    exact halg X g
  have htr := GlobalTheory.CompanionTheory.SW.isFibreFamily_transport _ _ _ μ ν (gramR R σ J) G Subtype.val
    Subtype.val_injective hGc hGe _ (gramR R σ J) G hGc hGe e τh hcomm B hBo m hfam
  rw [hBτ, hU] at htr
  have hmu' : μ.map e = a • μ := hmu
  have hnu' : ν.map τh = c • ν := hnu
  rw [hmu', hnu'] at htr
  have hnew : IsGramFib R σ J n (a • μ) (c • ν) (fun b => (m (τh.symm b)).map e) := htr
  have ha0 : a ≠ 0 := by
    rintro rfl
    have h0 : μ.map e = 0 := by rw [hmu', zero_smul]
    have h1 : (μ.map e) Set.univ = μ Set.univ := by
      rw [e.measurableEmbedding.map_apply, Set.preimage_univ]
    rw [h0] at h1
    exact (isOpen_univ.measure_pos μ Set.univ_nonempty).ne h1
  have hc0 : c ≠ 0 := by
    rintro rfl
    have h0 : ν.map τh = 0 := by rw [hnu', zero_smul]
    have h1 : (ν.map τh) Set.univ = ν Set.univ := by
      rw [τh.measurableEmbedding.map_apply, Set.preimage_univ]
    rw [h0] at h1
    exact (isOpen_univ.measure_pos ν Set.univ_nonempty).ne h1
  haveI hμa : (a • μ).IsAddHaarMeasure := Measure.IsAddHaarMeasure.nnreal_smul μ ha0
  haveI hνc : (c • ν).IsAddHaarMeasure := Measure.IsAddHaarMeasure.nnreal_smul ν hc0
  have hres := _root_.GlobalTheory.CompanionTheory.SW.Rescale.isGramFib_rescale F E σ hσ M J hJ R hR n μ ν m hμ hν hm a c ha0 hc0
  have huq := _root_.GlobalTheory.CompanionTheory.SW.GramFib.fibre_unique F E σ hσ M J hJ R hR n (a • μ) (c • ν) _ hμa hνc hres _ hnew (τ S)
  have hs : τh.symm (τ S) = S := τh.symm_apply_apply S
  simp only [hs] at huq
  have hfin : (m S).map (fun X => rmul R X g) = (a / c) • m (τ S) := huq.symm
  rw [hfin, smul_smul, mul_div_cancel₀ a hc0]

end GlobalTheory.CompanionTheory.SW.FibScale
end

