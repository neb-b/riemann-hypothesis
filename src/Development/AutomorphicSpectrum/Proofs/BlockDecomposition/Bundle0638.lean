module

public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.SiegelOneDescent.Descend2
public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0467
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalKTypeFinite
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0057
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CommuteRtOfMemZalg
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0630
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1310
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1477

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Jcpt
section
open PositivityTheory.RgEis PositivityTheory.RgEis.So

namespace GlobalTheory.CompanionTheory.RgEisSo

theorem jcpt : StdGood → GrpTop → JTop → JCpt := by
  intro hS hG hT F E R _ _ _ _ _ _ _ _ _ _ A ε ν r δ α ω ι _ _ i j hGood hB hi hJ
  show IsCompact (cK α j : Set (cover A ν ι))
  have hj : Continuous j := (hT F E R A ε ν r δ α ω ι i j hGood hB hi hJ).1
  obtain ⟨-, -, -, hUT2, -, -, hUK⟩ := hG E R A hGood ι ε
  have hν : Continuous ν := hB.cont

  have hmapν : Continuous (Matrix.GeneralLinearGroup.map (n := ι ⊕ ι) ν) := by
    refine Continuous.units_map _ ?_
    exact Continuous.matrix_map continuous_id hν
  let D : GL (ι ⊕ ι) R := dg ι (Units.map A.i.toMonoidHom δ)
  let M : GL (ι ⊕ ι) (NumberField.AdeleRing (NumberField.RingOfIntegers F) F) → GL (ι ⊕ ι) R :=
    fun h => D⁻¹ * Matrix.GeneralLinearGroup.map ν h * D
  have hM : Continuous M := (continuous_const.mul hmapν).mul continuous_const
  let φ : A.U ε ι × GL (ι ⊕ ι) (NumberField.AdeleRing (NumberField.RingOfIntegers F) F) → R :=
    fun p => ((p.1.1 * (M p.2)⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) (Sum.inl i) (Sum.inl i)
  let ψ : A.U ε ι × GL (ι ⊕ ι) (NumberField.AdeleRing (NumberField.RingOfIntegers F) F) → R :=
    fun p => ((M p.2 * (p.1.1)⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) (Sum.inl i) (Sum.inl i)
  have hval : Continuous (Subtype.val : A.U ε ι → GL (ι ⊕ ι) R) := continuous_subtype_val
  have hφ : Continuous φ := by
    have : Continuous fun p : A.U ε ι × GL (ι ⊕ ι) (NumberField.AdeleRing (NumberField.RingOfIntegers F) F) =>
        (p.1.1 * (M p.2)⁻¹ : GL (ι ⊕ ι) R) :=
      (hval.comp continuous_fst).mul (hM.comp continuous_snd).inv
    exact (Units.continuous_val.comp this).matrix_elem _ _
  have hψ : Continuous ψ := by
    have : Continuous fun p : A.U ε ι × GL (ι ⊕ ι) (NumberField.AdeleRing (NumberField.RingOfIntegers F) F) =>
        (M p.2 * (p.1.1)⁻¹ : GL (ι ⊕ ι) R) :=
      (hM.comp continuous_snd).mul (hval.comp continuous_fst).inv
    exact (Units.continuous_val.comp this).matrix_elem _ _

  have hrel : ∀ x : cover A ν ι, ((j x).1 : Matrix (ι ⊕ ι) (ι ⊕ ι) R) = (x.1.1 : R) • (M x.1.2 : Matrix (ι ⊕ ι) (ι ⊕ ι) R) :=
    fun x => hJ x
  have hφv : ∀ x : cover A ν ι, φ (j x, x.1.2) = (x.1.1 : R) := by
    intro x
    have e : (((j x).1 * (M x.1.2)⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) = (x.1.1 : R) • 1 := by
      rw [Units.val_mul, hrel x, Matrix.smul_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    show (((j x).1 * (M x.1.2)⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) (Sum.inl i) (Sum.inl i) = _
    rw [e]; simp
  have hψv : ∀ x : cover A ν ι, ψ (j x, x.1.2) = ((x.1.1⁻¹ : Rˣ) : R) := by
    intro x
    have e0 : (x.1.1 : R) • ((M x.1.2 * ((j x).1)⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) = 1 := by
      rw [Units.val_mul, ← Matrix.smul_mul, ← hrel x, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    have e : ((M x.1.2 * ((j x).1)⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) = ((x.1.1⁻¹ : Rˣ) : R) • 1 := by
      rw [← e0, smul_smul, Units.inv_mul, one_smul]
    show ((M x.1.2 * ((j x).1)⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) (Sum.inl i) (Sum.inl i) = _
    rw [e]; simp

  let C₂ : Set (GL (ι ⊕ ι) (NumberField.AdeleRing (NumberField.RingOfIntegers F) F)) :=
    ((((adStd F).kGL (ι ⊕ ι)).map (MulAut.conj (dg ι α)).toMonoidHom : Subgroup _) : Set _)
  have hC₂ : IsCompact C₂ := by
    have h0 := ((hS F).kcpt (ι ⊕ ι)).image
      (f := fun k => (MulAut.conj (dg ι α)).toMonoidHom k)
      (by
        show Continuous fun k => dg ι α * k * (dg ι α)⁻¹
        exact (continuous_const.mul continuous_id).mul continuous_const)
    exact h0
  let C₁ : Set (A.U ε ι) := (A.uK ε ι : Set (A.U ε ι))
  have hC : IsCompact (C₁ ×ˢ C₂) := hUK.prod hC₂
  have hS₁ := hC.image hφ
  have hS₂ : IsCompact (MulOpposite.op '' (ψ '' (C₁ ×ˢ C₂))) := (hC.image hψ).image MulOpposite.continuous_op
  let B : Set Rˣ := Units.embedProduct R ⁻¹' ((φ '' (C₁ ×ˢ C₂)) ×ˢ (MulOpposite.op '' (ψ '' (C₁ ×ˢ C₂))))
  have hBc : IsCompact B := Units.isClosedEmbedding_embedProduct.isCompact_preimage (hS₁.prod hS₂)

  have hdet : Continuous (Matrix.GeneralLinearGroup.det (n := ι ⊕ ι) (R := NumberField.AdeleRing (NumberField.RingOfIntegers F) F)) := by
    refine Units.continuous_iff.2 ⟨?_, ?_⟩
    · show Continuous fun g : GL (ι ⊕ ι) (NumberField.AdeleRing (NumberField.RingOfIntegers F) F) =>
        (g : Matrix (ι ⊕ ι) (ι ⊕ ι) (NumberField.AdeleRing (NumberField.RingOfIntegers F) F)).det
      exact Continuous.matrix_det Units.continuous_val
    · show Continuous fun g : GL (ι ⊕ ι) (NumberField.AdeleRing (NumberField.RingOfIntegers F) F) =>
        ((g⁻¹ : GL (ι ⊕ ι) (NumberField.AdeleRing (NumberField.RingOfIntegers F) F)) :
          Matrix (ι ⊕ ι) (ι ⊕ ι) (NumberField.AdeleRing (NumberField.RingOfIntegers F) F)).det
      exact Continuous.matrix_det (Units.continuous_val.comp continuous_inv)
  have hσ : Continuous A.σ := hGood.σcont
  have hUσ : Continuous (Units.map A.σ.toMonoidHom) := Continuous.units_map _ hσ
  have hUν : Continuous (Units.map ν.toMonoidHom) := Continuous.units_map _ hν
  have hcl : IsClosed ((cover A ν ι : Subgroup _) : Set (Rˣ × GL (ι ⊕ ι) (NumberField.AdeleRing (NumberField.RingOfIntegers F) F))) := by
    have hf : Continuous fun p : Rˣ × GL (ι ⊕ ι) (NumberField.AdeleRing (NumberField.RingOfIntegers F) F) =>
        p.1 * Units.map A.σ.toMonoidHom p.1 * Units.map ν.toMonoidHom (Matrix.GeneralLinearGroup.det p.2) :=
      (continuous_fst.mul (hUσ.comp continuous_fst)).mul (hUν.comp (hdet.comp continuous_snd))
    exact isClosed_singleton.preimage hf
  have hemb := hcl.isClosedEmbedding_subtypeVal
  have hP : IsCompact ((Subtype.val : cover A ν ι → _) ⁻¹' (B ×ˢ C₂)) :=
    hemb.isCompact_preimage (hBc.prod hC₂)
  have hprj : Continuous (prj A ν ι) := continuous_snd.comp continuous_subtype_val
  have hclK : IsClosed (cK α j : Set (cover A ν ι)) := by
    set_option synthInstance.maxHeartbeats 200000 in
      exact (hUK.isClosed.preimage hj).inter (hC₂.isClosed.preimage hprj)
  refine hP.of_isClosed_subset hclK ?_
  intro x hx
  have h1 : j x ∈ C₁ := hx.1
  have h2 : x.1.2 ∈ C₂ := hx.2
  refine ⟨?_, h2⟩
  refine ⟨⟨(j x, x.1.2), ⟨h1, h2⟩, hφv x⟩, ⟨ψ (j x, x.1.2), ⟨(j x, x.1.2), ⟨h1, h2⟩, rfl⟩, ?_⟩⟩
  rw [hψv x]
  rfl

end GlobalTheory.CompanionTheory.RgEisSo
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Jtop
section
open PositivityTheory.RgEis PositivityTheory.RgEis.So
open NumberField Matrix
open scoped NumberField.AdeleRing

namespace GlobalTheory.CompanionTheory.EisSo

theorem jtop : JTop := by
  intro F E R _ _ _ _ _ _ _ _ _ _ A ε ν _ δ _ _ ι _ _ _ j hA hB _ hJ
  have hcv : Continuous ν := hB.cont

  have hval : Continuous fun x : cover A ν ι => (((j x).1 : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) := by
    have e : (fun x : cover A ν ι => (((j x).1 : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R)) = fun x =>
        (x.1.1 : R) • ((((dg ι (Units.map A.i.toMonoidHom δ))⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) *
          ((x.1.2 : Matrix (ι ⊕ ι) (ι ⊕ ι) 𝔸[F]).map ν) *
          ((dg ι (Units.map A.i.toMonoidHom δ) : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R)) := by
      funext x; rw [hJ x]; rfl
    rw [e]
    have h1 : Continuous fun x : cover A ν ι => (x.1.1 : R) :=
      Units.continuous_val.comp (continuous_fst.comp continuous_subtype_val)
    have h2 : Continuous fun x : cover A ν ι => (x.1.2 : Matrix (ι ⊕ ι) (ι ⊕ ι) 𝔸[F]) :=
      Units.continuous_val.comp (continuous_snd.comp continuous_subtype_val)
    exact h1.smul ((continuous_const.matrix_mul (h2.matrix_map hcv)).matrix_mul continuous_const)
  have hjGL : Continuous fun x : cover A ν ι => ((j x).1 : GL (ι ⊕ ι) R) := by
    refine Units.continuous_iff.2 ⟨hval, ?_⟩
    have e : (fun x : cover A ν ι => (((((j x).1 : GL (ι ⊕ ι) R))⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R)) =
        (fun x : cover A ν ι => (((j x).1 : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R)) ∘ fun x => x⁻¹ := by
      funext x; simp [map_inv]
    rw [e]; exact hval.comp continuous_inv
  have hum : ∀ {S T : Type} [CommRing S] [CommRing T] [TopologicalSpace S] [TopologicalSpace T]
      [IsTopologicalRing S] (φ : S →+* T), Continuous φ → Continuous (Units.map φ.toMonoidHom) := by
    intro S T _ _ _ _ _ φ hφ
    exact Units.continuous_iff.2 ⟨hφ.comp Units.continuous_val, hφ.comp (Units.continuous_val.comp continuous_inv)⟩
  have hdet : Continuous (Matrix.GeneralLinearGroup.det : GL (ι ⊕ ι) 𝔸[F] → 𝔸[F]ˣ) :=
    Units.continuous_iff.2 ⟨Units.continuous_val.matrix_det, (Units.continuous_val.comp continuous_inv).matrix_det⟩
  haveI : SecondCountableTopology Rᵐᵒᵖ := MulOpposite.opHomeomorph.symm.secondCountableTopology
  haveI : SecondCountableTopology (Matrix (ι ⊕ ι) (ι ⊕ ι) 𝔸[F]) := inferInstanceAs (SecondCountableTopology (ι ⊕ ι → ι ⊕ ι → 𝔸[F]))
  haveI : SecondCountableTopology (Matrix (ι ⊕ ι) (ι ⊕ ι) 𝔸[F])ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.secondCountableTopology
  haveI : SecondCountableTopology Rˣ := Units.isEmbedding_embedProduct.secondCountableTopology
  haveI : SecondCountableTopology (GL (ι ⊕ ι) 𝔸[F]) := Units.isEmbedding_embedProduct.secondCountableTopology
  haveI : LocallyCompactSpace Rˣ := Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  haveI : LocallyCompactSpace (GL (ι ⊕ ι) 𝔸[F]) := Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  have hf : Continuous fun x : Rˣ × GL (ι ⊕ ι) 𝔸[F] =>
      x.1 * Units.map A.σ.toMonoidHom x.1 * Units.map ν.toMonoidHom (Matrix.GeneralLinearGroup.det x.2) :=
    (continuous_fst.mul ((hum A.σ hA.σcont).comp continuous_fst)).mul ((hum ν hcv).comp (hdet.comp continuous_snd))
  have hcl : IsClosed (cover A ν ι : Set (Rˣ × GL (ι ⊕ ι) 𝔸[F])) := by
    have e : (cover A ν ι : Set (Rˣ × GL (ι ⊕ ι) 𝔸[F])) = (fun x : Rˣ × GL (ι ⊕ ι) 𝔸[F] =>
        x.1 * Units.map A.σ.toMonoidHom x.1 * Units.map ν.toMonoidHom (Matrix.GeneralLinearGroup.det x.2)) ⁻¹' {1} :=
      Set.ext fun x => Iff.rfl
    rw [e]; exact isClosed_singleton.preimage hf
  haveI : SecondCountableTopology (Rˣ × GL (ι ⊕ ι) 𝔸[F]) := inferInstance
  exact ⟨hjGL.subtype_mk _, inferInstance, hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace,
    Topology.IsEmbedding.subtypeVal.secondCountableTopology⟩

end GlobalTheory.CompanionTheory.EisSo
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KFiniteIrreducibleFixedVectors
section
noncomputable section

open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CompanionTheory.SmoothRep
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.TypeSpace

section Abstract

variable {K X : Type*} [Group K] [NormedAddCommGroup X] [InnerProductSpace ℂ X]

def restrictRep (π : K →* (X →L[ℂ] X)) (Y : Submodule ℂ X) (hY : ∀ g, ∀ v ∈ Y, π g v ∈ Y) :
    Representation ℂ K Y where
  toFun g := ((π g : X →L[ℂ] X) : X →ₗ[ℂ] X).restrict (hY g)
  map_one' := by ext v; simp
  map_mul' g h := by ext v; simp

theorem span_orbit_stable' (π : K →* (X →L[ℂ] X)) (F : X) (g : K) :
    ∀ v ∈ Submodule.span ℂ (Set.range fun k : K => π k F),
      π g v ∈ Submodule.span ℂ (Set.range fun k : K => π k F) := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, rfl⟩ := hx
    refine Submodule.subset_span ⟨g * k, ?_⟩
    simp [map_mul]
  | zero => simp
  | add x y _ _ hx hy => simpa using add_mem hx hy
  | smul c x _ hx => simpa using Submodule.smul_mem _ c hx

end Abstract

theorem exists_typeSpace : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (H : Submodule ℂ (L2 (latticeGL E a) μ)), H ≤ L2cusp μ → IsIrredSubrep (R (latticeGL E a) μ) H → ∀ F ∈ H, IsKFinL2 μ F → ∃ U : Subgroup (GL (Fin a) (Af E)), IsOpen (U : Set (GL (Fin a) (Af E))) ∧ IsCompact (U : Set (GL (Fin a) (Af E))) ∧ ∃ X : Submodule ℂ (L2 (latticeGL E a) μ), FiniteDimensional ℂ X ∧ F ∈ X ∧ X ≤ H ∧ (∀ (k : Kinf E a), ∀ v ∈ X, R (latticeGL E a) μ (infGL E a (Unitary.toUnits k)) v ∈ X) ∧ (∀ u ∈ U, ∀ v ∈ X, R (latticeGL E a) μ (finGL E a u) v = v) ∧ ∀ B : L2 (latticeGL E a) μ →ₗ[ℂ] L2 (latticeGL E a) μ, (∀ (k : Kinf E a) v, B (R (latticeGL E a) μ (infGL E a (Unitary.toUnits k)) v) = R (latticeGL E a) μ (infGL E a (Unitary.toUnits k)) (B v)) → (∀ v ∈ H, (∀ u ∈ U, R (latticeGL E a) μ (finGL E a u) v = v) → B v ∈ H ∧ ∀ u ∈ U, R (latticeGL E a) μ (finGL E a u) (B v) = B v) → ∀ v ∈ X, B v ∈ X := by
  intro E _ _ _ a μ _ _ H hH hI F hFH hK
  obtain ⟨hSo, hfd⟩ := hK
  obtain ⟨K0, hK0o, hK0c⟩ := GlobalTheory.GLIntegral.exists_isOpen_isCompact E a

  let S : Subgroup (GL (Fin a) (Af E)) :=
    { carrier := {k | R (latticeGL E a) μ (finGL E a k) F = F}
      mul_mem' := fun {x y} hx hy => by
        have hx' : R (latticeGL E a) μ (finGL E a x) F = F := hx
        have hy' : R (latticeGL E a) μ (finGL E a y) F = F := hy
        change R (latticeGL E a) μ (finGL E a (x * y)) F = F
        rw [map_mul, map_mul, ContinuousLinearMap.mul_apply, hy', hx']
      one_mem' := by
        change R (latticeGL E a) μ (finGL E a 1) F = F
        simp
      inv_mem' := fun {x} hx => by
        have hx' : R (latticeGL E a) μ (finGL E a x) F = F := hx
        change R (latticeGL E a) μ (finGL E a x⁻¹) F = F
        conv_lhs => rw [← hx']
        rw [← ContinuousLinearMap.mul_apply, ← map_mul, ← map_mul, inv_mul_cancel]
        simp }
  have hSo' : IsOpen (S : Set (GL (Fin a) (Af E))) := hSo
  let U : Subgroup (GL (Fin a) (Af E)) := K0 ⊓ S
  have hUo : IsOpen (U : Set (GL (Fin a) (Af E))) := hK0o.inter hSo'
  have hUc : IsCompact (U : Set (GL (Fin a) (Af E))) := hK0c.inter_right (S.isClosed_of_isOpen hSo')

  let π : Kinf E a →* (L2 (latticeGL E a) μ →L[ℂ] L2 (latticeGL E a) μ) :=
    (R (latticeGL E a) μ).comp ((infGL E a).comp Unitary.toUnits)
  have hcomm : ∀ (u : GL (Fin a) (Af E)) (k : Kinf E a) (v : L2 (latticeGL E a) μ),
      R (latticeGL E a) μ (finGL E a u) (π k v) = π k (R (latticeGL E a) μ (finGL E a u) v) := by
    intro u k v
    have e := congrArg (fun g => R (latticeGL E a) μ g v) (infGL_comm (E := E) (a := a) (Unitary.toUnits k) u)
    simp only [map_mul, ContinuousLinearMap.mul_apply] at e
    exact e.symm
  let Y : Submodule ℂ (L2 (latticeGL E a) μ) := Submodule.span ℂ (Set.range fun k : Kinf E a => π k F)
  haveI : FiniteDimensional ℂ Y := hfd
  have hYs : ∀ g, ∀ v ∈ Y, π g v ∈ Y := span_orbit_stable' π F
  have hFY : F ∈ Y := Submodule.subset_span ⟨1, by simp⟩
  have hYP : ∀ v ∈ Y, v ∈ H ∧ ∀ u ∈ U, R (latticeGL E a) μ (finGL E a u) v = v := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      refine ⟨hI.1.2 _ _ hFH, fun u hu => ?_⟩
      exact (hcomm u k F).trans (congrArg (π k) hu.2)
    | zero => exact ⟨H.zero_mem, fun _ _ => map_zero _⟩
    | add x y _ _ hx hy =>
      exact ⟨H.add_mem hx.1 hy.1, fun u hu => by rw [map_add (f := _), hx.2 u hu, hy.2 u hu]⟩
    | smul c x _ hx =>
      exact ⟨H.smul_mem c hx.1, fun u hu => by rw [map_smul, hx.2 u hu]⟩
  let ρ : Representation ℂ (Kinf E a) Y := restrictRep π Y hYs
  let C : (Y →ₗ[ℂ] L2 (latticeGL E a) μ) → Prop := fun T =>
    (∀ k w, T (ρ k w) = R (latticeGL E a) μ (infGL E a (Unitary.toUnits k)) (T w)) ∧
      ∀ w, T w ∈ H ∧ ∀ u ∈ U, R (latticeGL E a) μ (finGL E a u) (T w) = T w
  let X : Submodule ℂ (L2 (latticeGL E a) μ) := ⨆ (T : Y →ₗ[ℂ] L2 (latticeGL E a) μ) (_ : C T), LinearMap.range T
  have hXf : FiniteDimensional ℂ X := _root_.GlobalTheory.CompanionTheory.IsoTypes.finiteDimensional_isotypic E a μ H hH hI U hUo Y ρ
  have hmem : ∀ T, C T → ∀ w, T w ∈ X := fun T hT w =>
    (le_iSup₂_of_le (f := fun (T : Y →ₗ[ℂ] L2 (latticeGL E a) μ) (_ : C T) => LinearMap.range T) T hT le_rfl)
      ⟨w, rfl⟩
  have hXP : ∀ v ∈ X, v ∈ H ∧ ∀ u ∈ U, R (latticeGL E a) μ (finGL E a u) v = v := by
    intro v hv
    let P : Submodule ℂ (L2 (latticeGL E a) μ) :=
      { carrier := {v | v ∈ H ∧ ∀ u ∈ U, R (latticeGL E a) μ (finGL E a u) v = v}
        zero_mem' := ⟨H.zero_mem, fun _ _ => map_zero _⟩
        add_mem' := fun {x y} hx hy =>
          ⟨H.add_mem hx.1 hy.1, fun u hu => by rw [map_add (f := _), hx.2 u hu, hy.2 u hu]⟩
        smul_mem' := fun c x hx => ⟨H.smul_mem c hx.1, fun u hu => by rw [map_smul, hx.2 u hu]⟩ }
    have hle : X ≤ P := iSup₂_le fun T hT => by
      rintro _ ⟨w, rfl⟩
      exact hT.2 w
    exact hle hv
  refine ⟨U, hUo, hUc, X, hXf, ?_, fun v hv => (hXP v hv).1, ?_, fun u hu v hv => (hXP v hv).2 u hu, ?_⟩
  · exact hmem Y.subtype ⟨fun k w => rfl, fun w => hYP _ w.2⟩ ⟨F, hFY⟩
  · intro k v hv
    have hle : X ≤ X.comap ((R (latticeGL E a) μ (infGL E a (Unitary.toUnits k)) :
        L2 (latticeGL E a) μ →L[ℂ] L2 (latticeGL E a) μ) : L2 (latticeGL E a) μ →ₗ[ℂ] L2 (latticeGL E a) μ) :=
      iSup₂_le fun T hT => by
        rintro _ ⟨w, rfl⟩
        change R (latticeGL E a) μ (infGL E a (Unitary.toUnits k)) (T w) ∈ X
        rw [← hT.1 k w]
        exact hmem T hT _
    exact hle hv
  · intro B hB1 hB2 v hv
    have hle : X ≤ X.comap B := iSup₂_le fun T hT => by
      rintro _ ⟨w, rfl⟩
      refine hmem (B ∘ₗ T) ⟨fun k w => ?_, fun w => hB2 _ (hT.2 w).1 (hT.2 w).2⟩ w
      change B (T (ρ k w)) = _
      rw [hT.1 k w, hB1]
      rfl
    exact hle hv

end GlobalTheory.CompanionTheory.TypeSpace

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviEmbeddingHeightBound
section
open NumberField GlobalTheory.CuspRep GlobalTheory.CompanionTheory.CTFin Matrix

noncomputable section
namespace GlobalTheory.CompanionTheory.CTFin.Slice1.Height
variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {r s : ℕ}

theorem norm_one_le : ‖(1 : Cinf E)‖ ≤ 1 := by
  exact (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => by simp

theorem norm_lev_le (y : GL (Fin r) (Cinf E)) :
    ‖toL (lev (Cinf E) r s (y, 1)).val‖ ≤ ‖toL y.val‖ + 1 := by
  have n0 := norm_nonneg (toL y.val)
  have hent : ∀ i j, ‖(y.val i j : Cinf E)‖ ≤ ‖toL y.val‖ := fun i j =>
    (norm_le_pi_norm (toL y.val i) j).trans (norm_le_pi_norm (toL y.val) i)
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i =>
    (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
  change ‖((lev (Cinf E) r s (y, 1) : GL _ _) : Matrix _ _ (Cinf E)) i j‖ ≤ _
  have hv : ((lev (Cinf E) r s (y, 1) : GL _ _) : Matrix _ _ (Cinf E)) =
      Matrix.reindex (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s))
        (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s))
        (Matrix.fromBlocks y.val 0 0 (1 : Matrix (Fin s) (Fin s) (Cinf E))) := by
    ext i j
    obtain ⟨a, rfl⟩ := (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).surjective i
    obtain ⟨b, rfl⟩ := (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).surjective j
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply]
    rcases a with a | a <;> rcases b with b | b <;>
      simp [lev, GlobalTheory.SmGL.emb₂, GlobalTheory.SmGL.leviEmb,
        GlobalTheory.SmGL.leviTwo, GlobalTheory.SmGL.two, Matrix.blockDiagonal'_apply]
  rw [hv]
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
  generalize (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).symm i = i'
  generalize (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).symm j = j'
  rcases i' with i' | i' <;> rcases j' with j' | j'
  · simpa using (hent i' j').trans (by linarith)
  · simp; linarith
  · simp; linarith
  · have h1 : ‖((1 : Matrix (Fin s) (Fin s) (Cinf E)) i' j')‖ ≤ 1 := by
      by_cases h : i' = j'
      · subst h; simpa using norm_one_le
      · simp [Matrix.one_apply_ne h]
    simpa using h1.trans (by linarith)

theorem height_lev_le (y : GL (Fin r) (Cinf E)) :
    height (lev (Cinf E) r s (y, 1)) ≤ 3 * height y := by
  have e : (lev (Cinf E) r s (y, 1))⁻¹ = lev (Cinf E) r s (y⁻¹, 1) := by
    rw [← map_inv, Prod.inv_mk, inv_one]
  have h1 := norm_lev_le (s := s) y
  have h2 := norm_lev_le (s := s) y⁻¹
  have n1 := norm_nonneg (toL y.val)
  have n2 := norm_nonneg (toL (y⁻¹).val)
  unfold height
  rw [e]
  linarith

end GlobalTheory.CompanionTheory.CTFin.Slice1.Height

theorem GlobalTheory.CompanionTheory.CTFin.Slice1.height_lev_mul_le : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (r s : ℕ) (c : GL (Fin (r + s)) (Cinf E)), ∃ B : ℝ, 0 ≤ B ∧ ∀ y : GL (Fin r) (Cinf E), height (lev (Cinf E) r s (y, 1) * c) ≤ B * height y := by
  intro E _ _ _ r s c
  have hb : 0 ≤ GlobalTheory.CompanionTheory.GrowthConv.bnd c := by
    unfold GlobalTheory.CompanionTheory.GrowthConv.bnd
    positivity
  refine ⟨3 * GlobalTheory.CompanionTheory.GrowthConv.bnd c, by positivity, fun y => ?_⟩
  refine (GlobalTheory.CompanionTheory.GrowthConv.height_mul_le_bnd c _).trans ?_
  have := mul_le_mul_of_nonneg_left (Height.height_lev_le (s := s) y) hb
  linarith

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemProdOfMemTsupport
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.FinPol

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem continuous_nrmL (hU : Unr E) (n : ℕ) (w : Pl E) : Continuous (nrmL n w) := by
  have ht := ThBasic.continuous_thL hU n w
  by_cases hs : IsSplitAt w
  · have e : nrmL n w = id := funext fun y => by simp [nrmL, hs]
    rw [e]
    exact continuous_id
  · have e : nrmL n w = fun y => y * thL n w y := funext fun y => by simp [nrmL, thL, hs]
    rw [e]
    exact continuous_id.mul ht

theorem isClosed_KGL (hU : Unr E) (n : ℕ) (w : Pl E) :
    IsClosed (GlobalTheory.LFun.KGL w (n := n) : Set (GLw n w)) :=
  (ThBasic.twist_basic E hU n w).2.2.2.2.2.1.isClosed

theorem nrmL_mem_KGL (hU : Unr E) (n : ℕ) (w : Pl E) {y : GLw n w} (hy : y ∈ GlobalTheory.LFun.KGL w (n := n)) :
    nrmL n w y ∈ GlobalTheory.LFun.KGL w (n := n) := by
  have ht := ThBasic.thL_mem_KGL hU n w y hy
  unfold nrmL
  unfold thL at ht
  split_ifs at ht ⊢ with hs
  · exact hy
  · exact mul_mem hy ht

theorem mem_prod_of_mem_tsupport (hU : Unr E) (a b : ℕ) (w : Pl E) {y : GLw a w × GLw b w}
    (hy : y ∈ tsupport ((((GlobalTheory.LFun.KGL w (n := a)).prod (GlobalTheory.LFun.KGL w (n := b))) : Set (GLw a w × GLw b w)).indicator
      (1 : GLw a w × GLw b w → ℂ))) :
    y.1 ∈ GlobalTheory.LFun.KGL w (n := a) ∧ y.2 ∈ GlobalTheory.LFun.KGL w (n := b) := by
  have hcl : IsClosed (((GlobalTheory.LFun.KGL w (n := a)).prod (GlobalTheory.LFun.KGL w (n := b))) : Set (GLw a w × GLw b w)) := by
    rw [Subgroup.coe_prod]
    exact (isClosed_KGL hU a w).prod (isClosed_KGL hU b w)
  have h := closure_minimal Set.support_indicator_subset hcl hy
  exact Subgroup.mem_prod.1 h

theorem finite_pairs : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (a b : ℕ) (S : Set (Pl E)), IsSection S → ∀ φ : ∀ w : Pl E, GLw a w × GLw b w → ℂ, (∀ w, HasCompactSupport (φ w)) → (∀ᶠ w in cofinite, φ w = (((GlobalTheory.LFun.KGL w (n := a)).prod (GlobalTheory.LFun.KGL w (n := b))) : Set (GLw a w × GLw b w)).indicator 1) → {p : E[X] × E[X] | p.1 ∈ Ell E a ∧ p.2 ∈ Ell E b ∧ ∀ w ∈ S, ∃ y : GLw a w × GLw b w, φ w y ≠ 0 ∧ (nrmL a w y.1).val.charpoly = atPl w p.1 ∧ (nrmL b w y.2).val.charpoly = atPl w p.2}.Finite := by
  intro E _ _ _ hU a b S hS φ hc hφ
  let C₁ : ∀ w : Pl E, Set (GLw a w) := fun w => nrmL a w '' (Prod.fst '' tsupport (φ w))
  let C₂ : ∀ w : Pl E, Set (GLw b w) := fun w => nrmL b w '' (Prod.snd '' tsupport (φ w))
  have hC₁ : ∀ w, IsCompact (C₁ w) := fun w =>
    ((hc w).isCompact.image continuous_fst).image (continuous_nrmL hU a w)
  have hC₂ : ∀ w, IsCompact (C₂ w) := fun w =>
    ((hc w).isCompact.image continuous_snd).image (continuous_nrmL hU b w)
  have hK₁ : ∀ᶠ w in cofinite, C₁ w ⊆ GlobalTheory.LFun.KGL w (n := a) := by
    filter_upwards [hφ] with w hw
    rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    rw [hw] at hy
    exact nrmL_mem_KGL hU a w (mem_prod_of_mem_tsupport hU a b w hy).1
  have hK₂ : ∀ᶠ w in cofinite, C₂ w ⊆ GlobalTheory.LFun.KGL w (n := b) := by
    filter_upwards [hφ] with w hw
    rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    rw [hw] at hy
    exact nrmL_mem_KGL hU b w (mem_prod_of_mem_tsupport hU a b w hy).2
  refine ((GlobalTheory.T.finite_ellipticCharpoly_compact_section E a S hS C₁ hC₁ hK₁).prod (GlobalTheory.T.finite_ellipticCharpoly_compact_section E b S hS C₂ hC₂ hK₂)).subset ?_
  rintro p ⟨h₁, h₂, h⟩
  refine ⟨⟨h₁, fun w hw => ?_⟩, ⟨h₂, fun w hw => ?_⟩⟩
  · obtain ⟨y, hy, e₁, -⟩ := h w hw
    exact ⟨_, ⟨y.1, ⟨y, subset_tsupport _ hy, rfl⟩, rfl⟩, e₁⟩
  · obtain ⟨y, hy, -, e₂⟩ := h w hw
    exact ⟨_, ⟨y.2, ⟨y, subset_tsupport _ hy, rfl⟩, rfl⟩, e₂⟩

end GlobalTheory.CompanionTheory.FinPol
end
end

