module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0102
public import Formalism.LocalToGlobal.KernelLattices.ThDistC
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeasurableSetPreSingleton
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0104
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0103
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlockActionDiagonalCoefficientSpaceSmulStatement
section
open Formalism.L2.Ker MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blockAction_diagonal_coefficientSpace_smul : ∀ {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → Formalism.BasicNotions.DomWeight n) (c : ι → ℂ) (Q : Formalism.L2.DIV.Pol ℂ ι n), Q ∈ Formalism.L2.DIV.VV ℂ lam → Formalism.GradedWeylDivisibility.blockAct ℂ (fun τ => Matrix.diagonal fun _ : Fin n => c τ) Q = (∏ τ, c τ ^ ∑ a, (lam τ).natW a) • Q := by
  first | exact @GlobalTheory.blockAct_diag_mem_VV | exact GlobalTheory.blockAct_diag_mem_VV | (intros; apply GlobalTheory.blockAct_diag_mem_VV <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlockVolumeProd
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound

noncomputable section
namespace GlobalTheory.BlockVolume

variable {k : Type} [MeasurableSpace k] (ν : Measure k) [SigmaFinite ν]

def rowSplit (A D : Type) [Fintype A] [Fintype D] :
    ((A ⊕ D) → k) ≃ᵐ ((A → k) × (D → k)) :=
  MeasurableEquiv.sumPiEquivProdPi (fun _ : A ⊕ D => k)

theorem rowSplit_mp (A D : Type) [Fintype A] [Fintype D] :
    MeasurePreserving (rowSplit (k := k) A D) (Measure.pi fun _ : A ⊕ D => ν)
      ((Measure.pi fun _ : A => ν).prod (Measure.pi fun _ : D => ν)) :=
  measurePreserving_sumPiEquivProdPi (fun _ : A ⊕ D => ν)

def colSplit (R A D : Type) [Fintype R] [Fintype A] [Fintype D] :
    (R → (A ⊕ D) → k) ≃ᵐ ((R → A → k) × (R → D → k)) :=
  (MeasurableEquiv.piCongrRight fun _ : R => rowSplit (k := k) A D).trans
    (MeasurableEquiv.arrowProdEquivProdArrow (A → k) (D → k) R)

theorem colSplit_mp (R A D : Type) [Fintype R] [Fintype A] [Fintype D] :
    MeasurePreserving (colSplit (k := k) R A D)
      (Measure.pi fun _ : R => Measure.pi fun _ : A ⊕ D => ν)
      ((Measure.pi fun _ : R => Measure.pi fun _ : A => ν).prod
        (Measure.pi fun _ : R => Measure.pi fun _ : D => ν)) := by
  have h1 := measurePreserving_pi (fun _ : R => Measure.pi fun _ : A ⊕ D => ν)
    (fun _ : R => (Measure.pi fun _ : A => ν).prod (Measure.pi fun _ : D => ν))
    (fun _ => rowSplit_mp ν A D)
  have h2 := measurePreserving_arrowProdEquivProdArrow (A → k) (D → k) R
    (fun _ => Measure.pi fun _ : A => ν) (fun _ => Measure.pi fun _ : D => ν)
  exact h2.comp h1

def blockSplit (A D : Type) [Fintype A] [Fintype D] :
    ((A ⊕ D) → (A ⊕ D) → k) ≃ᵐ (((A → A → k) × (A → D → k)) × ((D → A → k) × (D → D → k))) :=
  (MeasurableEquiv.sumPiEquivProdPi (fun _ : A ⊕ D => (A ⊕ D) → k)).trans
    (MeasurableEquiv.prodCongr (colSplit A A D) (colSplit D A D))

def blockEquiv (A D : Type) [Fintype A] [Fintype D] :
    Matrix (A ⊕ D) (A ⊕ D) k ≃ᵐ ((Matrix A A k × Matrix A D k) × (Matrix D A k × Matrix D D k)) :=
  blockSplit (k := k) A D

theorem blockSplit_mp (A D : Type) [Fintype A] [Fintype D] :
    MeasurePreserving (blockEquiv (k := k) A D) (volM ν (A ⊕ D) (A ⊕ D))
      (((volM ν A A).prod (volM ν A D)).prod ((volM ν D A).prod (volM ν D D))) := by
  have h1 := measurePreserving_sumPiEquivProdPi (fun _ : A ⊕ D => Measure.pi fun _ : A ⊕ D => ν)
  have h2 := (colSplit_mp ν A A D).prod (colSplit_mp ν D A D)
  exact h2.comp h1

end GlobalTheory.BlockVolume

theorem GlobalTheory.blockVolume_prod : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure]
    (A D : Type) [Fintype A] [Fintype D] (S₁₁ : Set (Matrix A A k)) (S₁₂ : Set (Matrix A D k))
    (S₂₁ : Set (Matrix D A k)) (S₂₂ : Set (Matrix D D k)),
    volM ν (A ⊕ D) (A ⊕ D)
        {x | x.toBlocks₁₁ ∈ S₁₁ ∧ x.toBlocks₁₂ ∈ S₁₂ ∧ x.toBlocks₂₁ ∈ S₂₁ ∧ x.toBlocks₂₂ ∈ S₂₂} =
      volM ν A A S₁₁ * volM ν A D S₁₂ * volM ν D A S₂₁ * volM ν D D S₂₂ := by
  intro k _ _ _ _ _ _ ν _ A D _ _ S₁₁ S₁₂ S₂₁ S₂₂
  haveI := GlobalTheory.IndexVolume.secondCountable k
  haveI : SigmaFinite ν := inferInstance
  haveI hσ : ∀ (m n : Type) [Fintype m] [Fintype n], SigmaFinite (volM ν m n) := fun m n _ _ => by
    exact (inferInstance : SigmaFinite (Measure.pi fun _ : m => Measure.pi fun _ : n => ν :
      Measure (m → n → k)))
  haveI := hσ A A; haveI := hσ A D; haveI := hσ D A; haveI := hσ D D
  have hmp := GlobalTheory.BlockVolume.blockSplit_mp ν A D
  have hset : {x : Matrix (A ⊕ D) (A ⊕ D) k | x.toBlocks₁₁ ∈ S₁₁ ∧ x.toBlocks₁₂ ∈ S₁₂ ∧
      x.toBlocks₂₁ ∈ S₂₁ ∧ x.toBlocks₂₂ ∈ S₂₂} =
      GlobalTheory.BlockVolume.blockEquiv (k := k) A D ⁻¹' ((S₁₁ ×ˢ S₁₂) ×ˢ (S₂₁ ×ˢ S₂₂)) := by
    ext x
    exact ⟨fun ⟨h1, h2, h3, h4⟩ => ⟨⟨h1, h2⟩, h3, h4⟩, fun ⟨⟨h1, h2⟩, h3, h4⟩ => ⟨h1, h2, h3, h4⟩⟩
  rw [hset]
  have h := hmp.measure_preimage_equiv ((S₁₁ ×ˢ S₁₂) ×ˢ (S₂₁ ×ˢ S₂₂))
  refine h.trans ?_
  rw [Measure.prod_prod, Measure.prod_prod, Measure.prod_prod]
  ring
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChainStepIdentities
section
noncomputable section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound

namespace GlobalTheory.ChainStepIdentities

theorem volAdd_eq (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (ν : Measure k) (hν : IsUnitVol ν) (r : ℕ) :
    volAdd ν r = ∏ i ∈ Finset.Icc 1 r, (zetaAt (resCard k) i)⁻¹ := by
  have := hν.1
  have h := GlobalTheory.IndexVolume.volumeOfGL ν hν.2 (Fin r)
  have hS : (Units.val '' (KO k (Fin r) : Set (GL (Fin r) k)) : Set (Matrix (Fin r) (Fin r) k)) =
      GlobalTheory.IndefiniteRowSideFullHecke.GLVolumeIndex.groupSet (⊤ : Subgroup (GL (Fin r) 𝒪[k])) := by
    ext x
    constructor
    · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
      exact ⟨g, trivial, rfl⟩
    · rintro ⟨g, -, rfl⟩
      exact ⟨_, ⟨g, rfl⟩, rfl⟩
  have e : volAdd ν r = GlobalTheory.IndefiniteRowSideFullHecke.GLVolumeIndex.volGroup ν (⊤ : Subgroup (GL (Fin r) 𝒪[k])) := by
    unfold volAdd GlobalTheory.IndefiniteRowSideFullHecke.GLVolumeIndex.volGroup
    rw [hS]
    rfl
  rw [e, h, Fintype.card_fin, Formalism.MainNotions.ZetaProductPairs.qE]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp [zetaAt, GlobalTheory.IndefiniteRowSideFullHecke.GLVolumeIndex.resCard, resCard, _root_.zpow_neg, _root_.zpow_natCast]

end GlobalTheory.ChainStepIdentities
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ComplexDerivativeAdjointOfSkewForm
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct

namespace GlobalTheory.RderCAdjoint

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)

theorem Rder_neg_dir (τ : D.what₂.Tau) (X : Matrix (Fin V.rank) (Fin V.rank) ℂ) (φ : GA D V → ℂ) :
    Rder θ V τ (-X) φ = -Rder θ V τ X φ := by
  funext g
  have := deriv_comp_neg (fun t : ℝ => φ (g * oneP θ V τ X t)) 0
  simpa only [Rder, oneP, smul_neg, neg_smul, neg_zero, Pi.neg_apply] using this

theorem conjAt_adjoint (τ : D.what₂.Tau) (Z : Matrix (Fin V.rank) (Fin V.rank) ℂ) :
    conjAt V τ ((gramAt D V τ)⁻¹ * Zᴴ * gramAt D V τ) = -Z := by
  have hu := GlobalTheory.SmoothAutCheck.gramAt_unit V τ
  have hH := GlobalTheory.SmoothAutCheck.gramAt_herm V τ
  unfold conjAt
  rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_nonsing_inv, hH,
    ← mul_assoc, nonsing_inv_mul _ hu, one_mul, mul_assoc, nonsing_inv_mul _ hu, mul_one]

theorem RderC_adjoint_eq (τ : D.what₂.Tau) (Z : Matrix (Fin V.rank) (Fin V.rank) ℂ) (φ : GA D V → ℂ) :
    RderC θ V τ ((gramAt D V τ)⁻¹ * Zᴴ * gramAt D V τ) φ =
      -Rder θ V τ ((1 / 2 : ℂ) • (Z + conjAt V τ Z)) φ +
        Complex.I • Rder θ V τ ((1 / (2 * Complex.I)) • (Z - conjAt V τ Z)) φ := by
  unfold RderC
  rw [conjAt_adjoint]
  have hW : (gramAt D V τ)⁻¹ * Zᴴ * gramAt D V τ = -conjAt V τ Z := by simp [conjAt]
  rw [hW, ← Rder_neg_dir, ← smul_neg, neg_add, add_comm (-Z), neg_sub_neg]

theorem rderC_adjoint : ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) (τ : D.what₂.Tau)
    (A : Submodule ℂ (GA D V → ℂ)) (b : (GA D V → ℂ) →ₗ⋆[ℂ] (GA D V → ℂ) →ₗ[ℂ] ℂ),
    (∀ X ∈ lieAt V τ, ∀ x ∈ A, ∀ y ∈ A, b x (Rder θ V τ X y) = -b (Rder θ V τ X x) y) →
    ∀ (Z : Matrix (Fin V.rank) (Fin V.rank) ℂ), ∀ x ∈ A, ∀ y ∈ A,
      b x (RderC θ V τ Z y) = b (RderC θ V τ ((gramAt D V τ)⁻¹ * Matrix.conjTranspose Z * gramAt D V τ) x) y := by
  intro D θ V τ A b hb Z x hx y hy
  obtain ⟨h1, h2⟩ := GlobalTheory.SmoothAutCheck.parts_mem V τ Z
  rw [RderC_adjoint_eq]
  unfold RderC
  rw [map_add (f := _), map_smul, hb _ h1 x hx y hy, hb _ h2 x hx y hy, map_add (f := _), map_neg, map_smulₛₗ]
  simp

end GlobalTheory.RderCAdjoint

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContractsOfIsoDirectSum
section
noncomputable section

open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.OneFunctional Formalism.BasicNotions GlobalTheory.Branching
open scoped TensorProduct DirectSum

namespace GlobalTheory.OneFunctional

theorem contracts_of_iso_directSum (H G I F V : Type) [Monoid H] [Monoid G] [AddCommGroup F] [Module ℂ F]
    [AddCommGroup V] [Module ℂ V] (A B : I → Type) [∀ i, AddCommGroup (A i)] [∀ i, Module ℂ (A i)]
    [∀ i, AddCommGroup (B i)] [∀ i, Module ℂ (B i)] (a : ∀ i, Representation ℂ H (A i))
    (b : ∀ i, Representation ℂ G (B i)) (φ : Representation ℂ (H × G) F) (σ : Representation ℂ H V) (i₀ : I)
    (hφ : Iso (Representation.directSum fun i =>
      Representation.tprod ((a i).comp (MonoidHom.fst H G)) ((b i).comp (MonoidHom.snd H G))) φ)
    (h0 : ∀ i, i ≠ i₀ → invFun ((a i).tprod σ) = ⊥)
    (h1 : Module.finrank ℂ (invFun ((a i₀).tprod σ)) = 1) : Contracts φ σ (b i₀) := by
  classical
  refine Contracts.congr ?_ hφ (Iso.refl σ) (Iso.refl _)
  obtain ⟨⟨ε, hε⟩, hne, hspan⟩ := finrank_eq_one_iff'.1 h1
  have hε0 : ε ≠ 0 := fun h => hne (Subtype.ext h)
  have hεi : ∀ h x v, ε (a i₀ h x ⊗ₜ σ h v) = ε (x ⊗ₜ v) := fun h x v => by
    simpa using mem_invFun.1 hε h (x ⊗ₜ v)
  obtain ⟨z, hz⟩ : ∃ z, ε z = 1 := LinearMap.surjective hε0 1
  let P : (A i₀ ⊗[ℂ] B i₀) ⊗[ℂ] V →ₗ[ℂ] B i₀ :=
    (TensorProduct.lid ℂ (B i₀)).toLinearMap ∘ₗ LinearMap.rTensor (B i₀) ε ∘ₗ
      (TensorProduct.rightComm ℂ (A i₀) (B i₀) V).toLinearMap
  have hP : ∀ x y v, P ((x ⊗ₜ y) ⊗ₜ v) = ε (x ⊗ₜ v) • y := fun x y v => by simp [P]
  let J : ∀ i, B i → A i ⊗[ℂ] V →ₗ[ℂ] (⨁ i, A i ⊗[ℂ] B i) ⊗[ℂ] V := fun i y =>
    LinearMap.rTensor V (DirectSum.lof ℂ I (fun i => A i ⊗[ℂ] B i) i ∘ₗ (TensorProduct.mk ℂ (A i) (B i)).flip y)
  have hJ : ∀ i y x v, J i y (x ⊗ₜ v) = DirectSum.lof ℂ I (fun i => A i ⊗[ℂ] B i) i (x ⊗ₜ y) ⊗ₜ v :=
    fun i y x v => by simp [J]
  let π : (⨁ i, A i ⊗[ℂ] B i) ⊗[ℂ] V →ₗ[ℂ] B i₀ :=
    P ∘ₗ LinearMap.rTensor V (DirectSum.component ℂ I (fun i => A i ⊗[ℂ] B i) i₀)
  have hπ : ∀ f v, π (f ⊗ₜ v) = P (DirectSum.component ℂ I (fun i => A i ⊗[ℂ] B i) i₀ f ⊗ₜ v) :=
    fun f v => by simp [π]
  have hπJ : ∀ y w, π (J i₀ y w) = ε w • y := fun y w => by
    induction w with
    | tmul x v => rw [hJ, hπ, DirectSum.component.lof_self, hP]
    | add s t hs ht => simp only [map_add (f := _), hs, ht, add_smul]
  have hπJ' : ∀ i, i ≠ i₀ → ∀ y x v, π (J i y (x ⊗ₜ v)) = 0 := fun i hi y x v => by
    rw [hJ, hπ, DirectSum.component.of, dite_eq_right hi]; simp
  refine ⟨π, fun y => ⟨J i₀ y z, by rw [hπJ, hz, one_smul]⟩, fun h g f v => ?_, fun l hl => ?_⟩
  · rw [hπ, hπ]
    have e : DirectSum.component ℂ I (fun i => A i ⊗[ℂ] B i) i₀ ((Representation.directSum fun i =>
        Representation.tprod ((a i).comp (MonoidHom.fst H G)) ((b i).comp (MonoidHom.snd H G))) (h, g) f) =
        TensorProduct.map (a i₀ h) (b i₀ g) (DirectSum.component ℂ I (fun i => A i ⊗[ℂ] B i) i₀ f) := rfl
    rw [e]
    generalize DirectSum.component ℂ I (fun i => A i ⊗[ℂ] B i) i₀ f = t
    induction t with
    | tmul x y => rw [TensorProduct.map_tmul, hP, hP, hεi, map_smul]
    | add s t hs ht => simp only [map_add (f := _), TensorProduct.add_tmul, hs, ht]
  · have hinv : ∀ i y, l ∘ₗ J i y ∈ invFun ((a i).tprod σ) := fun i y => mem_invFun.2 fun h w => by
      induction w with
      | tmul x v =>
        have := hl h (DirectSum.lof ℂ I (fun i => A i ⊗[ℂ] B i) i (x ⊗ₜ y)) v
        simpa [hJ] using this
      | add s t hs ht => simp only [map_add (f := _), hs, ht]
    let c : B i₀ →ₗ[ℂ] ℂ := l ∘ₗ LinearMap.rTensor V (DirectSum.lof ℂ I (fun i => A i ⊗[ℂ] B i) i₀) ∘ₗ
      (TensorProduct.rightComm ℂ (A i₀) (B i₀) V).symm.toLinearMap ∘ₗ TensorProduct.mk ℂ _ _ z
    have hc : ∀ y, c y = l (J i₀ y z) := fun y => by
      simp only [c, LinearMap.comp_apply, TensorProduct.mk_apply, LinearEquiv.coe_coe]
      congr 1
      generalize z = w
      induction w with
      | tmul x v => simp [hJ]
      | add s t hs ht => simp only [map_add (f := _), TensorProduct.add_tmul, hs, ht]
    have key : ∀ i y x v, l (J i y (x ⊗ₜ v)) = c (π (J i y (x ⊗ₜ v))) := fun i y x v => by
      by_cases hi : i = i₀
      · subst hi
        obtain ⟨r, hr⟩ := hspan ⟨_, hinv i y⟩
        have hr' : ∀ w, l (J i y w) = r * ε w := fun w => by
          simpa using (congrArg (fun m : invFun ((a i).tprod σ) => m.1 w) hr).symm
        rw [hπJ, map_smul, hc, hr', hr', hz, smul_eq_mul]
        ring
      · have := hinv i y
        rw [h0 i hi, Submodule.mem_bot] at this
        rw [hπJ' i hi, map_zero]
        exact LinearMap.congr_fun this _
    have hl' : l = c ∘ₗ π := by
      refine TensorProduct.ext (DirectSum.linearMap_ext _ fun i => TensorProduct.ext' fun x y => ?_)
      ext v
      simpa [hJ] using key i y x v
    intro x hx
    rw [hl', LinearMap.comp_apply, hx, map_zero]

end GlobalTheory.OneFunctional
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContractsTensorProductChain
section
noncomputable section

open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.OneFunctional Formalism.BasicNotions GlobalTheory.Branching
open scoped TensorProduct DirectSum

namespace GlobalTheory.OneFunctional

theorem exists_piTensor_succ_equiv (m : ℕ) (F : Fin (m + 1) → Type) [∀ j, AddCommGroup (F j)] [∀ j, Module ℂ (F j)] :
    ∃ e : ((⨂[ℂ] j : Fin m, F j.succ) ⊗[ℂ] F 0) ≃ₗ[ℂ] (⨂[ℂ] j, F j),
      ∀ (f : ∀ j, F j), e (PiTensorProduct.tprod ℂ (fun j : Fin m => f j.succ) ⊗ₜ f 0) = PiTensorProduct.tprod ℂ f := by
  let σ : Fin m ⊕ Unit ≃ Fin (m + 1) :=
    { toFun := Sum.elim Fin.succ (fun _ => 0)
      invFun := fun k => Fin.cases (motive := fun _ => Fin m ⊕ Unit) (Sum.inr ()) Sum.inl k
      left_inv := by rintro (j | ⟨⟩) <;> simp
      right_inv := by intro k; cases k using Fin.cases <;> simp }
  refine ⟨(TensorProduct.congr (LinearEquiv.refl ℂ _)
      (PiTensorProduct.subsingletonEquiv (R := ℂ) (s := fun _ : Unit => F 0) ()).symm).trans
      ((PiTensorProduct.tmulEquivDep ℂ (fun i : Fin m ⊕ Unit => F (σ i))).trans
        (PiTensorProduct.reindex ℂ F σ.symm).symm), fun f => ?_⟩
  have h1 : TensorProduct.congr (LinearEquiv.refl ℂ (⨂[ℂ] j : Fin m, F j.succ))
      (PiTensorProduct.subsingletonEquiv (R := ℂ) (s := fun _ : Unit => F 0) ()).symm
      (PiTensorProduct.tprod ℂ (fun j : Fin m => f j.succ) ⊗ₜ f 0) =
      PiTensorProduct.tprod ℂ (fun j : Fin m => f j.succ) ⊗ₜ PiTensorProduct.tprod ℂ (fun _ : Unit => f 0) := by
    rw [TensorProduct.congr_tmul, LinearEquiv.refl_apply, PiTensorProduct.subsingletonEquiv_symm_apply']
  have h2 : PiTensorProduct.tmulEquivDep ℂ (fun i : Fin m ⊕ Unit => F (σ i))
      (PiTensorProduct.tprod ℂ (fun j : Fin m => f j.succ) ⊗ₜ PiTensorProduct.tprod ℂ (fun _ : Unit => f 0)) =
      PiTensorProduct.tprod ℂ (fun i => f (σ i)) := by
    rw [← LinearEquiv.eq_symm_apply, PiTensorProduct.tmulEquivDep_symm_apply]
    all_goals rfl
  have h3 : (PiTensorProduct.reindex ℂ F σ.symm).symm (PiTensorProduct.tprod ℂ (fun i => f (σ i))) =
      PiTensorProduct.tprod ℂ f := by
    rw [LinearEquiv.symm_apply_eq, PiTensorProduct.reindex_tprod]
    all_goals rfl
  show (PiTensorProduct.reindex ℂ F σ.symm).symm (PiTensorProduct.tmulEquivDep ℂ (fun i : Fin m ⊕ Unit => F (σ i))
    (TensorProduct.congr (LinearEquiv.refl ℂ (⨂[ℂ] j : Fin m, F j.succ))
      (PiTensorProduct.subsingletonEquiv (R := ℂ) (s := fun _ : Unit => F 0) ()).symm
      (PiTensorProduct.tprod ℂ (fun j : Fin m => f j.succ) ⊗ₜ f 0))) = PiTensorProduct.tprod ℂ f
  rw [h1]
  exact (congrArg (PiTensorProduct.reindex ℂ F σ.symm).symm h2).trans h3

theorem exists_piTensor_succ_equiv_map (m : ℕ) (F : Fin (m + 1) → Type) [∀ j, AddCommGroup (F j)]
    [∀ j, Module ℂ (F j)] :
    ∃ e : ((⨂[ℂ] j : Fin m, F j.succ) ⊗[ℂ] F 0) ≃ₗ[ℂ] (⨂[ℂ] j, F j),
      ∀ (A : ∀ j, F j →ₗ[ℂ] F j) (t : ⨂[ℂ] j : Fin m, F j.succ) (a : F 0),
        PiTensorProduct.map A (e (t ⊗ₜ a)) = e (PiTensorProduct.map (fun j : Fin m => A j.succ) t ⊗ₜ A 0 a) := by
  obtain ⟨e, he⟩ := exists_piTensor_succ_equiv m F
  refine ⟨e, fun A t a => ?_⟩
  induction t using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    have h1 := he (Fin.cons a f : ∀ j, F j)
    have h2 := he (fun j => A j ((Fin.cons a f : ∀ j, F j) j))
    simp only [Fin.cons_succ, Fin.cons_zero] at h1 h2
    simp only [← TensorProduct.smul_tmul', map_smul, PiTensorProduct.map_tprod, h1, h2]
  | add x y hx hy =>
    simp only [TensorProduct.add_tmul, map_add (f := _), hx, hy]

private theorem factor_dual_lemma {X Y : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    (p : X →ₗ[ℂ] Y) (hp : Function.Surjective p) (l : Module.Dual ℂ X) (hl : ∀ x, p x = 0 → l x = 0) :
    ∃ l' : Module.Dual ℂ Y, ∀ x, l x = l' (p x) := by
  obtain ⟨s, hs⟩ := p.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hp)
  refine ⟨l ∘ₗ s, fun x => ?_⟩
  have hps : p (s (p x)) = p x := by rw [← LinearMap.comp_apply p s, hs, LinearMap.id_apply]
  have h0 : p (x - s (p x)) = 0 := by rw [map_sub, hps, sub_self]
  have h1 := hl _ h0
  rw [map_sub, sub_eq_zero] at h1
  rw [LinearMap.comp_apply]
  exact h1

private theorem lTensor_ker_lemma_2 {Q N P : Type} [AddCommGroup Q] [Module ℂ Q] [AddCommGroup N] [Module ℂ N]
    [AddCommGroup P] [Module ℂ P] (g : N →ₗ[ℂ] P) (hg : Function.Surjective g)
    (l : Module.Dual ℂ (Q ⊗[ℂ] N)) (hl : ∀ q n, g n = 0 → l (q ⊗ₜ n) = 0) :
    ∀ z, LinearMap.lTensor Q g z = 0 → l z = 0 := by
  intro z hz
  obtain ⟨y, rfl⟩ := ((lTensor_exact Q (LinearMap.exact_subtype_ker_map g) hg) z).mp hz
  clear hz
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul q k =>
    rw [LinearMap.lTensor_tmul]
    exact hl q k.1 (LinearMap.mem_ker.mp k.2)
  | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb, add_zero]

theorem contracts_chain : ∀ (m : ℕ) (G : Fin (m + 1) → Type) [∀ j, Monoid (G j)] (F : Fin m → Type) [∀ j, AddCommGroup (F j)] [∀ j, Module ℂ (F j)] (V : Fin (m + 1) → Type) [∀ j, AddCommGroup (V j)] [∀ j, Module ℂ (V j)] (φ : ∀ j : Fin m, Representation ℂ (G j.castSucc × G j.succ) (F j)) (σ : ∀ j, Representation ℂ (G j) (V j)), (∀ j : Fin m, Contracts (φ j) (σ j.castSucc) (σ j.succ)) → ∃ π : ((⨂[ℂ] j, F j) ⊗[ℂ] V 0) →ₗ[ℂ] V (Fin.last m), Function.Surjective π ∧ (∀ (g : ∀ j, G j) (f : ⨂[ℂ] j, F j) (v : V 0), π (PiTensorProduct.map (fun j => φ j (g j.castSucc, g j.succ)) f ⊗ₜ[ℂ] σ 0 (g 0) v) = σ (Fin.last m) (g (Fin.last m)) (π (f ⊗ₜ[ℂ] v))) ∧ ∀ l : Module.Dual ℂ ((⨂[ℂ] j, F j) ⊗[ℂ] V 0), (∀ g : ∀ j, G j, g (Fin.last m) = 1 → ∀ (f : ⨂[ℂ] j, F j) (v : V 0), l (PiTensorProduct.map (fun j => φ j (g j.castSucc, g j.succ)) f ⊗ₜ[ℂ] σ 0 (g 0) v) = l (f ⊗ₜ[ℂ] v)) → ∀ x, π x = 0 → l x = 0 := by
  intro m
  induction m with
  | zero =>
    intro G _ F _ _ V _ _ φ σ _
    obtain ⟨ψ, hψ⟩ : ∃ ψ : ((⨂[ℂ] j : Fin 0, F j) ⊗[ℂ] V 0) ≃ₗ[ℂ] V 0,
        ∀ (f : ⨂[ℂ] j : Fin 0, F j) (v : V 0), ψ (f ⊗ₜ v) = PiTensorProduct.isEmptyEquiv (Fin 0) f • v :=
      ⟨(TensorProduct.congr (PiTensorProduct.isEmptyEquiv (Fin 0)) (LinearEquiv.refl ℂ (V 0))).trans
        (TensorProduct.lid ℂ (V 0)), fun f v => by simp⟩
    have hmap : ∀ (A : ∀ j : Fin 0, F j →ₗ[ℂ] F j) (f : ⨂[ℂ] j : Fin 0, F j),
        PiTensorProduct.isEmptyEquiv (Fin 0) (PiTensorProduct.map A f) =
          PiTensorProduct.isEmptyEquiv (Fin 0) f := by
      intro A f
      induction f using PiTensorProduct.induction_on with
      | smul_tprod r x => simp [PiTensorProduct.map_tprod]
      | add x y hx hy => simp only [map_add (f := _), hx, hy]
    refine ⟨ψ.toLinearMap, ψ.surjective, ?_, ?_⟩
    · intro g f v
      simp only [LinearEquiv.coe_coe]
      rw [hψ, hψ, hmap, map_smul]
      all_goals rfl
    · intro l _ x hx
      have hx' : ψ x = 0 := hx
      rw [ψ.map_eq_zero_iff] at hx'
      rw [hx', map_zero]
  | succ m ih =>
    intro G _ F _ _ V _ _ φ σ hc
    obtain ⟨e, he⟩ := exists_piTensor_succ_equiv_map m F
    have hc0 : Contracts (φ 0) (σ 0) (σ (Fin.succ 0)) := hc 0
    obtain ⟨π₀, hs₀, he₀, hk₀⟩ := hc0
    obtain ⟨π', hs', he', hk'⟩ := ih (fun j => G j.succ) (fun j => F j.succ) (fun j => V j.succ)
      (fun j => φ j.succ) (fun j => σ j.succ) (fun j => hc j.succ)
    obtain ⟨ψ, hψ⟩ : ∃ ψ : ((⨂[ℂ] j, F j) ⊗[ℂ] V 0) ≃ₗ[ℂ]
        ((⨂[ℂ] j : Fin m, F j.succ) ⊗[ℂ] (F 0 ⊗[ℂ] V 0)),
        ∀ t a v, ψ (e (t ⊗ₜ a) ⊗ₜ v) = t ⊗ₜ (a ⊗ₜ v) :=
      ⟨(TensorProduct.congr e.symm (LinearEquiv.refl ℂ _)).trans (TensorProduct.assoc ℂ _ _ _),
        fun t a v => by simp⟩
    refine ⟨π' ∘ₗ LinearMap.lTensor _ π₀ ∘ₗ ψ.toLinearMap,
      hs'.comp ((LinearMap.lTensor_surjective _ hs₀).comp ψ.surjective), ?_, ?_⟩
    · intro g f v
      show π' (LinearMap.lTensor _ π₀ (ψ (PiTensorProduct.map (fun j => φ j (g j.castSucc, g j.succ)) f ⊗ₜ
        σ 0 (g 0) v))) = σ (Fin.last (m + 1)) (g (Fin.last (m + 1))) (π' (LinearMap.lTensor _ π₀ (ψ (f ⊗ₜ v))))
      obtain ⟨y, rfl⟩ := e.surjective f
      induction y using TensorProduct.induction_on with
      | zero =>
        simp only [map_zero, TensorProduct.zero_tmul]
        all_goals exact (map_zero _).symm
      | tmul t a =>
        rw [he, hψ, hψ, LinearMap.lTensor_tmul, LinearMap.lTensor_tmul]
        have h0 : π₀ (φ 0 (g (Fin.castSucc 0), g (Fin.succ 0)) a ⊗ₜ σ 0 (g 0) v) =
            σ (Fin.succ 0) (g (Fin.succ 0)) (π₀ (a ⊗ₜ v)) := he₀ _ _ a v
        rw [h0]
        exact he' (fun j => g j.succ) t (π₀ (a ⊗ₜ v))
      | add y₁ y₂ h₁ h₂ =>
        simp only [map_add (f := _), TensorProduct.add_tmul] at h₁ h₂ ⊢
        rw [h₁, h₂]
    · intro l hl x hx
      obtain ⟨L, hL⟩ : ∃ L : Module.Dual ℂ ((⨂[ℂ] j : Fin m, F j.succ) ⊗[ℂ] (F 0 ⊗[ℂ] V 0)),
          ∀ z, L z = l (ψ.symm z) := ⟨l ∘ₗ ψ.symm.toLinearMap, fun z => rfl⟩
      have hLe : ∀ t a v, L (t ⊗ₜ (a ⊗ₜ v)) = l (e (t ⊗ₜ a) ⊗ₜ v) := by
        intro t a v
        rw [hL, ← hψ t a v, LinearEquiv.symm_apply_apply]

      have hA : ∀ t u, π₀ u = 0 → L (t ⊗ₜ u) = 0 := by
        intro t u hu
        refine hk₀ (L.comp (TensorProduct.mk ℂ _ _ t)) ?_ u hu
        intro h a v
        simp only [LinearMap.comp_apply, TensorProduct.mk_apply, hLe]
        obtain ⟨gs, hg0, hg0', hg1, hg2, hg3, hgl⟩ : ∃ gs : ∀ j, G j, gs (Fin.castSucc 0) = h ∧ gs 0 = h ∧
            gs (Fin.succ 0) = 1 ∧ (∀ j : Fin m, gs j.succ.castSucc = 1) ∧ (∀ j : Fin m, gs j.succ.succ = 1) ∧
            gs (Fin.last (m + 1)) = 1 :=
          ⟨Pi.mulSingle (Fin.castSucc 0) h, Pi.mulSingle_eq_same _ _, Pi.mulSingle_eq_same _ _,
            Pi.mulSingle_eq_of_ne (by simp [Fin.ext_iff]) _, fun j => Pi.mulSingle_eq_of_ne (by simp [Fin.ext_iff]) _,
            fun j => Pi.mulSingle_eq_of_ne (by simp [Fin.ext_iff]) _, Pi.mulSingle_eq_of_ne (by simp [Fin.ext_iff]) _⟩
        have hinv := hl gs hgl (e (t ⊗ₜ a)) v
        rw [← hinv, he]
        simp only [hg0, hg0', hg1, hg2, hg3, ← Prod.one_eq_mk, map_one, PiTensorProduct.map_one,
          Module.End.one_apply]
        all_goals rfl
      have hB := lTensor_ker_lemma_2 π₀ hs₀ L (fun q n hn => hA q n hn)
      obtain ⟨L', hL'⟩ := factor_dual_lemma (LinearMap.lTensor _ π₀) (LinearMap.lTensor_surjective _ hs₀) L hB

      have hD : ∀ g' : ∀ j : Fin (m + 1), G j.succ, g' (Fin.last m) = 1 → ∀ t w,
          L' (PiTensorProduct.map (fun j : Fin m => φ j.succ ((g' j.castSucc : G j.succ.castSucc), g' j.succ)) t ⊗ₜ σ (Fin.succ 0) (g' 0) w) =
            L' (t ⊗ₜ w) := by
        intro g' hg' t w
        obtain ⟨u, rfl⟩ := hs₀ w
        induction u using TensorProduct.induction_on with
        | zero => simp only [map_zero, TensorProduct.tmul_zero]
        | tmul a v =>
          rw [← he₀ 1 (g' 0) a v]
          have k1 := hL' (PiTensorProduct.map (fun j : Fin m => φ j.succ ((g' j.castSucc : G j.succ.castSucc), g' j.succ)) t ⊗ₜ
            (φ 0 (1, g' 0) a ⊗ₜ σ 0 1 v))
          have k2 := hL' (t ⊗ₜ (a ⊗ₜ v))
          rw [LinearMap.lTensor_tmul, hLe] at k1 k2
          have hinv := hl (Fin.cons (1 : G 0) g' : ∀ j, G j)
            (by rw [← Fin.succ_last, Fin.cons_succ]; exact hg') (e (t ⊗ₜ a)) v
          rw [he] at hinv
          exact k1.symm.trans (hinv.trans k2)
        | add u₁ u₂ h₁ h₂ => simp only [map_add (f := _), TensorProduct.tmul_add, h₁, h₂]
      have hx' : π' (LinearMap.lTensor _ π₀ (ψ x)) = 0 := hx
      have h1 := hk' L' hD _ hx'
      rw [← hL', hL, LinearEquiv.symm_apply_apply] at h1
      exact h1

end GlobalTheory.OneFunctional
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.OneParamUnitaryMatrixEqExpLieAlgebraStatement
section
open Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.oneParamUnitaryMatrix_eq_exp_lieAlgebra : ∀ {n : ℕ} (G : Matrix (Fin n) (Fin n) ℂ) (u : ℝ → Matrix (Fin n) (Fin n) ℂ), Continuous u → u 0 = 1 → (∀ s t, u (s + t) = u s * u t) → (∀ t, u t ∈ Formalism.QuantumDeterminants.UH G) → ∃ Y ∈ GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.lieU G, ∀ t : ℝ, u t = NormedSpace.exp (t • Y) := by
  first | exact @GlobalTheory.OneParamUnitary.oneParam_eq_exp_lieU | exact GlobalTheory.OneParamUnitary.oneParam_eq_exp_lieU | (intros; apply GlobalTheory.OneParamUnitary.oneParam_eq_exp_lieU <;> assumption)
end

