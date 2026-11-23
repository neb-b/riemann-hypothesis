module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0165
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0147
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0185
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0157
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsRestrictedProductTupleMeasureMapLeftRightActio
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwoStepMeasureOrthogonalBasisSwapLocal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0154
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicTwoStepMeasureIsRestrictedProductLocal
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0543
public import Formalism.SharpRestriction.CuspSpanNormBounds.LocalGroupInFamilyNontrivial
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BesselDatumAuxiliaryVectorOrthogonalImage
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0193
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0184
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0192
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0178
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0190
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0007
public import Formalism.LocalToGlobal.PlaceMapInjectivity.MapPlInjective
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0113
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0188

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicTwoStepMeasureOrthogonalBasesPlaneCompare
section
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeEx

theorem twoStep_isProd_of_isStdX (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (d : ℕ) (b : Module.Basis (Fin d) F E)
    (s : StdMeas b) (M : ℕ) (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (x : Fin 1 → Fin (M + 1) → E)
    (a : F) (B : Matrix (Fin (M + 1)) (Fin M) E) (J' : Matrix (Fin M) (Fin M) E)
    (y : Fin 1 → Fin M → E) (c : F) (hS : StepData σ J x a B J') (hc : c ≠ 0)
    (hy : hE σ J' (y 0) (y 0) = algebraMap F E c)
    (ν : Measure (Fin 1 → Fin (M + 1) → AF F ⊗[F] E)) (ν' : Measure (Fin 1 → Fin M → AF F ⊗[F] E))
    (N : Measure (Fin 2 → Fin (M + 1) → AF F ⊗[F] E))
    (hν : IsStdX s σ J a ν) (hν' : IsStdX s σ J' c ν') (hN : TwoStep (AF F) σ J x B ν ν' N) :
    ∃ mi mi' Ni, ∃ (mv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin 1 → Fin (M + 1) → Fv F v ⊗[F] E))
      (mv' : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin 1 → Fin M → Fv F v ⊗[F] E))
      (Nv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin 2 → Fin (M + 1) → Fv F v ⊗[F] E)),
      FibAt (Ainf F) σ J (tupMeas s.lamI 1 (M + 1)) s.nuI (algebraMap F _ a) mi ∧
      FibAt (Ainf F) σ J' (tupMeas s.lamI 1 M) s.nuI (algebraMap F _ c) mi' ∧
      TwoStep (Ainf F) σ J x B mi mi' Ni ∧
      (∀ v, FibAt (Fv F v) σ J (tupMeas (s.lamV v) 1 (M + 1)) (s.nuV v) (algebraMap F _ a) (mv v)) ∧
      (∀ v, FibAt (Fv F v) σ J' (tupMeas (s.lamV v) 1 M) (s.nuV v) (algebraMap F _ c) (mv' v)) ∧
      (∀ v, TwoStep (Fv F v) σ J x B (mv v) (mv' v) (Nv v)) ∧ IsProd b N Ni Nv := by
  obtain ⟨mi, mv, hfi, hfv, hP⟩ := hν
  obtain ⟨mi', mv', hfi', hfv', hP'⟩ := hν'
  have hJ : IsHermND σ J := hS.1
  have ha : a ≠ 0 := hS.2.1
  have hx : hE σ J (x 0) (x 0) = algebraMap F E a := hS.2.2.1
  have hJ' : IsHermND σ J' := hS.2.2.2.2.2
  obtain ⟨hNi, hNv⟩ := nice_ainf_fv F
  have oi := _root_.GlobalTheory.GaugeEx.FibProp.fibre_invariant_orbit_ne_zero F E σ hCM (Ainf F) hNi (M + 1) J x a s.lamI s.nuI mi hJ ha hx
    s.haar_lamI s.haar_nuI hfi
  have oi' := _root_.GlobalTheory.GaugeEx.FibProp.fibre_invariant_orbit_ne_zero F E σ hCM (Ainf F) hNi M J' y c s.lamI s.nuI mi' hJ' hc hy
    s.haar_lamI s.haar_nuI hfi'
  have ov := fun v => _root_.GlobalTheory.GaugeEx.FibProp.fibre_invariant_orbit_ne_zero F E σ hCM (Fv F v) (hNv v) (M + 1) J x a (s.lamV v) (s.nuV v)
    (mv v) hJ ha hx (s.haar_lamV v) (s.haar_nuV v) (hfv v)
  have ov' := fun v => _root_.GlobalTheory.GaugeEx.FibProp.fibre_invariant_orbit_ne_zero F E σ hCM (Fv F v) (hNv v) M J' y c (s.lamV v) (s.nuV v)
    (mv' v) hJ' hc hy (s.haar_lamV v) (s.haar_nuV v) (hfv' v)
  obtain ⟨Ni, hTi, -⟩ := _root_.GlobalTheory.GaugeEx.twoStep_existsUnique F E σ hCM (Ainf F) M J x a B J' mi mi' hS oi.2.1 hP.1.1
    hP'.1.1 oi'.1
  have hTv : ∀ v, ∃ N', TwoStep (Fv F v) σ J x B (mv v) (mv' v) N' := fun v =>
    (_root_.GlobalTheory.GaugeEx.twoStep_existsUnique F E σ hCM (Fv F v) M J x a B J' (mv v) (mv' v) hS (ov v).2.1 (hP.1.2.1 v)
      (hP'.1.2.1 v) (ov' v).1).exists
  choose Nv hTv using hTv
  exact ⟨mi, mi', Ni, mv, mv', Nv, hfi, hfi', hTi, hfv, hfv', hTv,
    _root_.GlobalTheory.GaugeEx.TsProd.twoStep_isProd F E σ hCM d b M J x a B J' ν mi mv ν' mi' mv' N Ni Nv hS hP hP' oi.2.1
      (fun v => (ov v).2.1) oi'.1 (fun v => (ov' v).1) hTi hTv hN⟩

private theorem prInf_inclR_eq {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    (e : E) : prInf (inclR (AF F) e) = inclR (Ainf F) e := by
  show (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)) (1 ⊗ₜ[F] e) = 1 ⊗ₜ[F] e
  first
  | rfl
  | (erw [Algebra.TensorProduct.map_tmul, map_one]; rfl)

private theorem prV_inclR_eq {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) (e : E) : prV v (inclR (AF F) e) = inclR (Fv F v) e := by
  show (Algebra.TensorProduct.map (evalV F v) (AlgHom.id F E))
      ((Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)) (1 ⊗ₜ[F] e)) = 1 ⊗ₜ[F] e
  first
  | rfl
  | (erw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, map_one, map_one]; rfl)

theorem twoStep_adelic_swap : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (s : StdMeas b), ∀ (M : ℕ) (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (x₁ : Fin 1 → Fin (M + 1) → E) (a₁ : F) (B₁ : Matrix (Fin (M + 1)) (Fin M) E) (J₁' : Matrix (Fin M) (Fin M) E) (x₂ : Fin 1 → Fin (M + 1) → E) (a₂ : F) (B₂ : Matrix (Fin (M + 1)) (Fin M) E) (J₂' : Matrix (Fin M) (Fin M) E) (y₁ y₂ : Fin 1 → Fin M → E) (b₁ b₂ : F) (γ : GL (Fin 2) E), StepData σ J x₁ a₁ B₁ J₁' → StepData σ J x₂ a₂ B₂ J₂' → b₁ ≠ 0 → b₂ ≠ 0 → hE σ J₁' (y₁ 0) (y₁ 0) = algebraMap F E b₁ → hE σ J₂' (y₂ 0) (y₂ 0) = algebraMap F E b₂ → ![x₂ 0, B₂.mulVec (y₂ 0)] = lrAct 1 (γ : Matrix (Fin 2) (Fin 2) E) ![x₁ 0, B₁.mulVec (y₁ 0)] → ∀ (ν₁ ν₂ : Measure (Fin 1 → Fin (M + 1) → AF F ⊗[F] E)) (ν₁' ν₂' : Measure (Fin 1 → Fin M → AF F ⊗[F] E)) (N₁ N₂ : Measure (Fin 2 → Fin (M + 1) → AF F ⊗[F] E)), IsStdX s σ J a₁ ν₁ → IsStdX s σ J₁' b₁ ν₁' → IsStdX s σ J a₂ ν₂ → IsStdX s σ J₂' b₂ ν₂' → TwoStep (AF F) σ J x₁ B₁ ν₁ ν₁' N₁ → TwoStep (AF F) σ J x₂ B₂ ν₂ ν₂' N₂ → N₂ = N₁.map (lrAct 1 ((γ : Matrix (Fin 2) (Fin 2) E).map (inclR (AF F)))) := by
  intro F E _ _ _ _ _ σ hCM d b s M J x₁ a₁ B₁ J₁' x₂ a₂ B₂ J₂' y₁ y₂ b₁ b₂ γ hS₁ hS₂ hb₁ hb₂ hy₁
    hy₂ hγ ν₁ ν₂ ν₁' ν₂' N₁ N₂ hν₁ hν₁' hν₂ hν₂' hN₁ hN₂
  obtain ⟨u, hu, hloc⟩ := _root_.GlobalTheory.GaugeEx.SwapLoc.twoStep_swap_local F E σ hCM M J x₁ a₁ B₁ J₁' x₂ a₂ B₂ J₂' y₁ y₂ b₁ b₂ γ
    hS₁ hS₂ hb₁ hb₂ hy₁ hy₂ hγ
  obtain ⟨mi₁, mi₁', Ni₁, mv₁, mv₁', Nv₁, hfi₁, hfi₁', hTi₁, hfv₁, hfv₁', hTv₁, hP₁⟩ :=
    twoStep_isProd_of_isStdX F E σ hCM d b s M J x₁ a₁ B₁ J₁' y₁ b₁ hS₁ hb₁ hy₁ ν₁ ν₁' N₁
      hν₁ hν₁' hN₁
  obtain ⟨mi₂, mi₂', Ni₂, mv₂, mv₂', Nv₂, hfi₂, hfi₂', hTi₂, hfv₂, hfv₂', hTv₂, hP₂⟩ :=
    twoStep_isProd_of_isStdX F E σ hCM d b s M J x₂ a₂ B₂ J₂' y₂ b₂ hS₂ hb₂ hy₂ ν₂ ν₂' N₂
      hν₂ hν₂' hN₂
  obtain ⟨hNi, hNv⟩ := nice_ainf_fv F

  have ei := hloc (Ainf F) hNi s.lamI s.nuI mi₁ mi₂ mi₁' mi₂' Ni₁ Ni₂ s.haar_lamI s.haar_nuI
    hfi₁ hfi₁' hfi₂ hfi₂' hTi₁ hTi₂
  have ev := fun v => hloc (Fv F v) (hNv v) (s.lamV v) (s.nuV v) (mv₁ v) (mv₂ v) (mv₁' v)
    (mv₂' v) (Nv₁ v) (Nv₂ v) (s.haar_lamV v) (s.haar_nuV v) (hfv₁ v) (hfv₁' v) (hfv₂ v)
    (hfv₂' v) (hTv₁ v) (hTv₂ v)

  have hmap := _root_.GlobalTheory.GaugeEx.ProdTransport.isProd_map_lrAct F E d b 2 (M + 1) N₁ Ni₁ Nv₁ 1
    (Matrix.GeneralLinearGroup.map (inclR (AF F)) γ) hP₁
  have hγA : ((Matrix.GeneralLinearGroup.map (inclR (AF F)) γ : GL (Fin 2) (AF F ⊗[F] E)) :
      Matrix (Fin 2) (Fin 2) (AF F ⊗[F] E)) = (γ : Matrix (Fin 2) (Fin 2) E).map (inclR (AF F)) :=
    rfl
  have hγi : ((γ : Matrix (Fin 2) (Fin 2) E).map (inclR (AF F))).map prInf =
      (γ : Matrix (Fin 2) (Fin 2) E).map (inclR (Ainf F)) := by
    ext i j; exact prInf_inclR_eq _
  have hγv : ∀ v, ((γ : Matrix (Fin 2) (Fin 2) E).map (inclR (AF F))).map (prV v) =
      (γ : Matrix (Fin 2) (Fin 2) E).map (inclR (Fv F v)) := by
    intro v; ext i j; exact prV_inclR_eq v _
  have h1i : (1 : Matrix (Fin (M + 1)) (Fin (M + 1)) (AF F ⊗[F] E)).map prInf = 1 :=
    Matrix.map_one _ (map_zero _) (map_one _)
  have h1v : ∀ v, (1 : Matrix (Fin (M + 1)) (Fin (M + 1)) (AF F ⊗[F] E)).map (prV v) = 1 :=
    fun v => Matrix.map_one _ (map_zero _) (map_one _)
  rw [hγA] at hmap
  simp only [Units.val_one, h1i, h1v, hγi, hγv] at hmap

  obtain ⟨hfin, hprod⟩ := _root_.GlobalTheory.GaugeEx.prod_modu_inclR F E σ hCM u hu
  have hsc := GlobalTheory.T.restrictedProduct_measure_smul_factors_eq_smul F E d b 2 (M + 1) _ _ _ (modu (Ainf F ⊗[F] E) (inclR (Ainf F) u))
    (fun v => modu (Fv F v ⊗[F] E) (inclR (Fv F v) u)) hmap hfin
  simp only [hprod, one_smul] at hsc
  have hv : Nv₂ = fun v => modu (Fv F v ⊗[F] E) (inclR (Fv F v) u) •
      (Nv₁ v).map (lrAct 1 ((γ : Matrix (Fin 2) (Fin 2) E).map (inclR (Fv F v)))) := funext ev
  rw [← ei, ← hv] at hsc
  exact ((_root_.GlobalTheory.GaugeEx.isProd_basic F E d b 2 (M + 1) N₂ Ni₂ Nv₂ hP₂).2.2.1 _ hsc).symm

end GlobalTheory.GaugeEx
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgebraMapTraceEq
section
noncomputable section

open NumberField Matrix GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.IntPair GlobalTheory.IntTerm Formalism.BasicNotions
open Formalism.MainNotions.S (FlagG LieU perpS)

namespace GlobalTheory.RelFlag

section Space

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' : E}

theorem hT_eq_form (x y : S.V) : S.hT y x = form (starRingEnd E) S.gram (co S x) (co S y) := by
  rw [hT_eq_sum, form, Matrix.dotProduct_mulVec]; rfl

variable (F : FlagG S r T)

variable {F}

end Space

attribute [local instance] Formalism.BasicNotions.Host.cmStar

end GlobalTheory.RelFlag
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AnnihilatorSubsetCompact
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.BesselData GlobalTheory.RootExch
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PosLinVec

theorem hA_single {D : D7} (A : HSp D) (x : Fin A.rank → AE D) (i : Fin A.rank) (s : AE D) :
    hA A x (Pi.single i (cA D s)) = (A.gram.map (incA D)).mulVec x i * s := by
  rw [hA_eq, show (fun j => cA D ((Pi.single i (cA D s) : Fin A.rank → AE D) j)) = Pi.single i s from
    funext fun j => by by_cases e : j = i <;> simp [e, GlobalTheory.RootExch.cA_cA], single_dotProduct, mul_comm]

theorem vec_of_scalar {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] {n : ℕ}
    (c : R →+* R) (hc : Continuous c) (ε u w : R) (huw : w * u = 1) (J : Matrix (Fin n) (Fin n) R) (hJ : IsUnit J)
    (h : (Fin n → R) → (Fin n → R) → R) (hh : ∀ x i s, h x (Pi.single i (c s)) = J.mulVec x i * s)
    (P : R → Prop)
    (H : ∀ V ∈ nhds (0 : R), ∃ C : Set R, IsCompact C ∧ ∀ a, ε * a = a → (∀ s ∈ V, ε * s = s → P (a * s)) → a ∈ C) :
    ∀ V ∈ nhds (0 : Fin n → R), ∃ C : Set (Fin n → R), IsCompact C ∧ ∀ t₀, ε • t₀ = t₀ →
      (∀ t ∈ V, c ε • t = t → P (u * h t₀ t)) → t₀ ∈ C := by
  intro V hV
  have hc' : ∀ i : Fin n, Continuous fun s : R => (Pi.single i (c s) : Fin n → R) := fun i =>
    (continuous_single (A := fun _ : Fin n => R) i).comp hc
  have hVi : ∀ i : Fin n, (fun s : R => (Pi.single i (c s) : Fin n → R)) ⁻¹' V ∈ nhds (0 : R) := fun i =>
    (hc' i).continuousAt.preimage_mem_nhds (by simpa only [map_zero, Pi.single_zero] using hV)
  choose C hC hmem using fun i => H _ (hVi i)
  obtain ⟨K, hK⟩ := hJ.exists_left_inv
  let g : (Fin n → R) → (Fin n → R) := fun a => w • K.mulVec a
  have hg0 : Continuous fun a : Fin n → R => K.mulVec a := continuous_const.matrix_mulVec continuous_id
  have hg : Continuous g := continuous_pi fun i => continuous_const.mul ((continuous_apply i).comp hg0)
  refine ⟨g '' Set.pi Set.univ C, (isCompact_univ_pi hC).image hg, fun t₀ ht h' => ?_⟩
  refine ⟨u • J.mulVec t₀, fun i _ => hmem i _ ?_ fun s hs hεs => ?_, ?_⟩
  · conv_rhs => rw [← ht]
    simp only [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
    ring
  · have := h' _ hs (by rw [← Pi.single_smul, smul_eq_mul, ← map_mul, hεs])
    rw [hh] at this
    rw [Pi.smul_apply, smul_eq_mul, mul_assoc]
    exact this
  · simp only [g]
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, hK, Matrix.one_mulVec, smul_smul, huw, one_smul]

theorem annihilator_subset_compact : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ ε : AE D, IsSplitIdem D ε → ∀ (A : HSp D) (θ : D.host.E), θ ≠ 0 → ∀ V ∈ nhds (0 : Fin A.rank → AE D), ∃ C : Set (Fin A.rank → AE D), IsCompact C ∧ ∀ t₀, ε • t₀ = t₀ → (∀ t ∈ V, cA D ε • t = t → ψ (Algebra.trace (AF D.host.F) (AE D) (incA D θ * hA A t₀ t)) = 1) → t₀ ∈ C := by
  intro D ψ hψ ε hε A θ hθ
  have : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)
  exact vec_of_scalar (cA D) GlobalTheory.FockCompare.ThetaCont.continuous_conj ε (incA D θ) (incA D θ⁻¹)
    (by rw [← RingHom.map_mul, inv_mul_cancel₀ hθ, RingHom.map_one]) (A.gram.map (incA D))
    ((GlobalTheory.BesselCompare.gram_isUnit A).map (incA D).mapMatrix) (hA A) (hA_single A)
    (fun a => ψ (Algebra.trace (AF D.host.F) (AE D) a) = 1)
    (_root_.GlobalTheory.SplitAnnihilator.annihilator_subset_compact D ψ (_root_.GlobalTheory.StdCharLocal.psiV_ne_one D ψ hψ) ε hε)

end GlobalTheory.PosLinVec
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CardKilledByInType
section
open NumberField IsDedekindDomain Matrix Formalism.L2.Col GlobalTheory.InertNbr
open Formalism.L2.DIV (Pl kP St resS oToS idS cmpS)
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.InertDivUniq

def minSum (s : List ℕ) (k : ℕ) : ℕ := (s.map (fun a => min a k)).sum

theorem minSum_succ (s : List ℕ) (k : ℕ) :
    minSum s (k + 1) = minSum s k + s.countP (fun a => k < a) := by
  induction s with
  | nil => simp [minSum]
  | cons a s ih =>
    simp only [minSum, List.map_cons, List.sum_cons, List.countP_cons] at ih ⊢
    rw [ih]
    by_cases h : k < a
    · simp [h]; omega
    · simp [h]; omega

theorem countP_lt_eq (s : List ℕ) (k : ℕ) :
    s.countP (fun a => k < a) = s.count (k + 1) + s.countP (fun a => k + 1 < a) := by
  induction s with
  | nil => simp
  | cons a s ih =>
    simp only [List.countP_cons, List.count_cons]
    rw [ih]
    by_cases h1 : k < a <;> by_cases h2 : a = k + 1 <;> by_cases h3 : k + 1 < a <;> simp [h1, h2, h3] <;> omega

theorem eq_of_minSum {s t : List ℕ} (hs : s.Pairwise (· ≥ ·)) (hs0 : ∀ a ∈ s, 0 < a)
    (ht : t.Pairwise (· ≥ ·)) (ht0 : ∀ a ∈ t, 0 < a) (h : ∀ k, minSum s k = minSum t k) : s = t := by
  have hc : ∀ k, s.countP (fun a => k < a) = t.countP (fun a => k < a) := fun k => by
    have := minSum_succ s k; have := minSum_succ t k; have := h k; have := h (k + 1); omega
  have hcount : ∀ a, s.count a = t.count a := by
    intro a
    rcases a with _ | a
    · rw [List.count_eq_zero.2 (fun h0 => lt_irrefl 0 (hs0 0 h0)),
        List.count_eq_zero.2 (fun h0 => lt_irrefl 0 (ht0 0 h0))]
    · have := countP_lt_eq s a; have := countP_lt_eq t a; have := hc a; have := hc (a + 1); omega
  exact List.Perm.eq_of_pairwise' hs ht (List.perm_iff_count.2 hcount)

theorem sum_map_eq (s : List ℕ) (f : ℕ → ℕ) : (s.map f).sum = ∑ i : Fin s.length, f (s.get i) := by
  induction s with
  | nil => simp
  | cons a s ih =>
    rw [List.map_cons, List.sum_cons, ih]
    exact (Fin.sum_univ_succ (n := s.length) (fun i => f ((a :: s).get i))).symm

variable {E : Type} [Field E] [NumberField E]

def killedBy {M : Type} [AddCommGroup M] [Module (𝓞 E) M] (I : Ideal (𝓞 E)) : Set M := {x | ∀ r ∈ I, r • x = 0}

theorem card_killedBy_congr {M N : Type} [AddCommGroup M] [Module (𝓞 E) M] [AddCommGroup N] [Module (𝓞 E) N]
    (e : M ≃ₗ[𝓞 E] N) (I : Ideal (𝓞 E)) :
    Nat.card (killedBy I : Set M) = Nat.card (killedBy I : Set N) :=
  Nat.card_congr (e.toEquiv.subtypeEquiv fun x => by
    simp only [killedBy, Set.mem_setOf_eq]
    refine forall₂_congr fun r _ => ?_
    rw [LinearEquiv.coe_toEquiv, ← map_smul, LinearEquiv.map_eq_zero_iff])

theorem card_killedBy_inType (Q : Ideal (𝓞 E)) (s : List ℕ) (I : Ideal (𝓞 E)) :
    Nat.card (killedBy I : Set (Formalism.L2.Col.inType Q s)) =
      ∏ i : Fin s.length, Nat.card (killedBy I : Set (𝓞 E ⧸ Q ^ s.get i)) := by
  rw [← Nat.card_pi]
  refine Nat.card_congr ((Equiv.subtypeEquivRight fun x => ?_).trans Equiv.subtypePiEquivPi)
  simp only [killedBy, Set.mem_setOf_eq]
  constructor
  · intro h i r hr; exact congrFun (h r hr) i
  · intro h r hr; funext i; exact h i r hr

theorem card_quot_pow (Q : Ideal (𝓞 E)) (n : ℕ) : Nat.card (𝓞 E ⧸ Q ^ n) = Ideal.absNorm Q ^ n := by
  rw [← map_pow, Ideal.absNorm_apply, Submodule.cardQuot_apply]

theorem mem_killedBy_iff (Q : Ideal (𝓞 E)) (hQ0 : Q ≠ ⊥) (a k : ℕ) (x : 𝓞 E) :
    (∀ r ∈ Q ^ k, r * x ∈ Q ^ a) ↔ x ∈ Q ^ (a - k) := by
  constructor
  · intro H
    rcases le_or_gt a k with hak | hak
    · rw [Nat.sub_eq_zero_of_le hak, pow_zero, Ideal.one_eq_top]; trivial
    · have hle : Q ^ k * Ideal.span {x} ≤ Q ^ a := Ideal.mul_le.2 fun r hr y hy => by
        obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hy
        rw [mul_left_comm]; exact Ideal.mul_mem_left _ c (H r hr)
      have hd := Ideal.dvd_iff_le.2 hle
      rw [show Q ^ a = Q ^ k * Q ^ (a - k) by rw [← pow_add]; congr 1; omega] at hd
      have hQ : Q ≠ 0 := by rwa [Ne, Ideal.zero_eq_bot]
      have := Ideal.dvd_iff_le.1 ((mul_dvd_mul_iff_left (pow_ne_zero k hQ)).1 hd)
      exact (Ideal.span_singleton_le_iff_mem _).1 this
  · intro hx r hr
    have := Ideal.mul_mem_mul hr hx
    rw [← pow_add] at this
    exact Ideal.pow_le_pow_right (by omega) this

theorem card_killedBy_quot (Q : Ideal (𝓞 E)) (hQ0 : Q ≠ ⊥) (a k : ℕ) :
    Nat.card (killedBy (Q ^ k) : Set (𝓞 E ⧸ Q ^ a)) = Ideal.absNorm Q ^ min a k := by
  have hle : Q ^ a ≤ Q ^ (a - k) := Ideal.pow_le_pow_right (Nat.sub_le a k)
  have hset : (killedBy (Q ^ k) : Set (𝓞 E ⧸ Q ^ a)) =
      (((Q ^ (a - k)).map (Ideal.Quotient.mk (Q ^ a)) : Ideal (𝓞 E ⧸ Q ^ a)) : Set (𝓞 E ⧸ Q ^ a)) := by
    ext y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    simp only [killedBy, Set.mem_setOf_eq, SetLike.mem_coe, Ideal.mem_quotient_iff_mem hle]
    rw [← mem_killedBy_iff Q hQ0 a k x]
    refine forall₂_congr fun r _ => ?_
    rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
  rw [hset]
  have h1 := Submodule.card_eq_card_quotient_mul_card ((Q ^ (a - k)).map (Ideal.Quotient.mk (Q ^ a)))
  rw [Nat.card_congr (DoubleQuot.quotQuotEquivQuotOfLE hle).toEquiv, card_quot_pow, card_quot_pow] at h1
  have hq : 0 < Ideal.absNorm Q := Nat.pos_of_ne_zero (fun h0 => hQ0 (Ideal.absNorm_eq_zero_iff.1 h0))
  have ha : Ideal.absNorm Q ^ a = Ideal.absNorm Q ^ min a k * Ideal.absNorm Q ^ (a - k) := by
    rw [← pow_add]; congr 1; omega
  rw [ha] at h1
  exact (Nat.eq_of_mul_eq_mul_right (pow_pos hq _) h1).symm

theorem inType_exps_unique : ∀ {E : Type} [Field E] [NumberField E] (Q : HeightOneSpectrum (𝓞 E)) (s t : List ℕ),
    s.Pairwise (· ≥ ·) → (∀ a ∈ s, 0 < a) → t.Pairwise (· ≥ ·) → (∀ a ∈ t, 0 < a) →
    Nonempty (inType Q.asIdeal s ≃ₗ[𝓞 E] inType Q.asIdeal t) → s = t := by
  intro E _ _ Q s t hs hs0 ht ht0 ⟨e⟩
  refine eq_of_minSum hs hs0 ht ht0 fun k => ?_
  have hq : 2 ≤ Ideal.absNorm Q.asIdeal := by
    have h0 : Ideal.absNorm Q.asIdeal ≠ 0 := fun h0 => Q.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
    have h1 : Ideal.absNorm Q.asIdeal ≠ 1 := fun h1 => Q.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h1)
    omega
  have key : ∀ u : List ℕ, Nat.card (killedBy (Q.asIdeal ^ k) : Set (inType Q.asIdeal u)) =
      Ideal.absNorm Q.asIdeal ^ minSum u k := fun u => by
    rw [card_killedBy_inType, minSum, sum_map_eq, ← Finset.prod_pow_eq_pow_sum]
    exact Finset.prod_congr rfl fun i _ => card_killedBy_quot Q.asIdeal Q.ne_bot _ k
  have := card_killedBy_congr e (Q.asIdeal ^ k)
  rw [key, key] at this
  exact Nat.pow_right_injective hq this

end GlobalTheory.InertDivUniq
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColLieOperatorEqSumColUnitaryActionBddDegree
section
noncomputable section

open Matrix

namespace GlobalTheory.DefLift.ColComb

variable {ι : Type} {m n : ℕ}

def sw (ι : Type) (m n : ℕ) : ι × Fin m × Fin n → ι × Fin n × Fin m := fun v => (v.1, v.2.2, v.2.1)

theorem sw_sw (v : ι × Fin m × Fin n) : sw ι n m (sw ι m n v) = v := rfl

theorem sw_injective : Function.Injective (sw ι m n) := Function.LeftInverse.injective sw_sw

theorem rename_subst (a : ι → Matrix (Fin m) (Fin m) ℂ) (b : ι → Matrix (Fin n) (Fin n) ℂ) (Q : Pol ι n m) :
    MvPolynomial.rename (sw ι n m) (subst a b Q) =
      subst (fun ρ => (b ρ)ᵀ) (fun ρ => (a ρ)ᵀ) (MvPolynomial.rename (sw ι n m) Q) := by
  have : (MvPolynomial.rename (sw ι n m)).comp (subst a b) =
      (subst (fun ρ => (b ρ)ᵀ) (fun ρ => (a ρ)ᵀ)).comp (MvPolynomial.rename (sw ι n m)) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨ρ, c, i⟩
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [subst, AlgHom.comp_apply, MvPolynomial.aeval_X, MvPolynomial.rename_X, map_sum, map_smul, sw,
      Matrix.transpose_apply]
    rw [Finset.sum_comm]
    simp only [mul_comm]
  exact AlgHom.congr_fun this Q

def cj (u : Matrix.unitaryGroup (Fin n) ℂ) : Matrix.unitaryGroup (Fin n) ℂ :=
  ⟨star (u : Matrix (Fin n) (Fin n) ℂ)ᵀ, by
    rw [Matrix.mem_unitaryGroup_iff', star_star]
    have h : star (u : Matrix (Fin n) (Fin n) ℂ) * u = 1 := Matrix.mem_unitaryGroup_iff'.1 u.2
    have e : star (u : Matrix (Fin n) (Fin n) ℂ)ᵀ = (star (u : Matrix (Fin n) (Fin n) ℂ))ᵀ := rfl
    rw [e, ← Matrix.transpose_mul, h, Matrix.transpose_one]⟩

theorem cj_cj (u : Matrix.unitaryGroup (Fin n) ℂ) : cj (cj u) = u := by
  apply Subtype.ext
  ext i j
  simp [cj]

theorem rename_rowSub (τ : ι) (u : Matrix.unitaryGroup (Fin n) ℂ) (Q : Pol ι n m) :
    MvPolynomial.rename (sw ι n m) (rowSub m τ u Q) = colSub m τ (cj u) (MvPolynomial.rename (sw ι n m) Q) := by
  simp only [rowSub, colSub, AlgHom.toLinearMap_apply, rename_subst]
  congr 2
  · funext ρ
    split_ifs <;> simp [cj]
  · funext ρ
    simp

theorem rename_rowLie (τ : ι) (k l : Fin n) (Q : Pol ι n m) :
    MvPolynomial.rename (sw ι n m) (rowLie m τ k l Q) = colLie m τ k l (MvPolynomial.rename (sw ι n m) Q) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [rowLie_apply, colLie_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, MvPolynomial.rename_X, ← MvPolynomial.pderiv_rename sw_injective]
  rfl

end GlobalTheory.DefLift.ColComb

namespace GlobalTheory.DefLift


open ColComb in
theorem colLie_eq_sum_colSub : ∀ (ι : Type) [Fintype ι] (m n d : ℕ) (τ : ι) (k l : Fin n),
    ∃ (s : Finset (Matrix.unitaryGroup (Fin n) ℂ)) (c : Matrix.unitaryGroup (Fin n) ℂ → ℂ),
      ∀ P : Pol ι m n, P.totalDegree ≤ d → ∑ g ∈ s, c g • colSub m τ g P = colLie m τ k l P := by
  intro ι _ m n d τ k l
  obtain ⟨s, c, h⟩ := _root_.GlobalTheory.DefLift.exists_sum_rowSub_eq_rowLie ι n m d τ k l
  refine ⟨s.map ⟨cj, Function.LeftInverse.injective cj_cj⟩, fun g => c (cj g), fun P hP => ?_⟩
  have e : MvPolynomial.rename (sw ι n m) (MvPolynomial.rename (sw ι m n) P) = P := by
    rw [MvPolynomial.rename_rename]
    exact MvPolynomial.rename_id_apply P
  have h1 := congrArg (MvPolynomial.rename (sw ι n m))
    (h (MvPolynomial.rename (sw ι m n) P) ((MvPolynomial.totalDegree_rename_le _ _).trans hP))
  set_option synthInstance.maxHeartbeats 100000 in
    rw [rename_rowLie, map_sum, e] at h1
  rw [← h1, Finset.sum_map]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [map_smul, rename_rowSub, e]
  simp [cj_cj]

end GlobalTheory.DefLift

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyMemFixed
section
open NumberField IsDedekindDomain

namespace GlobalTheory.CuspRep.AeFix

theorem eventually_mem_fixed : ∀ (E : Type) [Field E] [NumberField E] [NumberField.IsTotallyComplex E] (a : ℕ) (π : GlobalTheory.CuspRep.CuspSub E a) (x : π.V), ∀ᶠ v in Filter.cofinite, x ∈ GlobalTheory.PRep.fixed (π.locRep v) (GlobalTheory.LFun.KGL v (n := a)) := by
  intro E _ _ _ a π x
  filter_upwards [GlobalTheory.CuspRep.LocSph.eventually_mem ((π.cusp x.1 x.2).1.level.mem_nhds (by simp))] with w hw
  refine GlobalTheory.LGrp.mem_fixed.2 fun k hk => Subtype.ext ?_
  obtain ⟨g, rfl⟩ := hk
  exact hw g

end GlobalTheory.CuspRep.AeFix
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsColStableDisjointStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory GlobalTheory.DefLift GlobalTheory.Chain
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_colStable_complement_of_lt : ∀ (ι : Type) [Fintype ι] (m n : ℕ) (X : Type) [AddCommGroup X] [Module ℂ X] [FiniteDimensional ℂ X] (U W : Submodule ℂ (X →ₗ[ℂ] Pol ι m n)), (∀ Φ ∈ U, ∀ τ g, colSub m τ g ∘ₗ Φ ∈ U) → (∀ Φ ∈ W, ∀ τ g, colSub m τ g ∘ₗ Φ ∈ W) → U < W → ∃ U' : Submodule ℂ (X →ₗ[ℂ] Pol ι m n), U' ≠ ⊥ ∧ U' ≤ W ∧ U ⊓ U' = ⊥ ∧ ∀ Φ ∈ U', ∀ τ g, colSub m τ g ∘ₗ Φ ∈ U' := by
  first | exact @GlobalTheory.DefLift.exists_colStable_disjoint | exact GlobalTheory.DefLift.exists_colStable_disjoint | (intros; apply GlobalTheory.DefLift.exists_colStable_disjoint <;> assumption)
end

