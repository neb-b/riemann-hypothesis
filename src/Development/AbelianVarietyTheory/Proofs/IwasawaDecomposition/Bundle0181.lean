module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0151
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0171
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
public import Formalism.LocalRingCardinality.Bundle0007
public import Formalism.LocalRingCardinality.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsBesPosOfBesselTied
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0160
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsotropicUnipotentRadicalsRationalCocompact
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0162
public import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRealIntertwinerOfCompactGroupIntertwiner
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.Chain GlobalTheory.CompactHowe Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompactIntertwiner

theorem hasDerivAt_dual_of_sep {F Z : Type*} [AddCommGroup F] [Module ℂ F] [FiniteDimensional ℂ F]
    (l : Z → F →ₗ[ℂ] ℂ) (hl : ∀ x, (∀ z, l z x = 0) → x = 0) (c : ℝ → F) (y : F)
    (h : ∀ z, HasDerivAt (fun t => l z (c t)) (l z y) 0) (f : F →ₗ[ℂ] ℂ) :
    HasDerivAt (fun t => f (c t)) (f y) 0 := by
  have hsp : Submodule.span ℂ (Set.range l) = ⊤ := by
    have h1 : (Submodule.span ℂ (Set.range l)).dualCoannihilator = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      rw [Submodule.mem_dualCoannihilator] at hx
      exact hl x fun z => hx _ (Submodule.subset_span ⟨z, rfl⟩)
    have h2 := Subspace.dualCoannihilator_dualAnnihilator_eq (W := Submodule.span ℂ (Set.range l))
    rw [h1, Submodule.dualAnnihilator_bot] at h2
    exact h2.symm
  have hf : f ∈ Submodule.span ℂ (Set.range l) := hsp ▸ Submodule.mem_top
  induction hf using Submodule.span_induction with
  | mem g hg => obtain ⟨z, rfl⟩ := hg; exact h z
  | zero => simpa using hasDerivAt_const (0 : ℝ) (0 : ℂ)
  | add g g' _ _ hg hg' => exact hg.fun_add hg'
  | smul a g _ hg => simpa using hg.const_mul a

theorem hasDerivAt_dual_of_sep_sub {E Z : Type*} [AddCommGroup E] [Module ℂ E] (F : Submodule ℂ E)
    [FiniteDimensional ℂ F] (l : Z → E →ₗ[ℂ] ℂ) (hl : ∀ x, (∀ z, l z x = 0) → x = 0) (c : ℝ → E) (y : E)
    (hc : ∀ t, c t ∈ F) (hy : y ∈ F)
    (h : ∀ z, HasDerivAt (fun t => l z (c t)) (l z y) 0) (f : E →ₗ[ℂ] ℂ) :
    HasDerivAt (fun t => f (c t)) (f y) 0 :=
  hasDerivAt_dual_of_sep (F := F) (fun z => l z ∘ₗ F.subtype) (fun x hx => Subtype.ext (hl x hx))
    (fun t => ⟨c t, hc t⟩) ⟨y, hy⟩ h (f ∘ₗ F.subtype)

theorem hasDerivAt_bilin {E G : Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup G] [Module ℂ G]
    [FiniteDimensional ℂ G] (B : E →ₗ[ℂ] G →ₗ[ℂ] ℂ) (c : ℝ → E) (c' : E) (x : ℝ → G) (x' : G)
    (hc : ∀ f : E →ₗ[ℂ] ℂ, HasDerivAt (fun t => f (c t)) (f c') 0)
    (hx : ∀ f : G →ₗ[ℂ] ℂ, HasDerivAt (fun t => f (x t)) (f x') 0) :
    HasDerivAt (fun t => B (c t) (x t)) (B c' (x 0) + B (c 0) x') 0 := by
  let b := Module.finBasis ℂ G
  have e : ∀ a u, B a u = ∑ i, B.flip (b i) a * b.coord i u := by
    intro a u
    set_option synthInstance.maxHeartbeats 100000 in
      conv_lhs => rw [← b.sum_repr u, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, smul_eq_mul, mul_comm]
    rfl
  have := HasDerivAt.fun_sum (u := Finset.univ) fun i _ => (hc (B.flip (b i))).mul (hx (b.coord i))
  simp only [e]
  rw [← Finset.sum_add_distrib]
  exact this

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

theorem ellT_tprod (M : DSModel V S) (w v : ∀ τ, M.H τ) :
    ellT M w (PiTensorProduct.tprod ℂ v) = ∏ τ, inner ℂ (w τ) (v τ) := by
  simp [ellT]

theorem finite_tensor (M : DSModel V S) (h : ∀ τ, FiniteDimensional ℂ (M.H τ)) :
    FiniteDimensional ℂ (⨂[ℂ] τ, M.H τ) := by
  classical
  exact Module.Finite.of_basis (Basis.piTensorProduct fun τ => Module.finBasis ℂ (M.H τ))

theorem ellT_sep (M : DSModel V S) (h : ∀ τ, FiniteDimensional ℂ (M.H τ)) (x : ⨂[ℂ] τ, M.H τ)
    (hx : ∀ w, ellT M w x = 0) : x = 0 := by
  classical
  let o := fun τ => stdOrthonormalBasis ℂ (M.H τ)
  let b := Basis.piTensorProduct fun τ => (o τ).toBasis
  have key : ∀ i, b.coord i = ellT M fun τ => o τ (i τ) := by
    intro i
    refine PiTensorProduct.ext (MultilinearMap.ext fun v => ?_)
    simp only [LinearMap.compMultilinearMap_apply, ellT_tprod, Module.Basis.coord_apply, b]
    rw [Basis.piTensorProduct_repr_tprod_apply]
    refine Finset.prod_congr rfl fun τ _ => ?_
    simp [OrthonormalBasis.repr_apply_apply]
  refine b.ext_elem fun i => ?_
  have := hx fun τ => o τ (i τ)
  rw [← key] at this
  simpa using this

theorem inclT_bij (M : DSModel V S) (h : ∀ τ, M.sm τ = ⊤) : Function.Bijective (inclT M) := by
  have : inclT M = (PiTensorProduct.congr fun τ => LinearEquiv.ofTop (M.sm τ) (h τ)).toLinearMap := by
    refine PiTensorProduct.ext (MultilinearMap.ext fun v => ?_)
    simp [inclT]
  rw [this]
  exact LinearEquiv.bijective _

theorem isUnit_gram (M : DSModel V S) (τ : D.what₂.Tau) : IsUnit (gramAt D V τ) := by
  rw [← M.fr_gram τ]
  refine ((M.fr_unit τ).star.mul ?_).mul (M.fr_unit τ)
  refine IsUnit.of_mul_eq_one (Formalism.REAL.Jm (M.ε τ)) ?_
  unfold Formalism.REAL.Jm
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  split_ifs <;> simp

theorem continuous_tprod (M : DSModel V S) (h : ∀ τ, FiniteDimensional ℂ (M.H τ)) (f : (⨂[ℂ] τ, M.H τ) →ₗ[ℂ] ℂ) :
    Continuous fun v : ∀ τ, M.H τ => f (PiTensorProduct.tprod ℂ v) := by
  classical
  let o := fun τ => Module.finBasis ℂ (M.H τ)
  let b := Basis.piTensorProduct o
  have e : ∀ v : ∀ τ, M.H τ, f (PiTensorProduct.tprod ℂ v) = ∑ i, (∏ τ, (o τ).coord (i τ) (v τ)) * f (b i) := by
    intro v
    set_option synthInstance.maxHeartbeats 100000 in
      conv_lhs => rw [← b.sum_repr (PiTensorProduct.tprod ℂ v), map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, smul_eq_mul, Basis.piTensorProduct_repr_tprod_apply]
    rfl
  simp only [e]
  exact continuous_finsetSum _ fun i _ => (continuous_finsetProd _ fun τ _ =>
    ((o τ).coord (i τ)).continuous_of_finiteDimensional.comp (continuous_apply τ)).mul continuous_const

theorem one_mem_UH {n : ℕ} (G : Matrix (Fin n) (Fin n) ℂ) : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ Formalism.QuantumDeterminants.UH G := by
  simp [Formalism.QuantumDeterminants.UH]

theorem hasDerivAt_pol {σ Z : Type} [Finite σ] (pt : MvPolynomial σ ℂ →ₗ[ℂ] (Z → ℂ)) (hpt : Function.Injective pt)
    (c : ℝ → MvPolynomial σ ℂ) (N : ℕ) (hc : ∀ t, (c t).totalDegree ≤ N) (y : MvPolynomial σ ℂ)
    (h : ∀ z, HasDerivAt (fun t => pt (c t) z) (pt y z) 0) (f : MvPolynomial σ ℂ →ₗ[ℂ] ℂ) :
    HasDerivAt (fun t => f (c t)) (f y) 0 :=
  hasDerivAt_dual_of_sep_sub (MvPolynomial.restrictTotalDegree σ ℂ (max N y.totalDegree))
    (fun z => LinearMap.proj z ∘ₗ pt) (fun x hx => hpt (by rw [map_zero]; exact funext hx)) c y
    (fun t => (MvPolynomial.mem_restrictTotalDegree _ _ _).2 ((hc t).trans (le_max_left _ _)))
    ((MvPolynomial.mem_restrictTotalDegree _ _ _).2 (le_max_right _ _)) h f

theorem exists_isItW : ∀ (D : D7) (V W : HSp D) (S S' : D.what₂.Tau → SPar) (θ : InfFam D) (M : DSModel V S) (M' : DSModel W S') (I : PolF D W.rank V.rank →ₗ[ℂ] (⨂[ℂ] τ, M'.H τ) →ₗ[ℂ] ⨂[ℂ] τ, M.H τ) (ρ : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ → PolF D W.rank V.rank → PolF D W.rank V.rank) (ρ' : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ → PolF D W.rank V.rank → PolF D W.rank V.rank), IsInfFam θ → (∀ τ, FiniteDimensional ℂ (M.H τ) ∧ M.sm τ = ⊤) → (∀ τ, FiniteDimensional ℂ (M'.H τ) ∧ M'.sm τ = ⊤) → I ≠ 0 → (∀ τ g φ, (ρ τ g φ).totalDegree ≤ φ.totalDegree) → (∀ τ h φ, (ρ' τ h φ).totalDegree ≤ φ.totalDegree) → (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ φ x, I (ρ τ g φ) x = actT M τ g (I φ x)) → (∀ τ, ∀ h ∈ Formalism.QuantumDeterminants.UH (gramAt D W τ), ∀ φ x, I (ρ' τ h φ) (actT M' τ h x) = I φ x) → ∃ It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M, ∀ (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (pt : PolF D W.rank V.rank →ₗ[ℂ] (WO V W → ℂ)), Function.Injective pt → (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ φ, ω (atTau θ V τ g, 1) (pt φ) = pt (ρ τ g φ)) → (∀ τ, ∀ h ∈ Formalism.QuantumDeterminants.UH (gramAt D W τ), ∀ φ, ω (1, atTau θ W τ h) (pt φ) = pt (ρ' τ h φ)) → IsItW θ M M' ω pt It := by
  intro D V W S S' θ M M' I ρ ρ' hθ hM hM' hI hd hd' hρ hρ'
  have fM := finite_tensor M fun τ => (hM τ).1
  have fM' := finite_tensor M' fun τ => (hM' τ).1
  let e := LinearEquiv.ofBijective (inclT M) (inclT_bij M fun τ => (hM τ).2)
  let e' := LinearEquiv.ofBijective (inclT M') (inclT_bij M' fun τ => (hM' τ).2)
  have he : ∀ x, inclT M (e.symm x) = x := fun x => e.apply_symm_apply x
  have he' : ∀ x, inclT M' (e'.symm x) = x := fun x => e'.apply_symm_apply x
  let It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M := (I.compl₂ (inclT M')).compr₂ e.symm.toLinearMap
  have hIt : ∀ φ v, inclT M (It φ v) = I φ (inclT M' v) := fun φ v => he _
  have hinj : Function.Injective (inclT M) := e.injective
  refine ⟨It, fun ω pt hpt hω hω' => ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro h0
    refine hI (LinearMap.ext fun φ => LinearMap.ext fun x => ?_)
    have := hIt φ (e'.symm x)
    rw [he', h0] at this
    simpa using this.symm
  · intro φ w
    haveI := fun τ => (hM' τ).1
    let m : (Π τ, M'.H τ) →ₘₗ[ℂ] ℂ :=
      (ellT M w ∘ₗ I φ).compMultilinearMap (PiTensorProduct.tprod ℂ)
    obtain ⟨c, -, hc⟩ := m.exists_bound_of_continuous (continuous_tprod M' this (ellT M w ∘ₗ I φ))
    refine ⟨c, fun v => ?_⟩
    rw [hIt]
    have := hc fun τ => (v τ : M'.H τ)
    simpa [m, inclT] using this
  · intro τ g hg φ φ' h v
    rw [hω τ g hg] at h
    rw [hpt h, hIt, hIt, hρ τ g hg]
  · intro τ X hX φ φ' h v w
    have hm : ∀ t : ℝ, NormedSpace.exp (t • X) ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) :=
      fun t => GlobalTheory.GardingVec.exp_mem (isUnit_gram M τ) hX t
    simp only [oneP, hω τ _ (hm _)] at h
    have := hasDerivAt_pol pt hpt (fun t : ℝ => ρ τ (NormedSpace.exp (t • X)) φ) _ (fun t => hd τ _ φ) φ' h
      (ellT M w ∘ₗ I.flip (inclT M' v))
    simp only [hIt, ← hρ τ _ (hm _)]
    exact this
  · intro τ g hg φ φ' v v' h h'
    rw [hω' τ g hg] at h
    apply hinj
    rw [hpt h, hIt, hIt, h', hρ' τ g hg]
  · intro τ X hX φ φ' v v' h h'
    have hm : ∀ t : ℝ, NormedSpace.exp (t • X) ∈ Formalism.QuantumDeterminants.UH (gramAt D W τ) :=
      fun t => GlobalTheory.GardingVec.exp_mem (isUnit_gram M' τ) hX t
    simp only [oneP, hω' τ _ (hm _)] at h
    have h1 : ∀ ψ, ρ' τ 1 ψ = ψ := fun ψ => hpt (by
      rw [← hω' τ 1 (one_mem_UH _), GlobalTheory.PointAtPlaceHom.atTau_one hθ]
      exact congrArg (fun f : Module.End ℂ (WO V W → ℂ) => f (pt ψ)) (map_one ω))
    apply hinj
    rw [map_add (f := _), hIt, hIt, map_zero]
    refine ellT_sep M (fun τ => (hM τ).1) _ fun w => ?_
    have hB := hasDerivAt_bilin (I.compr₂ (ellT M w)) (fun t : ℝ => ρ' τ (NormedSpace.exp (t • X)) φ) φ'
      (fun t : ℝ => actT M' τ (NormedSpace.exp (t • X)) (inclT M' v)) (inclT M' v')
      (hasDerivAt_pol pt hpt _ _ (fun t => hd' τ _ φ) φ' h)
      (hasDerivAt_dual_of_sep (ellT M') (ellT_sep M' fun τ => (hM' τ).1) _ _ h')
    simp only [LinearMap.compr₂_apply, hρ' τ _ (hm _), zero_smul, NormedSpace.exp_zero, h1] at hB
    have h2 := hρ' τ 1 (one_mem_UH _) φ' (inclT M' v)
    rw [h1] at h2
    rw [h2] at hB
    rw [map_add (f := _)]
    exact hB.unique (hasDerivAt_const _ _)

end GlobalTheory.CompactIntertwiner

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsThetaLiftAdjointScalarOnPart
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ScalChoice

theorem exists_pin (P : ℝ → Prop) (h : ∀ a b, P a → P b → a = b) : ∃ a, ∀ l, P l → a = l := by
  by_cases hP : ∃ a, P a
  · obtain ⟨a, ha⟩ := hP
    exact ⟨a, fun l hl => h a l ha hl⟩
  · exact ⟨0, fun l hl => absurd ⟨l, hl⟩ hP⟩

theorem exists_eig {M : Type*} [AddCommGroup M] [Module ℂ M] (S : Submodule ℂ M) (f : M → M) (c : ℝ) :
    ∃ a : ℝ, (∀ l : ℝ, S ≠ ⊥ → (∀ x ∈ S, f x = (l : ℂ) • x) → a = l) ∧ (S = ⊥ → a = c) := by
  rcases eq_or_ne S ⊥ with hW | hW
  · exact ⟨c, fun l h => absurd hW h, fun _ => rfl⟩
  · obtain ⟨a, ha⟩ := exists_pin (fun l => ∀ x ∈ S, f x = (l : ℂ) • x) (fun a b ha hb => by
        obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
        exact_mod_cast smul_left_injective ℂ hx0 ((ha x hx).symm.trans (hb x hx)))
    exact ⟨a, fun l _ h => ha l h, fun h => absurd h hW⟩

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

abbrev withScal (R : RealDat D A Ks) (lam : Fin D.R.m → T → A.fam.base.Ix → InfinitePlace D.what₂.LL → ℝ) (kap : ℝ) :
    RealDat D A Ks := { R with lam := lam, kap := kap }

def OffEq (R : RealDat D A Ks) (F : Face D A) (b : Bool) (i : Fin D.R.m) (p : A.fam.base.Ix)
    (v : InfinitePlace D.what₂.LL) (l : ℝ) : Prop :=
  ∀ x, (R.toCx F).tC F.cr b i A.μ0 (Cx.cpt A.v0.embedding x) ∈ (R.toCx F).Wp i p → ∀ y,
      inner ℂ ((R.toCx F).wC b i v (Cx.cpt v.embedding (((R.toCx F).liftMat F.cr b i A.μ0).mulVec x)))
          ((R.toCx F).wC b i v (Cx.cpt v.embedding (((R.toCx F).liftMat F.cr b i A.μ0).mulVec y))) =
        ((l : ℝ) : ℂ) * Formalism.HermitianLatticesTheory.majAt (Pi.basisFun D.what₂.LL _) ((Cx.lv (F.fc (R.toCx F).zs) b).XT i A.μ0) v x y

theorem OffEq.unique {R : RealDat D A Ks} {F : Face D A} {b : Bool} {i : Fin D.R.m} {p : A.fam.base.Ix}
    {v : InfinitePlace D.what₂.LL} {l l' : ℝ} (hp : R.PartAt F b i p v) (h : OffEq R F b i p v l)
    (h' : OffEq R F b i p v l') : l = l' := by
  obtain ⟨x, hx, hx0⟩ := hp
  have h1 := (h x hx x).symm.trans (h' x hx x)
  have h2 := mul_right_cancel₀ (by exact_mod_cast hx0) h1
  exact_mod_cast h2

theorem partAt_withScal (R : RealDat D A Ks) (F : Face D A) (lam) (kap : ℝ) (b i p v) :
    (withScal R lam kap).PartAt F b i p v ↔ R.PartAt F b i p v := Iff.rfl

theorem offEq_withScal (R : RealDat D A Ks) (F : Face D A) (lam) (kap : ℝ) (b i p v l) :
    OffEq (withScal R lam kap) F b i p v l ↔ OffEq R F b i p v l := Iff.rfl

theorem exists_thetaLift_adjoint_scalar_on_part (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (p : A.fam.base.Ix) (c : ℝ) :
    ∃ a : ℝ, (∀ l : ℝ, R.Wp i p ≠ ⊥ →
      (∀ x ∈ R.Wp i p, R.thG i t (LinearMap.adjoint (R.thG i t) x) = (l : ℂ) • x) → a = l) ∧ (R.Wp i p = ⊥ → a = c) :=
  exists_eig (R.Wp i p) (fun x => R.thG i t (LinearMap.adjoint (R.thG i t) x)) c

theorem exists_lamOff (R : RealDat D A Ks) (F : Face D A) (i : Fin D.R.m) (p : A.fam.base.Ix)
    (v : InfinitePlace D.what₂.LL) (c : ℝ) :
    ∃ a : ℝ, (∀ b (l : ℝ), R.PartAt F b i p v → (b = false ∨ ¬ R.PartAt F false i p v) → OffEq R F b i p v l → a = l) ∧
      ((∀ b, ¬ R.PartAt F b i p v) → a = c) := by
  by_cases h0 : R.PartAt F false i p v
  · obtain ⟨a, ha⟩ := exists_pin (OffEq R F false i p v) (fun a b => OffEq.unique h0)
    refine ⟨a, fun b l _ hb h => ?_, fun h => absurd h0 (h false)⟩
    rcases hb with rfl | hb
    · exact ha l h
    · exact absurd h0 hb
  · by_cases h1 : R.PartAt F true i p v
    · obtain ⟨a, ha⟩ := exists_pin (OffEq R F true i p v) (fun a b => OffEq.unique h1)
      refine ⟨a, fun b l hp _ h => ?_, fun h => absurd h1 (h true)⟩
      cases b
      · exact absurd hp h0
      · exact ha l h
    · refine ⟨c, fun b l hp _ _ => ?_, fun _ => rfl⟩
      cases b
      · exact absurd hp h0
      · exact absurd hp h1

theorem exists_isScal : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), ∀ F : Face D A, ∃ lam kap, ({ R with lam := lam, kap := kap } : RealDat D A Ks).IsScal F := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F
  classical
  choose f0 hf0 hf0' using fun i t p => exists_thetaLift_adjoint_scalar_on_part R i t p (Real.exp ((F.Zsc (R.toCx F).zs).l6m i))
  choose f1 hf1 hf1' using fun i p v => exists_lamOff R F i p v (Real.exp ((F.Zsc (R.toCx F).zs).l6m i))
  obtain ⟨lam, h0, h1⟩ : ∃ lam : Fin D.R.m → T → A.fam.base.Ix → InfinitePlace D.what₂.LL → ℝ,
      (∀ i t p, lam i t p A.v0 = f0 i t p) ∧ ∀ i t p v, v ≠ A.v0 → lam i t p v = f1 i p v :=
    ⟨fun i t p v => if v = A.v0 then f0 i t p else f1 i p v, fun i t p => if_pos rfl, fun i t p v hv => if_neg hv⟩
  obtain ⟨kap, hk⟩ := exists_pin (fun κ => Lift.IsKap D.R.m (fun t => R.Th t ∘ₗ LinearMap.adjoint (R.Th t)) R.EEp
      (withScal R lam 0).lamN κ ∧ ∃ t p, R.EEp p ≠ ⊥ ∧ ∏ j ∈ Finset.Icc 1 D.R.m, (withScal R lam 0).lamN t j p ≠ 0)
    (fun a b ha hb => by
      obtain ⟨t, p, hp, hl⟩ := ha.2
      exact Lift.IsKap.unique ha.1 hb.1 t p hp hl)
  refine ⟨lam, kap, (?_ : (withScal R lam kap).IsScal F)⟩
  refine ⟨fun i t p l hW h => ?_, fun κ h h' => hk κ ⟨h, h'⟩, fun b i p v l hv hp hb h => ?_, fun i t p hW => ?_,
    fun i p v hv h => ?_, fun i t p v hv => ?_⟩
  · exact (h0 i t p).trans (hf0 i t p l hW h)
  · refine (h1 i _ p v hv).trans (hf1 i p v b l ((partAt_withScal R F lam kap b i p v).1 hp) ?_
      ((offEq_withScal R F lam kap b i p v l).1 h))
    rwa [partAt_withScal] at hb
  · exact (h0 i t p).trans (hf0' i t p hW)
  · exact (h1 i _ p v hv).trans (hf1' i p v fun b hb => h b ((partAt_withScal R F lam kap b i p v).2 hb))
  · exact (h1 i t p v hv).trans (h1 i _ p v hv).symm

end GlobalTheory.ScalChoice
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitOfCocompact
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory IsDedekindDomain NumberField
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Per.UnitN

theorem exists_unit_of_cocompact {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
    [BorelSpace G] [LocallyCompactSpace G] [SecondCountableTopology G] (Γ : Subgroup G) [Countable Γ] [DiscreteTopology Γ]
    {K : Set G} (hK : IsCompact K) (hcov : ∀ n, ∃ γ ∈ Γ, ∃ k ∈ K, n = γ * k) :
    ∃ (ν : Measure G) (𝓝 : Set G), ν.IsHaarMeasure ∧ IsFundamentalDomain Γ 𝓝 ν ∧ ν 𝓝 = 1 := by
  let μ : Measure G := Measure.haar
  obtain ⟨𝓕, h⟩ := GlobalTheory.FundDomDiscrete.exists_isFundamentalDomain Γ μ
  have hle : μ 𝓕 ≤ μ K := by
    rw [h.measure_eq_tsum K]
    refine (measure_mono fun n hn => ?_).trans (measure_iUnion_le _)
    obtain ⟨γ, hγ, k, hk, rfl⟩ := hcov n
    exact Set.mem_iUnion.2 ⟨⟨γ, hγ⟩, ⟨k, hk, rfl⟩, hn⟩
  have hfin : μ 𝓕 ≠ ⊤ := (hle.trans_lt hK.measure_lt_top).ne
  have hpos : μ 𝓕 ≠ 0 := h.measure_ne_zero (NeZero.ne μ)
  refine ⟨(μ 𝓕)⁻¹ • μ, 𝓕, Measure.IsHaarMeasure.smul μ (ENNReal.inv_ne_zero.2 hfin) (ENNReal.inv_ne_top.2 hpos),
    h.mono Measure.smul_absolutelyContinuous, ?_⟩
  rw [Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel hpos hfin]

theorem exists_isUnitN : ∀ (D : D7) (B : HSp D) (ρ : ℕ) (e : Matrix (Fin B.rank) (Fin ρ) D.host.E), IsIsoSub B e →
    ∃ ν 𝓝, GlobalTheory.Per.IsUnitN B e ν 𝓝 := by
  intro D B ρ e he
  obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B
  obtain ⟨K, hK, h⟩ := (GlobalTheory.Mem.UnipCocompact.radicals_cocompact D B ρ e he).1
  have hcl : IsClosed (NFlag B e : Set (GA D B)) := by
    have : DiscreteTopology (GQ B ⊓ NFlag B e : Subgroup (GA D B)) :=
      DiscreteTopology.of_subset (s := (GQ B : Set (GA D B))) i6 (fun x hx => hx.1)
    have h1 : IsClosed ((GQ B ⊓ NFlag B e : Subgroup (GA D B)) : Set (GA D B)) := Subgroup.isClosed_of_discrete
    have h2 := h1.mul_right_of_isCompact (hK.image continuous_subtype_val)
    convert h2 using 1
    ext x
    constructor
    · intro hx
      obtain ⟨γ, hγ, k, hk, e⟩ := h ⟨x, hx⟩
      exact ⟨γ, ⟨hγ, γ.2⟩, k, ⟨k, hk, rfl⟩, (congrArg Subtype.val e).symm⟩
    · rintro ⟨γ, hγ, _, ⟨k, -, rfl⟩, rfl⟩
      exact mul_mem hγ.2 k.2
  have : LocallyCompactSpace (NFlag B e) := hcl.locallyCompactSpace
  have : SecondCountableTopology (NFlag B e) := TopologicalSpace.Subtype.secondCountableTopology _
  have hinj : Function.Injective fun γ : NFlagQ B e => (⟨γ.1.1, γ.2⟩ : GQ B) :=
    fun a b h => Subtype.ext (Subtype.ext (congrArg (fun x : GQ B => (x : GA D B)) h))
  have : Countable (NFlagQ B e) := hinj.countable
  have : DiscreteTopology (NFlagQ B e) :=
    DiscreteTopology.of_continuous_injective
      ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _) hinj
  exact exists_unit_of_cocompact (NFlagQ B e) hK h

end GlobalTheory.Per.UnitN
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LowestKTypeSmoothVectorsIsKStable
section
noncomputable section

open Matrix
open scoped ContDiff

namespace GlobalTheory.SmoothLowKStable

open Formalism.MainNotions.S GlobalTheory.GardingVec

theorem list_prod_conj {n : ℕ} {g h : Matrix (Fin n) (Fin n) ℂ} (hgh : g * h = 1)
    (l : List (Matrix (Fin n) (Fin n) ℂ)) : l.prod * g = g * (l.map fun x => h * x * g).prod := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.map_cons, List.prod_cons, List.prod_cons, Matrix.mul_assoc, ih]
    simp only [← Matrix.mul_assoc, hgh, Matrix.one_mul]

theorem smoothVec_apply {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hmul : ∀ g ∈ UJset ε, ∀ h ∈ UJset ε, σ (g * h) = σ g * σ h) {P G : Matrix (Fin n) (Fin n) ℂ} (hP : IsUnit P)
    (h : Pᴴ * Formalism.REAL.Jm ε * P = G) {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ UJset ε) {v : H}
    (hv : Formalism.L2.Theta.SmoothVec {X | Xᴴ * G + G * X = 0} (fun g => σ (P * g * P⁻¹)) v) :
    Formalism.L2.Theta.SmoothVec {X | Xᴴ * G + G * X = 0} (fun g => σ (P * g * P⁻¹)) (σ k v) := by
  have hG : IsUnit G := by
    rw [← h]
    exact (((Matrix.isUnit_conjTranspose _).2 hP).mul
      (IsUnit.of_mul_eq_one _ (Formalism.REAL.Jm_mul_self ε))).mul hP
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP
  have hPP : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ hd
  have hPP' : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul _ hd
  have hk' : kᴴ * Formalism.REAL.Jm ε * k = Formalism.REAL.Jm ε := hk
  set g := P⁻¹ * k * P with hg
  have hPg : P * g = k * P := by rw [hg, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hPP, Matrix.one_mul]
  have hgG : gᴴ * G * g = G := by
    calc gᴴ * G * g = (P * g)ᴴ * Formalism.REAL.Jm ε * (P * g) := by
          rw [← h]; simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = Pᴴ * (kᴴ * Formalism.REAL.Jm ε * k) * P := by rw [hPg]; simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = G := by rw [hk', h]
  have hgu : IsUnit g := by
    have : IsUnit (gᴴ * G * g).det := by rw [hgG]; exact (Matrix.isUnit_iff_isUnit_det G).1 hG
    rw [Matrix.det_mul] at this
    exact (Matrix.isUnit_iff_isUnit_det g).2 (isUnit_of_mul_isUnit_right this)
  have hgd : IsUnit g.det := (Matrix.isUnit_iff_isUnit_det g).1 hgu
  have hgg : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv _ hgd
  have hGg : G * g⁻¹ = gᴴ * G := by
    conv_lhs => rw [← hgG]
    rw [Matrix.mul_assoc, hgg, Matrix.mul_one]
  have hGg' : (g⁻¹)ᴴ * G = G * g := by
    conv_lhs => rw [← hgG]
    rw [Matrix.mul_assoc gᴴ, ← Matrix.mul_assoc, ← conjTranspose_mul, hgg, conjTranspose_one, Matrix.one_mul]
  intro m Xs hX
  have hY : ∀ i, (g⁻¹ * Xs i * g)ᴴ * G + G * (g⁻¹ * Xs i * g) = 0 := fun i => by
    have hXi : (Xs i)ᴴ * G + G * Xs i = 0 := hX i
    calc (g⁻¹ * Xs i * g)ᴴ * G + G * (g⁻¹ * Xs i * g)
        = gᴴ * (Xs i)ᴴ * ((g⁻¹)ᴴ * G) + (G * g⁻¹) * Xs i * g := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = gᴴ * ((Xs i)ᴴ * G + G * Xs i) * g := by
          rw [hGg, hGg']; simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
      _ = 0 := by rw [hXi]; simp
  have hs := hv m (fun i => g⁻¹ * Xs i * g) hY
  have hmem : ∀ (Ys : Fin m → Matrix (Fin n) (Fin n) ℂ), (∀ i, (Ys i)ᴴ * G + G * Ys i = 0) → ∀ t : Fin m → ℝ,
      P * (List.ofFn fun i => NormedSpace.exp (t i • Ys i)).prod * P⁻¹ ∈ UJset ε := fun Ys hYs t => by
    refine conj_mem hP h (list_prod_mem _ fun g hg => ?_)
    obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hg
    exact exp_mem hG (hYs i) _
  have key : ∀ t : Fin m → ℝ,
      σ (P * (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod * P⁻¹) (σ k v)
        = σ k (σ (P * (List.ofFn fun i => NormedSpace.exp (t i • (g⁻¹ * Xs i * g))).prod * P⁻¹) v) := fun t => by
    have e1 : (List.ofFn fun i => NormedSpace.exp (t i • (g⁻¹ * Xs i * g)))
        = (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).map fun x => g⁻¹ * x * g := by
      rw [List.map_ofFn]
      congr 1
      funext i
      rw [Function.comp_apply, ← Matrix.exp_conj' _ _ hgu, Matrix.mul_smul, Matrix.smul_mul]
    have e2 := list_prod_conj hgg (List.ofFn fun i => NormedSpace.exp (t i • Xs i))
    rw [← ContinuousLinearMap.mul_apply, ← ContinuousLinearMap.mul_apply, ← hmul _ (hmem Xs hX t) _ hk,
      ← hmul _ hk _ (hmem _ hY t), e1]
    congr 2
    have e3 : P⁻¹ * k = g * P⁻¹ := by rw [hg, Matrix.mul_assoc _ P, hPP, Matrix.mul_one]
    rw [Matrix.mul_assoc _ P⁻¹, e3, ← Matrix.mul_assoc, Matrix.mul_assoc P, e2]
    simp only [← Matrix.mul_assoc, hPg]
  have := ((σ k).restrictScalars ℝ).contDiff.comp hs
  refine (funext key : _ = _) ▸ this

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult
  Formalism.IndefR.Datum Formalism.IndefR.FWT

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem isKStableOn_lowKSub_inf_sm (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S)
    (τ : D.what₂.Tau) : IsKStableOn (M.ε τ) (M.σ τ) (lowKSub (M.ε τ) (M.lam τ) (M.σ τ) ⊓ M.sm τ) := by
  intro k hk w hw
  have hkU : k ∈ UJset (M.ε τ) := by
    show kᴴ * Formalism.REAL.Jm _ * k = Formalism.REAL.Jm _
    have h1 : kᴴ * k = 1 := (Matrix.mem_unitaryGroup_iff').1 hk.1
    rw [Matrix.mul_assoc, ← hk.2, ← Matrix.mul_assoc, h1, Matrix.one_mul]
  refine ⟨?_, ?_⟩
  · have : lowKSub (M.ε τ) (M.lam τ) (M.σ τ)
        ≤ (lowKSub (M.ε τ) (M.lam τ) (M.σ τ)).comap (M.σ τ k : _ →ₗ[ℂ] _) :=
      sSup_le fun T hT v hv => (le_sSup hT : T ≤ _) (hT.2.1 k hk v hv)
    exact this hw.1
  · have : M.sm τ ≤ (M.sm τ).comap (M.σ τ k : _ →ₗ[ℂ] _) :=
      Submodule.span_le.2 fun v hv => Submodule.subset_span
        (smoothVec_apply (M.ds τ).2.2.1.1.2 (M.fr_unit τ) (M.fr_gram τ) hkU hv)
    exact this hw.2

end GlobalTheory.SmoothLowKStable

end
end

