module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0519
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0520
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0010
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
public import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.IsSmoothHermConstLine
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockImageInverse
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.LocCompareSplit
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0521
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1081
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenCellJacquetIntegralVolume
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0331
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0344
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0470
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0503
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothVectorCompactUnipotentFixer

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemLatticeOfDualPairing
section
noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.LatticeDualityAlt

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix

theorem exists_extend {K : Type} [Field K] [NumberField K] {m : ℕ}
    (L : Submodule (𝓞 K) (Fin m → K))
    (hs : Submodule.span K (L : Set (Fin m → K)) = ⊤) (φ : L →ₗ[𝓞 K] 𝓞 K) :
    ∃ G : (Fin m → K) →ₗ[K] K, ∀ x : L, G x = algebraMap (𝓞 K) K (φ x) := by
  classical
  have hs' : ⊤ ≤ Submodule.span K (L : Set (Fin m → K)) := hs.ge
  obtain ⟨ι, b, hb⟩ : ∃ (ι : Type) (b : Module.Basis ι K (Fin m → K)), ∀ i, b i ∈ L :=
    ⟨_, Module.Basis.ofSpan hs', fun i => Module.Basis.ofSpan_subset hs' ⟨i, rfl⟩⟩
  haveI := Module.Finite.finite_basis b
  haveI := Fintype.ofFinite ι
  let G : (Fin m → K) →ₗ[K] K := b.constr K (fun i => algebraMap (𝓞 K) K (φ ⟨b i, hb i⟩))
  have hGb : ∀ i, G (b i) = algebraMap (𝓞 K) K (φ ⟨b i, hb i⟩) := fun i => b.constr_basis _ _ _
  refine ⟨G, fun x => ?_⟩
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors (𝓞 K))
    (fun i => b.repr (x : Fin m → K) i) (S := K)
  choose e he using hd
  have hx : ((d : 𝓞 K) • (x : Fin m → K)) = ∑ i, e i • b i := by
    conv_lhs => rw [← b.sum_repr (x : Fin m → K)]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← algebraMap_smul K (e i) (b i), he i, smul_assoc]
  have hxL : (d : 𝓞 K) • x = ∑ i, e i • (⟨b i, hb i⟩ : L) := by
    apply Subtype.ext
    simpa using hx
  have h1 : (d : 𝓞 K) * φ x = ∑ i, e i * φ ⟨b i, hb i⟩ := by
    have h := congrArg φ hxL
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_smul, map_sum, smul_eq_mul] at h
    rw [h]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul, smul_eq_mul]
  have h2 : algebraMap (𝓞 K) K (d : 𝓞 K) * G x = algebraMap (𝓞 K) K ((d : 𝓞 K) * φ x) := by
    have h3 : algebraMap (𝓞 K) K (d : 𝓞 K) * G x = G ((d : 𝓞 K) • (x : Fin m → K)) := by
      rw [← algebraMap_smul K (d : 𝓞 K) (x : Fin m → K), map_smul, smul_eq_mul]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [h3, hx, h1, map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← algebraMap_smul K (e i) (b i), map_smul, hGb, smul_eq_mul, map_mul]
  have hd0 : algebraMap (𝓞 K) K (d : 𝓞 K) ≠ 0 := by
    have := nonZeroDivisors.ne_zero d.2
    simpa using this
  rw [map_mul] at h2
  exact mul_left_cancel₀ hd0 h2

theorem mem_of_dot_integral : ∀ (K : Type) [Field K] [NumberField K] (m : ℕ)
    (L : Submodule (𝓞 K) (Fin m → K)), IsLat L → ∀ v : Fin m → K,
    (∀ a : Fin m → K, (∀ x ∈ L, a ⬝ᵥ x ∈ (1 : Submodule (𝓞 K) K)) →
      a ⬝ᵥ v ∈ (1 : Submodule (𝓞 K) K)) → v ∈ L := by
  intro K _ _ m L hL v hv
  obtain ⟨hfg, hspan⟩ := hL
  haveI : Module.Finite (𝓞 K) L := Module.Finite.iff_fg.mpr hfg
  haveI : Module.IsTorsionFree (𝓞 K) L := inferInstance
  haveI : Module.FinitePresentation (𝓞 K) L := Module.finitePresentation_of_finite _ _
  haveI : Module.Projective (𝓞 K) L := Module.Flat.projective_of_finitePresentation
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' (𝓞 K) L
  obtain ⟨s, hs⟩ := Module.projective_lifting_property f LinearMap.id hf
  let φ : Fin n → L →ₗ[𝓞 K] 𝓞 K := fun i => (LinearMap.proj i).comp s
  let l : Fin n → L := fun i => f (fun j => if i = j then 1 else 0)
  have hdual : ∀ x : L, x = ∑ i, φ i x • l i := by
    intro x
    have h1 : f (s x) = x := LinearMap.congr_fun hs x
    have h2 := LinearMap.pi_apply_eq_sum_univ f (s x)
    rw [h1] at h2
    exact h2
  choose G hG using fun i => exists_extend L hspan (φ i)
  let a : Fin n → Fin m → K := fun i j => G i (fun k => if j = k then 1 else 0)
  have ha : ∀ i w, a i ⬝ᵥ w = G i w := by
    intro i w
    rw [LinearMap.pi_apply_eq_sum_univ (G i) w]
    simp [dotProduct, a, mul_comm]
  have hid : ∀ w : Fin m → K, w = ∑ i, G i w • (l i : Fin m → K) := by
    let T : (Fin m → K) →ₗ[K] (Fin m → K) := ∑ i, (G i).smulRight (l i : Fin m → K)
    have hT : T = LinearMap.id := by
      refine LinearMap.ext_on hspan ?_
      intro x hx
      have h1 := congrArg (Subtype.val) (hdual ⟨x, hx⟩)
      simp only [T, LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.id_apply]
      have h2 : ∀ i, G i x • (l i : Fin m → K) = φ i ⟨x, hx⟩ • (l i : Fin m → K) := by
        intro i
        rw [show G i x = algebraMap (𝓞 K) K (φ i ⟨x, hx⟩) from hG i ⟨x, hx⟩, algebraMap_smul]
      simp only [h2]
      simpa using h1.symm
    intro w
    have h := LinearMap.congr_fun hT w
    simpa [T, LinearMap.sum_apply] using h.symm
  have hint : ∀ i, ∃ o : 𝓞 K, algebraMap (𝓞 K) K o = a i ⬝ᵥ v := by
    intro i
    have h := hv (a i) (fun x hx => by
      rw [(ha i x).trans (hG i ⟨x, hx⟩)]
      exact Submodule.mem_one.mpr ⟨_, rfl⟩)
    exact Submodule.mem_one.mp h
  choose o ho using hint
  rw [hid v]
  refine Submodule.sum_mem _ fun i _ => ?_
  have h3 : G i v • (l i : Fin m → K) = o i • (l i : Fin m → K) := by
    rw [← ha, ← ho, algebraMap_smul]
  rw [h3]
  exact L.smul_mem _ (l i).2

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.LatticeDualityAlt
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultiprojectivePrimeEqPointIdeal
section
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict
open GlobalTheory

namespace GlobalTheory.CompanionTheory.MPDict.Onto

open GroundTheory.Heights₂.Heights.HilbertSamuel.BlockImageInverse (mConeMap_of_isMultiHomog)

section Coord

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem mCoordIdeal_comp_ringHom {L Ω : Type} [Field L] [Field Ω] (j : L →+* Ω) (w : (Σ k, ι k) → L) :
    Geo.mCoordIdeal (fun p => j (w p)) = Geo.mCoordIdeal w := by
  have key : ∀ f : Geo.MRing ι, Geo.mConeMap (fun p => j (w p)) f = MvPolynomial.map j (Geo.mConeMap w f) := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C a => simp [Geo.mConeMap]
    | add p q hp hq => simp only [map_add (f := _), hp, hq]
    | mul_X p q hp =>
      rw [map_mul, map_mul, map_mul, hp]
      simp [Geo.mConeMap]
  ext f
  simp only [Geo.mCoordIdeal, RingHom.mem_ker, key]
  exact map_eq_zero_iff _ (MvPolynomial.map_injective j j.injective)

theorem mCoordIdeal_blockScale {Ω : Type} [Field Ω] (c : K → Ω) (hc : ∀ k, c k ≠ 0) (z : (Σ k, ι k) → Ω) :
    Geo.mCoordIdeal (fun p : Σ k, ι k => c p.1 * z p) = Geo.mCoordIdeal z := by
  let φ : MvPolynomial K Ω →ₐ[Ω] MvPolynomial K Ω := aeval fun k => C (c k) * X k
  let φ' : MvPolynomial K Ω →ₐ[Ω] MvPolynomial K Ω := aeval fun k => C (c k)⁻¹ * X k
  have hinv : φ'.comp φ = AlgHom.id Ω _ := by
    apply MvPolynomial.algHom_ext
    intro k
    simp only [φ, φ', AlgHom.comp_apply, aeval_X, map_mul, aeval_C, AlgHom.id_apply]
    rw [← mul_assoc, algebraMap_eq, ← C_mul, mul_inv_cancel₀ (hc k), C_1, one_mul]
  have hinj : Function.Injective φ := fun a b h => by
    have := congrArg φ' h
    rwa [← AlgHom.comp_apply, ← AlgHom.comp_apply, hinv] at this
  have hcomp : ∀ g, Geo.mConeMap (fun p : Σ k, ι k => c p.1 * z p) g = φ (Geo.mConeMap z g) := by
    intro g
    have : Geo.mConeMap (fun p : Σ k, ι k => c p.1 * z p) = (φ.restrictScalars ℤ).comp (Geo.mConeMap z) := by
      apply MvPolynomial.algHom_ext
      intro p
      simp only [Geo.mConeMap, aeval_X, AlgHom.comp_apply, AlgHom.restrictScalars_apply, φ, map_mul, aeval_C,
        algebraMap_eq]
      ring
    rw [this]; rfl
  ext g
  simp only [Geo.mCoordIdeal, RingHom.mem_ker, hcomp, map_eq_zero_iff φ hinj]

theorem mCoordIdeal_of_ker {Ω : Type} [Field Ω] (P : Ideal (Geo.MRing ι)) (hP : Geo.IsMultiHomogIdeal P)
    (φ : Geo.MRing ι →+* Ω) (hφ : RingHom.ker φ = P) : Geo.mCoordIdeal (fun p => φ (X p)) = P := by
  have hev : ∀ f, aeval (fun p => φ (X p)) f = φ f := by
    intro f
    have : ((aeval (fun p => φ (X p)) : Geo.MRing ι →ₐ[ℤ] Ω) : Geo.MRing ι →+* Ω) = φ :=
      MvPolynomial.ringHom_ext
        (fun r => RingHom.congr_fun (Subsingleton.elim
          (((aeval (fun p => φ (X p)) : Geo.MRing ι →ₐ[ℤ] Ω) : Geo.MRing ι →+* Ω).comp C) (φ.comp C)) r)
        (fun p => by simp)
    exact congrArg (fun ψ => ψ f) this
  apply le_antisymm
  · intro f hf
    rw [Geo.mCoordIdeal, RingHom.mem_ker] at hf
    have e : ((aeval fun _ : K => (1 : Ω)).restrictScalars ℤ).comp
        (Geo.mConeMap (fun p => φ (X p))) = aeval (fun p => φ (X p)) := by
      apply MvPolynomial.algHom_ext
      intro p
      simp [Geo.mConeMap]
    have := congrArg (fun ψ => ψ f) e
    simp only [AlgHom.comp_apply, hf, map_zero, hev] at this
    rw [← hφ, RingHom.mem_ker]
    exact this.symm
  · have hP' := hP
    obtain ⟨S, hS, hPS⟩ := hP'
    rw [hPS, Ideal.span_le]
    intro f hf
    obtain ⟨a, ha⟩ := hS f hf
    have h0 : φ f = 0 := by
      rw [← RingHom.mem_ker, hφ, hPS]
      exact Ideal.subset_span hf
    rw [SetLike.mem_coe, Geo.mCoordIdeal, RingHom.mem_ker, mConeMap_of_isMultiHomog _ ha, hev, h0, C_0, mul_zero]

end Coord

variable {m : ℕ} {n : Fin (m + 1) → ℕ}

theorem evaluation_resG' {X : Scheme.{0}} {U V : X.Opens} (h : V ≤ U) (x : X) (hx : x ∈ V) (s : Γ(X, U)) :
    (X.evaluation V x hx).hom (resG X h s) = (X.evaluation U x (h hx)).hom s := by
  show X.residue x (X.presheaf.germ V x hx (X.presheaf.map (homOfLE h).op s)) = _
  rw [TopCat.Presheaf.germ_res_apply]
  rfl

theorem exists_ptIdeal_eq_mCoordIdeal {F : Type} [Field F] (v : (Σ k, Bk n k) → F)
    (hv : ∀ k, ∃ i, v ⟨k, i⟩ ≠ 0) : ∃ x : MP ℤ m n, ptIdeal x = Geo.mCoordIdeal v := by
  have hu : ∀ k, Ideal.span (Set.range fun i : Bk n k => v ⟨k, i⟩) = ⊤ := fun k => by
    obtain ⟨i, hi⟩ := hv k
    exact Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨i, rfl⟩) (isUnit_iff_ne_zero.2 hi)
  let a : ∀ k, Sp F ⟶ PSpace ℤ (n k) := fun k =>
    GlobalTheory.ProjSpace.pt (Int.castRingHom F) (fun i : Bk n k => v ⟨k, i⟩) (hu k)
  have ha : ∀ k, a k ≫ ProjSpace.toSpecBase ℤ (n k) = spMap (Int.castRingHom F) := by
    intro k
    dsimp only [a]
    rw [GlobalTheory.ProjSpace.pt, ProjSpace.toSpecBase, ProjPoint.ofHom_toSpecZero_assoc,
      ← Spec.map_comp]
    congr 1
    ext1
    exact RingHom.ext fun r => MvPolynomial.eval₂Hom_C _ _ r
  let g : Sp F ⟶ MP ℤ m n := ProjSpace.lift m n (spMap (Int.castRingHom F)) a ha
  have hg : ∀ k, g ≫ prB n k = a k := fun k => ProjSpace.lift_pr m n _ a ha k
  let p : Sp F := IsLocalRing.closedPoint F
  let x : MP ℤ m n := g p
  let θ : F →+* (Sp F).residueField p :=
    ((Sp F).evaluation ⊤ p trivial).hom.comp (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom
  let ρ : (MP ℤ m n).residueField x →+* (Sp F).residueField p := (g.residueFieldMap p).hom
  have key : ∀ (k : Fin (m + 1)) (j : Bk n k),
      θ (v ⟨k, ptChart x k⟩) * ρ (ptCoord x ⟨k, j⟩) = θ (v ⟨k, j⟩) := by
    intro k j
    have hx : g p ∈ blockChart n k (ptChart x k) := mem_ptChart x k
    have hW : g ⁻¹ᵁ blockChart n k (ptChart x k) ≤ a k ⁻¹ᵁ chart ℤ (n k) (ptChart x k) := by
      rw [← hg k]
      exact le_of_eq rfl
    have e1 : ρ (ptCoord x ⟨k, j⟩) = ((Sp F).evaluation _ p hx).hom
        (pullRatio (a k) (g ⁻¹ᵁ blockChart n k (ptChart x k)) (ptChart x k) hW j) := by
      refine (Scheme.evaluation_naturality_apply g p hx _).trans ?_
      refine congrArg _ ?_
      have := appLE_pullRatio (φ := prB n k) (W := blockChart n k (ptChart x k)) (i := ptChart x k)
        (hi := le_rfl) (j := j) g (T := g ⁻¹ᵁ blockChart n k (ptChart x k)) le_rfl
      exact this.trans (pullRatio_of_eq (hg k) _ _)
    have e2 := pullRatio_pt_mul (Int.castRingHom F) (fun i : Bk n k => v ⟨k, i⟩) (hu k)
      (W := g ⁻¹ᵁ blockChart n k (ptChart x k)) (ptChart x k) j hW
    have e3 : ∀ b : F, ((Sp F).evaluation _ p hx).hom (fnOn (g ⁻¹ᵁ blockChart n k (ptChart x k)) b) = θ b :=
      fun b => evaluation_resG' le_top p hx _
    have := congrArg ((Sp F).evaluation _ p hx).hom e2
    rw [map_mul, e3, e3] at this
    rw [e1, mul_comm]
    exact this
  have hne : ∀ k, θ (v ⟨k, ptChart x k⟩) ≠ 0 := by
    intro k
    refine (map_ne_zero θ).2 fun h0 => ?_
    have hx : p ∈ a k ⁻¹ᵁ chart ℤ (n k) (ptChart x k) := by
      have : g p ∈ blockChart n k (ptChart x k) := mem_ptChart x k
      rw [← hg k]
      exact this
    rw [GlobalTheory.ProjSpace.pt_preimage_chart, GlobalTheory.ProjSpace.mem_spOpen] at hx
    exact hx (h0 ▸ Ideal.zero_mem _)
  refine ⟨x, ?_⟩
  rw [ptIdeal, ← mCoordIdeal_comp_ringHom ρ, ← mCoordIdeal_comp_ringHom θ v,
    ← mCoordIdeal_blockScale (fun k => θ (v ⟨k, ptChart x k⟩)) hne]
  congr 1
  funext q
  obtain ⟨k, j⟩ := q
  exact key k j

theorem exists_ptIdeal_eq (m : ℕ) (n : Fin (m + 1) → ℕ) (P : Ideal (Geo.MRing (Bk n)))
    (hP : Geo.IsMultiProjPrime P) : ∃ x : MP ℤ m n, ptIdeal x = P := by
  obtain ⟨hp, hh, hr⟩ := hP
  let φ : Geo.MRing (Bk n) →+* FractionRing (Geo.MRing (Bk n) ⧸ P) :=
    (algebraMap (Geo.MRing (Bk n) ⧸ P) _).comp (Ideal.Quotient.mk P)
  have hφ : RingHom.ker φ = P := by
    ext f
    rw [RingHom.mem_ker, ← Ideal.Quotient.eq_zero_iff_mem]
    exact map_eq_zero_iff (algebraMap (Geo.MRing (Bk n) ⧸ P) (FractionRing (Geo.MRing (Bk n) ⧸ P)))
      (IsFractionRing.injective (Geo.MRing (Bk n) ⧸ P) (FractionRing (Geo.MRing (Bk n) ⧸ P)))
  have hv : ∀ k, ∃ i, φ (X ⟨k, i⟩) ≠ 0 := fun k => by
    obtain ⟨i, hi⟩ := hr k
    refine ⟨i, fun h0 => hi ?_⟩
    rw [← hφ, RingHom.mem_ker]
    exact h0
  obtain ⟨x, hx⟩ := exists_ptIdeal_eq_mCoordIdeal (fun p => φ (X p)) hv
  exact ⟨x, hx.trans (mCoordIdeal_of_ker P hh φ hφ)⟩

end GlobalTheory.CompanionTheory.MPDict.Onto
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormCharpolySeparableOfElliptic
section
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin GlobalTheory.CompanionTheory.LocalHypotheses
open scoped Classical

namespace GlobalTheory.CompanionTheory.SepLocEl

theorem cj_algebraMap {E : Type} [Field E] [NumberField E] [IsCMField E] {w : Pl E} (hw : ¬ IsSplitAt w) (x : E) :
    GlobalTheory.BCT.cj w (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x) := by
  have key : ∀ (v : Pl E) (_ : v = w) (f : v.adicCompletion E →+* w.adicCompletion E), Continuous f →
      (∀ k : E, f (algebraMap E _ k) = algebraMap E _ (GlobalTheory.SplitPts.conjE (E := E) k)) →
      GlobalTheory.BCT.cj w (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x) := by
    rintro v rfl f hf h
    have hex : ∃ s : v.adicCompletion E →+* v.adicCompletion E, Continuous s ∧
        ∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x) := ⟨f, hf, h⟩
    rw [GlobalTheory.BCT.cj, dite_eq_left hex]
    exact hex.choose_spec.2 x
  have hinv : conjSrc (GlobalTheory.SplitPts.conjE (E := E))
      (conjSrc (GlobalTheory.SplitPts.conjE (E := E)) w) = w := by
    apply (eq_conjSrc (fun x => ?_)).symm
    rw [← conjPl_conjSrc (GlobalTheory.SplitPts.conjE (E := E)) w
      (GlobalTheory.SplitPts.conjE (E := E) x)]
    exact congrArg _ (IsCMField.complexConj_apply_apply E x)
  have hsrc : conjSrc (GlobalTheory.SplitPts.conjE (E := E)) w = w := by
    by_contra hne
    apply hw
    refine ⟨_, hne, (GlobalTheory.Mem.Chr.under_eq_iff_conjPl (IsCMField.complexConj E)
      (Algebra.IsQuadraticExtension.finrank_eq_two _ _) (IsCMField.complexConj_ne_one E) w _).2 ?_⟩
    right
    have h := conjPl_conjSrc (GlobalTheory.SplitPts.conjE (E := E))
      (conjSrc (GlobalTheory.SplitPts.conjE (E := E)) w)
    rwa [hinv] at h
  exact key _ hsrc _
    (conjLoc_spec (GlobalTheory.SplitPts.conjE (E := E)) _).1 (conjLoc_spec (GlobalTheory.SplitPts.conjE (E := E)) _).2.1

theorem nrmL_locEl {E : Type} [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) (δ : GL (Fin n) E) :
    nrmL n w (locEl n w δ) = GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) (δ * thE E n δ) := by
  by_cases h : IsSplitAt w
  · simp only [nrmL, locEl, if_pos h]
  · simp only [nrmL, locEl, if_neg h]
    rw [map_mul]
    congr 1
    exact (GlobalTheory.ThetaPull.map_thetaGL (algebraMap E (w.adicCompletion E)) _ (GlobalTheory.BCT.cj w)
      (fun x => (cj_algebraMap h x).symm) δ).symm

theorem separable_charpoly_nrmL_locEl : CjEx → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) (δ : GL (Fin n) E), polE δ ∈ Ell E n →
    (nrmL n w (locEl n w δ)).val.charpoly.Separable := by
  intro _ E _ _ _ n w δ hδ
  rw [nrmL_locEl]
  have e : (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) (δ * thE E n δ)).val =
      (δ * thE E n δ).val.map (algebraMap E (w.adicCompletion E)) := rfl
  rw [e, Matrix.charpoly_map]
  exact Polynomial.Separable.map hδ.2.2.1

end GlobalTheory.CompanionTheory.SepLocEl

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenCellJacquetIntegralVolumeStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib GlobalTheory.CompanionTheory.Rodier
open scoped TensorProduct
namespace GlobalTheory.CompanionTheory.Rodier.RadInt
open MeasureTheory
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {h N : ℕ} {d : Fin h → ℕ} {hd : ∑ a, d a = N}
variable {W : Type} [AddCommGroup W] [Module ℂ W] {ρ : Representation ℂ (Levi k fun a => Fin (d a)) W}
variable [MeasurableSpace (unipU k d hd)] [BorelSpace (unipU k d hd)]
private theorem phi_levi_current (ψ : AddChar k Circle) (f f' : IndSp (stdBlocks d hd) ρ) (a : GL (Fin N) k)
    (ha : a ∈ unipL k d hd) (m : unipM k d)
    (hm : pm k (wOpen d hd) * a * (pm k (wOpen d hd))⁻¹ = leviEmb k (stdBlocks d hd) m.1)
    (hf' : f' = parInd (stdBlocks d hd) ρ a f) :
    phi ψ f' = fun x => ρ m.1 (phi ψ f (conjU a⁻¹ (inv_mem (unipL_le ha)) x)) := by
  subst hf'
  funext x
  have e1 : pm k (wOpen d hd) * x.1 * a = leviEmb k (stdBlocks d hd) m.1 *
      (pm k (wOpen d hd) * (conjU (d := d) (hd := hd) a⁻¹ (inv_mem (unipL_le ha)) x).1) := by
    rw [← hm]
    show _ = pm k (wOpen d hd) * a * (pm k (wOpen d hd))⁻¹ * (pm k (wOpen d hd) * (a⁻¹ * x.1 * a⁻¹⁻¹))
    group
  have e2 := parInd_law (stdBlocks d hd) ρ f
    ⟨leviEmb k (stdBlocks d hd) m.1, leviEmb_mem_parab k (stdBlocks d hd) m.1⟩
    (pm k (wOpen d hd) * (conjU (d := d) (hd := hd) a⁻¹ (inv_mem (unipL_le ha)) x).1)
  rw [leviProj_leviEmb, deltaHalf_unipM m, Units.val_one, one_smul] at e2
  show (((thetaU ψ x)⁻¹ : ℂˣ) : ℂ) • (parInd (stdBlocks d hd) ρ a f).1.1 (pm k (wOpen d hd) * x.1) =
    ρ m.1 ((((thetaU ψ (conjU a⁻¹ (inv_mem (unipL_le ha)) x))⁻¹ : ℂˣ) : ℂ) •
      f.1.1 (pm k (wOpen d hd) * (conjU (d := d) (hd := hd) a⁻¹ (inv_mem (unipL_le ha)) x).1))
  rw [parInd_apply, e1, thetaU_conjU, map_smul]
  exact congrArg _ e2

private theorem radInt_levi_current {ψ : AddChar k Circle} (hψ : Continuous ψ) (hρ : IsSmooth ρ) (μ : Measure (unipU k d hd))
    [μ.IsHaarMeasure] (a : GL (Fin N) k) (ha : a ∈ unipL k d hd) (m : unipM k d)
    (hm : pm k (wOpen d hd) * a * (pm k (wOpen d hd))⁻¹ = leviEmb k (stdBlocks d hd) m.1)
    (f f' : openFns d hd ρ) (hf : (f' : IndSp (stdBlocks d hd) ρ) = parInd (stdBlocks d hd) ρ a f) :
    radInt hψ hρ μ f' = ρ m.1 (radInt hψ hρ μ f) := by
  have key := smInt_comp μ (ρ m.1) (conjU a⁻¹ (inv_mem (unipL_le ha))) (phi ψ f.1)
    (measurePreserving_conjU μ _ _) (isLocallyConstant_phi hψ _) (hasCompactSupport_phi ψ hρ _ f.2)
  show smInt μ (phi ψ f'.1) = _
  rw [phi_levi_current ψ f.1 f'.1 a ha m hm hf, key]
  rfl

end GlobalTheory.CompanionTheory.Rodier.RadInt

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.open_cell_jacquet_integral_volume : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ∀ (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Levi k fun a => Fin (d a)) W), IsSmooth ρ → ∃ (J : openFns d hd ρ →ₗ[ℂ] W) (vol : Subgroup (GL (Fin N) k) → ℝ), (∀ (u : GL (Fin N) k) (hu : u ∈ unipU k d hd) (hb : u ∈ unipB k (Fin N)) (f f' : openFns d hd ρ), (f' : IndSp (stdBlocks d hd) ρ) = parInd (stdBlocks d hd) ρ u f → J f' = (whitChar ψ N ⟨u, hb⟩ : ℂ) • J f) ∧ (∀ (a : GL (Fin N) k) (ha : a ∈ unipL k d hd) (m : unipM k d), pm k (wOpen d hd) * a * (pm k (wOpen d hd))⁻¹ = leviEmb k (stdBlocks d hd) m.1 → ∀ f f' : openFns d hd ρ, (f' : IndSp (stdBlocks d hd) ρ) = parInd (stdBlocks d hd) ρ a f → J f' = ρ m.1 (J f)) ∧ ∀ L₀ : Subgroup (GL (Fin N) k), L₀ ≤ unipU k d hd → IsCompact (L₀ : Set (GL (Fin N) k)) → (∃ O : Set (GL (Fin N) k), IsOpen O ∧ O ∩ (unipU k d hd : Set (GL (Fin N) k)) = L₀) → 0 < vol L₀ ∧ ∀ (f : openFns d hd ρ) (v : W), (∀ (u : GL (Fin N) k) (hb : u ∈ unipB k (Fin N)), u ∈ L₀ → f.1.1.1 (pm k (wOpen d hd) * u) = (whitChar ψ N ⟨u, hb⟩ : ℂ) • v) → (∀ u ∈ unipU k d hd, u ∉ L₀ → f.1.1.1 (pm k (wOpen d hd) * u) = 0) → J f = (vol L₀ : ℂ) • v := by
  intro k _ _ _ _ ψ hψ h N d hd W _ _ ρ hρ
  letI : MeasurableSpace (unipU k d hd) := borel _
  haveI : BorelSpace (unipU k d hd) := ⟨rfl⟩
  haveI : LocallyCompactSpace (unipU k d hd) :=
    (RadInt.isClosed_unipU (k := k) (d := d) (hd := hd)).isClosedEmbedding_subtypeVal.locallyCompactSpace
  let μ : MeasureTheory.Measure (unipU k d hd) := MeasureTheory.Measure.haar
  exact ⟨RadInt.radInt hψ hρ μ, RadInt.volU μ,
    fun u hu hb f f' hf => RadInt.radInt_right hψ hρ μ u hu hb f f' hf,
    fun a ha m hm f f' hf => RadInt.radInt_levi_current hψ hρ μ a ha m hm f f' hf,
    fun L₀ h1 h2 h3 => RadInt.radInt_indicator hψ hρ μ L₀ h1 h2 h3⟩
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PointIdealHorizontalIffCharZero
section
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict
open GlobalTheory

namespace GlobalTheory.CompanionTheory.MPDict

private theorem C_mem_ptIdeal_iff_intCast_residueField_eq_zero (m : ℕ) (n : Fin (m + 1) → ℕ) (x : MP ℤ m n) (c : ℤ) :
    (MvPolynomial.C c : Geo.MRing (Bk n)) ∈ ptIdeal x ↔ ((c : ℤ) : (MP ℤ m n).residueField x) = 0 := by
  rw [ptIdeal, Geo.mCoordIdeal, RingHom.mem_ker, Geo.mConeMap, MvPolynomial.aeval_C, eq_intCast,
    ← map_intCast (MvPolynomial.C : (MP ℤ m n).residueField x →+* MvPolynomial (Fin (m + 1)) ((MP ℤ m n).residueField x)) c,
    MvPolynomial.C_eq_zero]

theorem ptIdeal_isHorizontal_iff (m : ℕ) (n : Fin (m + 1) → ℕ) (x : MP ℤ m n) :
    Geo.IsHorizontal (ptIdeal x) ↔ CharZero ((MP ℤ m n).residueField x) := by
  constructor
  · intro h
    have h' : (ptIdeal x).comap (MvPolynomial.C : ℤ →+* Geo.MRing (Bk n)) = ⊥ := h
    refine charZero_of_inj_zero fun k hk => ?_
    have hm : ((k : ℤ)) ∈ (ptIdeal x).comap (MvPolynomial.C : ℤ →+* Geo.MRing (Bk n)) := by
      rw [Ideal.mem_comap, C_mem_ptIdeal_iff_intCast_residueField_eq_zero]
      exact_mod_cast hk
    rw [h', Ideal.mem_bot] at hm
    exact_mod_cast hm
  · intro h
    show (ptIdeal x).comap (MvPolynomial.C : ℤ →+* Geo.MRing (Bk n)) = ⊥
    rw [eq_bot_iff]
    intro c hc
    rw [Ideal.mem_bot]
    rw [Ideal.mem_comap, C_mem_ptIdeal_iff_intCast_residueField_eq_zero] at hc
    exact Int.cast_eq_zero.mp hc

end GlobalTheory.CompanionTheory.MPDict
end
end

