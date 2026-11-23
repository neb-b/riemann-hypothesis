module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0005
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0003
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0013
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle0007
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0006

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DecompB
section
noncomputable section

open Matrix
open scoped ComplexOrder

namespace PositivityTheory.Rg.Sw.Glob.DecH

variable {n : ℕ}

theorem det_sub_I_smul_ne_zero {A B C D : Matrix (Fin n) (Fin n) ℂ} (h : InG (fromBlocks A B C D))
    (hu : IsUnit (fromBlocks A B C D).det) : (A - Complex.I • C).det ≠ 0 := by
  classical
  have hrel : Cᴴ * A = Aᴴ * C := by
    have h' := h
    unfold PositivityTheory.Rg.Sw.InG PositivityTheory.Rg.Sw.JJ at h'
    rw [fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply] at h'
    have h1 := (fromBlocks_inj.1 h').1
    simp at h1
    exact neg_add_eq_zero.1 h1
  have hM : (A - Complex.I • C)ᴴ * (A - Complex.I • C) = Aᴴ * A + Cᴴ * C := by
    simp only [conjTranspose_sub, conjTranspose_smul, Complex.star_def, Complex.conj_I,
      sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, smul_smul, hrel]
    match_scalars <;> ring_nf <;> simp [Complex.I_sq]
  intro hdet
  obtain ⟨v, hv0, hv⟩ := exists_mulVec_eq_zero_iff.2 hdet
  have hv2 : (Aᴴ * A + Cᴴ * C) *ᵥ v = 0 := by
    rw [← hM, ← mulVec_mulVec, hv, mulVec_zero]
  set V : Fin n ⊕ Fin n → ℂ := Sum.elim v 0 with hV
  set P : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ := fromBlocks A 0 C 0 with hPdef
  have hP : (Pᴴ * P) *ᵥ V = 0 := by
    rw [hPdef, fromBlocks_conjTranspose, fromBlocks_multiply]
    simp [hV, fromBlocks_mulVec, hv2]
  have hP2 := (conjTranspose_mul_self_mulVec_eq_zero _ _).1 hP
  have hg : fromBlocks A B C D *ᵥ V = 0 := by
    have := hP2
    simp [hV, hPdef, fromBlocks_mulVec] at this ⊢
    exact this
  have hV0 : V ≠ 0 := by
    intro h0
    apply hv0
    funext i
    have := congrFun h0 (Sum.inl i)
    simpa [hV] using this
  exact hu.ne_zero (exists_mulVec_eq_zero_iff.1 ⟨V, hV0, hg⟩)

theorem exists_real_det_ne_zero {A C : Matrix (Fin n) (Fin n) ℂ} (h : (A - Complex.I • C).det ≠ 0) :
    ∃ t : ℝ, (A - (t : ℂ) • C).det ≠ 0 := by
  classical
  by_contra hne
  push_neg at hne
  set p : Polynomial ℂ :=
    ((Polynomial.X : Polynomial ℂ) • (-C).map Polynomial.C + A.map Polynomial.C).det with hp
  have heval : ∀ z : ℂ, p.eval z = (A - z • C).det := by
    intro z
    rw [hp, ← Polynomial.coe_evalRingHom, RingHom.map_det]
    congr 1
    ext i j
    simp
    ring
  have hp0 : p = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply Set.Infinite.mono _ (Set.infinite_range_of_injective Complex.ofReal_injective)
    rintro _ ⟨t, rfl⟩
    rw [Set.mem_setOf_eq, Polynomial.IsRoot, heval]
    exact hne t
  apply h
  have := heval Complex.I
  rw [hp0, Polynomial.eval_zero] at this
  exact this.symm

end PositivityTheory.Rg.Sw.Glob.DecH
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DenseC
section
noncomputable section

open Matrix Topology
open scoped Matrix TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum
open GlobalTheory.StdUnn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.DenseP

open Formalism.IndefR.Eqv (psiT psiT_inclR)

variable {D : D7} {n : ℕ}

theorem denseRange_of_not_isReal' {K : Type} [Field K] (σ : K →+* ℂ)
    (h : ¬ NumberField.ComplexEmbedding.IsReal σ) : DenseRange σ := by
  have hc : IsClosed (σ.fieldRange.topologicalClosure : Set ℂ) :=
    Subfield.isClosed_topologicalClosure _
  rcases Complex.subfield_eq_of_closed hc with h1 | h1
  · exfalso
    apply h
    rw [NumberField.ComplexEmbedding.isReal_iff]
    ext x
    have hx : σ x ∈ σ.fieldRange.topologicalClosure := Subfield.le_topologicalClosure _ ⟨x, rfl⟩
    rw [h1] at hx
    obtain ⟨r, hr⟩ := hx
    rw [NumberField.ComplexEmbedding.conjugate_coe_eq, ← hr]
    exact Complex.conj_ofReal r
  · have : closure (Set.range σ) = Set.univ := by
      have := congrArg (fun S : Subfield ℂ => (S : Set ℂ)) h1
      exact this
    exact dense_iff_closure_eq.2 this

theorem tauE_not_real (τ : D.what₂.Tau) : ¬ NumberField.ComplexEmbedding.IsReal (tauE D τ) := by
  intro h
  rw [NumberField.ComplexEmbedding.isReal_iff] at h
  have h1 : starRingEnd ℂ (tauE D τ D.host.xi0) = tauE D τ D.host.xi0 := by
    have := congrArg (fun f : D.host.E →+* ℂ => f D.host.xi0) h
    simpa [NumberField.ComplexEmbedding.conjugate_coe_eq] using this
  have h2 : tauE D τ (star D.host.xi0) = starRingEnd ℂ (tauE D τ D.host.xi0) := Formalism.IndefR.Eqv.tauE_star D τ _
  rw [Formalism.IndefR.Datum.Brg.star_purely_imaginary_eq_neg, map_neg, h1] at h2
  have h3 : tauE D τ D.host.xi0 = 0 := by
    have : (2 : ℂ) * tauE D τ D.host.xi0 = 0 := by linear_combination -h2
    exact (mul_eq_zero.1 this).resolve_left two_ne_zero
  exact Formalism.IndefR.Fin.embedding_xi_zero_ne_zero ((map_eq_zero_iff _ (tauE D τ).injective).1 h3)

theorem denseRange_tauE (τ : D.what₂.Tau) : DenseRange (tauE D τ) := denseRange_of_not_isReal' _ (tauE_not_real τ)

theorem sig_apply (x : D.host.E) : D.sp.cm.sig x = star x := rfl

theorem cT_map_tauE (τ : D.what₂.Tau) {k : ℕ} (u : Matrix (Fin k) (Fin k) D.host.E) :
    (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) u).map (tauE D τ) = (u.map (tauE D τ))ᴴ := by
  ext i j
  simp [Formalism.UG.cT, Matrix.conjTranspose_apply, sig_apply, Formalism.IndefR.Eqv.tauE_star]

theorem block_matrix_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (a b c d : Matrix (Fin n) (Fin n) R) :
    (blk4 a b c d).map f = blk4 (a.map f) (b.map f) (c.map f) (d.map f) := by
  rw [blk4, blk4, ← Matrix.submatrix_map, Matrix.fromBlocks_map]

theorem map0 (τ : D.what₂.Tau) : (0 : Matrix (Fin n) (Fin n) D.host.E).map (tauE D τ) = 0 :=
  map_zero (RingHom.mapMatrix (tauE D τ))

theorem map1 (τ : D.what₂.Tau) : (1 : Matrix (Fin n) (Fin n) D.host.E).map (tauE D τ) = 1 :=
  map_one (RingHom.mapMatrix (tauE D τ))

theorem mapn1 (τ : D.what₂.Tau) : (-1 : Matrix (Fin n) (Fin n) D.host.E).map (tauE D τ) = -1 := by
  show RingHom.mapMatrix (tauE D τ) (-1) = -1
  rw [map_neg, map_one]

theorem map_smul_E (τ : D.what₂.Tau) {k : ℕ} (c : D.host.E) (X : Matrix (Fin k) (Fin k) D.host.E) :
    (c • X).map (tauE D τ) = (tauE D τ c) • X.map (tauE D τ) := by
  ext i j; simp [Matrix.map_apply, Matrix.smul_apply]

theorem Jst_map (τ : D.what₂.Tau) : (Jst D n).map (tauE D τ) = Glob.reidx (JJ n) := by
  rw [Jst, block_matrix_map, map0, map1, mapn1]
  rfl

theorem reidx_mul (a b : M2 n) : Glob.reidx (a * b) = Glob.reidx a * Glob.reidx b := by
  simp [Glob.reidx, Matrix.submatrix_mul_equiv]

theorem reidx_one : Glob.reidx (1 : M2 n) = 1 := by
  simp [Glob.reidx, Matrix.submatrix_one_equiv]

theorem reidx_conjTranspose (a : M2 n) : Glob.reidx aᴴ = (Glob.reidx a)ᴴ := by
  simp [Glob.reidx, Matrix.conjTranspose_submatrix]

theorem inG_JJc : InG (JJ n) := by
  simp only [InG, JJ, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]
  simp

theorem mat_one : mat (1 : G D n) = 1 := by simp [mat]

theorem mat_mul (g h : G D n) : mat (g * h) = mat g * mat h := by simp [mat]

theorem ratPt_of (τ : D.what₂.Tau) (u : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E) (M : M2 n) (hM : InG M)
    (hu : u.map (tauE D τ) = Glob.reidx M) : ∃ γ ∈ GF D n, (mat γ).map (psiT D τ) = Glob.reidx M := by
  have hdet : IsUnit u.det := by
    have h1 : tauE D τ u.det = M.det := by
      rw [RingHom.map_det, RingHom.mapMatrix_apply, hu, Glob.reidx, Matrix.det_submatrix_equiv_self]
    have h2 : M.det ≠ 0 := (isUnit_det_of_inG hM).ne_zero
    refine isUnit_iff_ne_zero.2 fun h0 => h2 ?_
    rw [← h1, h0, map_zero]
  let U : GL (Fin (n + n)) D.host.E := ⟨u, u⁻¹, Matrix.mul_nonsing_inv u hdet, Matrix.nonsing_inv_mul u hdet⟩
  have hU : U ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) (Jst D n) := by
    show Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) u * Jst D n * u = Jst D n
    have key : (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) u * Jst D n * u).map (tauE D τ) =
        (Jst D n).map (tauE D τ) := by
      rw [Matrix.map_mul, Matrix.map_mul, cT_map_tauE, Jst_map, hu, ← reidx_conjTranspose, ← reidx_mul, ← reidx_mul, hM]
    exact Matrix.map_injective (tauE D τ).injective key
  refine ⟨GlobalTheory.AdelicU.ratEmb D.sp.cm.sig (Jst D n) ⟨U, hU⟩, ?_, ?_⟩
  · show _ ∈ GlobalTheory.AdelicU.ratPts D.sp.cm.sig (Jst D n)
    rw [← GlobalTheory.AdelicU.range_ratEmb]; exact MonoidHom.mem_range.2 ⟨_, rfl⟩
  · show (u.map (inclR (AF D.host.F))).map (psiT D τ) = _
    rw [Matrix.map_map]
    have : (⇑(psiT D τ) ∘ ⇑(inclR (AF D.host.F))) = ⇑(tauE D τ) := funext fun e => psiT_inclR D τ e
    rw [this, hu]

def gam (D : D7) (n : ℕ) (τ : D.what₂.Tau) : Subgroup (GR n) where
  carrier := {y | ∃ γ ∈ GF D n, (mat γ).map (psiT D τ) = Glob.reidx (mR y)}
  one_mem' := ⟨1, one_mem _, by
    rw [mat_one, Matrix.map_one _ (map_zero _) (map_one _)]
    exact reidx_one.symm⟩
  mul_mem' := by
    rintro a b ⟨γ, hγ, ea⟩ ⟨γ', hγ', eb⟩
    refine ⟨γ * γ', mul_mem hγ hγ', ?_⟩
    rw [mat_mul, Matrix.map_mul, ea, eb]
    exact (reidx_mul _ _).symm
  inv_mem' := by
    rintro a ⟨γ, hγ, ea⟩
    refine ⟨γ⁻¹, inv_mem hγ, ?_⟩
    have h1 : (mat γ⁻¹).map (psiT D τ) * (mat γ).map (psiT D τ) = 1 := by
      rw [← Matrix.map_mul, ← mat_mul, inv_mul_cancel, mat_one, Matrix.map_one _ (map_zero _) (map_one _)]
    have h2 : Glob.reidx (mR a) * Glob.reidx (mR a⁻¹) = 1 := by
      rw [← reidx_mul]
      show Glob.reidx (mR (a * a⁻¹)) = 1
      rw [mul_inv_cancel]; exact reidx_one
    calc (mat γ⁻¹).map (psiT D τ) = (mat γ⁻¹).map (psiT D τ) * (Glob.reidx (mR a) * Glob.reidx (mR a⁻¹)) := by
          rw [h2, Matrix.mul_one]
      _ = Glob.reidx (mR a⁻¹) := by rw [← Matrix.mul_assoc, ← ea, h1, Matrix.one_mul]

theorem mkGR_ext {g : M2 n} (hg : InG g) {h : GR n} (e : mR h = g) : h = mkGR g hg :=
  Subtype.ext (Units.ext e)

theorem gens_mem (τ : D.what₂.Tau) (h : GR n) (hh : IsNElt h ∨ IsMElt h ∨ IsWElt h) :
    h ∈ (gam D n τ).topologicalClosure := by
  rcases hh with ⟨b, hb, e⟩ | ⟨A, hA, e⟩ | e
  · have hh : h = nuE b := by
      rw [mkGR_ext (inG_nUh (hpart_herm b)) (show mR h = nU (hpart b) by rw [hpart_of_herm hb]; exact e)]; rfl
    rw [hh]
    refine closure_mono ?_ (nuE_mem_closure (tauE D τ) (denseRange_tauE τ) b)
    rintro _ ⟨e', rfl⟩
    have hβ : ((2 : D.host.E)⁻¹ • (e' + Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) e')).map (tauE D τ) =
        hpart (e'.map (tauE D τ)) := by
      rw [map_smul_E, Matrix.map_add _ (map_add (tauE D τ)), cT_map_tauE, map_inv₀, map_ofNat, hpart, one_div]
    obtain ⟨γ, hγ, he⟩ := ratPt_of τ (blk4 1 ((2 : D.host.E)⁻¹ • (e' + Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) e')) 0 1)
      (nU (hpart (e'.map (tauE D τ)))) (inG_nUh (hpart_herm _)) (by
        rw [block_matrix_map, map0, map1, hβ]
        rfl)
    exact ⟨γ, hγ, he⟩
  · have hh : h = mlE A := by rw [mlE_of hA]; exact mkGR_ext (inG_mL hA) e
    rw [hh]
    refine closure_mono ?_ (mlE_mem_closure (tauE D τ) (denseRange_tauE τ) A hA)
    rintro _ ⟨B, ⟨hB, e', rfl⟩, rfl⟩
    have hdet : IsUnit e'.det := by
      have h1 : tauE D τ e'.det = (e'.map (tauE D τ)).det := by rw [RingHom.map_det, RingHom.mapMatrix_apply]
      refine isUnit_iff_ne_zero.2 fun h0 => (hB : IsUnit (e'.map (tauE D τ)).det).ne_zero ?_
      rw [← h1, h0, map_zero]
    have hcd : IsUnit (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) e').det := by
      have h1 : tauE D τ (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) e').det = ((e'.map (tauE D τ))ᴴ).det := by
        rw [RingHom.map_det, RingHom.mapMatrix_apply, cT_map_tauE]
      refine isUnit_iff_ne_zero.2 fun h0 => ?_
      have : ((e'.map (tauE D τ))ᴴ).det = 0 := by rw [← h1, h0, map_zero]
      rw [Matrix.det_conjTranspose, star_eq_zero] at this
      exact (hB : IsUnit (e'.map (tauE D τ)).det).ne_zero this
    have hinv : ((Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) e')⁻¹).map (tauE D τ) =
        ((e'.map (tauE D τ))⁻¹)ᴴ := by
      rw [Matrix.conjTranspose_nonsing_inv, ← cT_map_tauE]
      refine (Matrix.inv_eq_right_inv ?_).symm
      rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ hcd, Matrix.map_one _ (map_zero _) (map_one _)]
    obtain ⟨γ, hγ, he⟩ := ratPt_of τ (blk4 e' 0 0 (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) e')⁻¹)
      (fromBlocks (e'.map (tauE D τ)) 0 0 ((e'.map (tauE D τ))⁻¹)ᴴ) (inG_mL hB) (by
        rw [block_matrix_map, hinv, map0]
        rfl)
    refine ⟨γ, hγ, ?_⟩
    rw [he, mlE_of hB]
    rfl
  · refine (gam D n τ).le_topologicalClosure ?_
    obtain ⟨γ, hγ, he⟩ := ratPt_of τ (Jst D n) (JJ n) inG_JJc (Jst_map τ)
    exact ⟨γ, hγ, by rw [he, e]⟩

theorem gam_dense (hgen : GenSt) (τ : D.what₂.Tau) (g : GR n) : g ∈ closure (gam D n τ : Set (GR n)) := by
  have h1 : Subgroup.closure {h : GR n | IsNElt h ∨ IsMElt h ∨ IsWElt h} ≤ (gam D n τ).topologicalClosure :=
    (Subgroup.closure_le _).2 fun h hh => gens_mem τ h hh
  exact h1 (hgen n g)

end PositivityTheory.Rg.Sw.Glob.DenseP
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DerivOne
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

variable {D : D7} {n : ℕ}

def DX (θ : InfFam D) (V : HSp D) (τ : D.what₂.Tau) (fr X : Matrix (Fin V.rank) (Fin V.rank) ℂ) (Φ : Mx D V.rank n → ℂ)
    (x : Mx D V.rank n) : ℂ :=
  deriv (fun t : ℝ => Φ (HMul.hMul (mt V (atTau θ V τ (fr * NormedSpace.exp ((t : ℂ) • X) * fr⁻¹))) x)) 0

def LieComm : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν τ ε fr ι, Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι → ∀ Ψ ∈ awayA θ V n l s τ,
    ∀ X : Matrix (Fin V.rank) (Fin V.rank) ℂ, IsUe ε X → ∀ (P : PX V.rank n) (g : G D n) (x : Mx D V.rank n),
      (ω g (phiS θ τ fr (cLoc l τ) Ψ (vfX (cLoc l τ) X P))).1 x = DX θ V τ fr X (ω g (phiS θ τ fr (cLoc l τ) Ψ P)).1 x

def DerivOne : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν τ ε fr ι, Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι →
    ∀ X : Matrix (Fin V.rank) (Fin V.rank) ℂ, IsUe ε X → ∀ Θ Θ' : schwartzA θ V.rank n,
      (∀ x, Θ'.1 x = DX θ V τ fr X Θ.1 x) → thetaInt ω ν Θ' 1 = 0

end PositivityTheory.Rg.Sw.Glob
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocFactPf
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

theorem locFact_of (hD : Decomp) (hG : OpGen) : LocFact := by
  intro D n V ψ χ θ μ ω H l s ν τ ε fr ι hC
  have hop : ∀ y : GR n, ((∃ b : Matrix (Fin n) (Fin n) ℂ, bᴴ = b ∧ mR y = nU b) ∨
      (∃ c : Matrix (Fin n) (Fin n) ℂ, cᴴ = c ∧ mR y = nbar c) ∨
      (∃ a : Matrix (Fin n) (Fin n) ℂ, IsUnit a.det ∧ mR y = mM a)) →
    ∃ L : ((Fin V.rank → Fin n → ℂ) → ℂ) → ((Fin V.rank → Fin n → ℂ) → ℂ), (∀ f, IsSch f → IsSch (L f)) ∧
      ∀ Ψ (hΨ : AwayCls θ τ fr Ψ) f (hf : IsSch f),
        (ω (ι y) ⟨tens θ τ fr f Ψ, hΨ.2 f hf⟩).1 = tens θ τ fr (L f) Ψ :=
    fun y hy => hG D n V ψ χ θ μ ω H l s ν τ ε fr ι hC y hy
  choose! large₂ hLgS hLg using hop
  have hdec := fun y : GR n => hD n y
  choose y1 y2 y3 y4 hy h1 h2 h3 h4 using hdec
  have g1 : ∀ y, (∃ b : Matrix (Fin n) (Fin n) ℂ, bᴴ = b ∧ mR (y1 y) = nU b) ∨
      (∃ c : Matrix (Fin n) (Fin n) ℂ, cᴴ = c ∧ mR (y1 y) = nbar c) ∨
      (∃ a : Matrix (Fin n) (Fin n) ℂ, IsUnit a.det ∧ mR (y1 y) = mM a) := fun y => by
    obtain ⟨t, ht⟩ := h1 y
    exact Or.inl ⟨_, herm_smul_one t, ht⟩
  have g2 : ∀ y, (∃ b : Matrix (Fin n) (Fin n) ℂ, bᴴ = b ∧ mR (y2 y) = nU b) ∨
      (∃ c : Matrix (Fin n) (Fin n) ℂ, cᴴ = c ∧ mR (y2 y) = nbar c) ∨
      (∃ a : Matrix (Fin n) (Fin n) ℂ, IsUnit a.det ∧ mR (y2 y) = mM a) := fun y => Or.inr (Or.inl (h2 y))
  have g3 : ∀ y, (∃ b : Matrix (Fin n) (Fin n) ℂ, bᴴ = b ∧ mR (y3 y) = nU b) ∨
      (∃ c : Matrix (Fin n) (Fin n) ℂ, cᴴ = c ∧ mR (y3 y) = nbar c) ∨
      (∃ a : Matrix (Fin n) (Fin n) ℂ, IsUnit a.det ∧ mR (y3 y) = mM a) := fun y => Or.inr (Or.inr (h3 y))
  have g4 : ∀ y, (∃ b : Matrix (Fin n) (Fin n) ℂ, bᴴ = b ∧ mR (y4 y) = nU b) ∨
      (∃ c : Matrix (Fin n) (Fin n) ℂ, cᴴ = c ∧ mR (y4 y) = nbar c) ∨
      (∃ a : Matrix (Fin n) (Fin n) ℂ, IsUnit a.det ∧ mR (y4 y) = mM a) := fun y => Or.inl (h4 y)
  refine ⟨fun y f => large₂ (y1 y) (large₂ (y2 y) (large₂ (y3 y) (large₂ (y4 y) f))), fun y f hf => ?_, fun y Ψ hΨ f hf => ?_⟩
  · exact hLgS _ (g1 y) _ (hLgS _ (g2 y) _ (hLgS _ (g3 y) _ (hLgS _ (g4 y) _ hf)))
  · have step : ∀ (z : GR n) (hz : (∃ b : Matrix (Fin n) (Fin n) ℂ, bᴴ = b ∧ mR z = nU b) ∨
        (∃ c : Matrix (Fin n) (Fin n) ℂ, cᴴ = c ∧ mR z = nbar c) ∨
        (∃ a : Matrix (Fin n) (Fin n) ℂ, IsUnit a.det ∧ mR z = mM a)), ∀ f (hf : IsSch f)
        (h : tens θ τ fr f Ψ ∈ schwartzA θ V.rank n),
        ω (ι z) ⟨tens θ τ fr f Ψ, h⟩ = ⟨tens θ τ fr (large₂ z f) Ψ, hΨ.2 _ (hLgS z hz f hf)⟩ := by
      intro z hz f hf h
      exact Subtype.ext (hLg z hz Ψ hΨ f hf)
    have hprod : ω (ι y) = ω (ι (y1 y)) * ω (ι (y2 y)) * ω (ι (y3 y)) * ω (ι (y4 y)) := by
      conv_lhs => rw [hy y]
      simp only [map_mul]
    rw [hprod]
    simp only [Module.End.mul_apply]
    have s4 := hLgS (y4 y) (g4 y) _ hf
    have s3 := hLgS (y3 y) (g3 y) _ s4
    have s2 := hLgS (y2 y) (g2 y) _ s3
    rw [step (y4 y) (g4 y) _ hf, step (y3 y) (g3 y) _ s4, step (y2 y) (g2 y) _ s3, step (y1 y) (g1 y) _ s2]

theorem locOpEx_of_fact (hF : LocFact) (hA : AwayIn) (hS : SchFP) (hL : LNe) : LocOpEx := by
  intro D n V ψ χ θ μ ω H l s ν τ ε fr ι hC
  obtain ⟨L, -, hL2⟩ := hF D n V ψ χ θ μ ω H l s ν τ ε fr ι hC
  refine ⟨L, ?_⟩
  intro y Ψ hΨ P
  have hAw : AwayCls θ τ fr Ψ :=
    hA D n V θ l s τ ε fr hC.hθ hC.hs hC.hfr (fun τ' => hL D ψ θ l hC.hψ hC.hθ hC.hl τ') Ψ hΨ
  have hc : 0 < cLoc l τ := by
    have hne := hL D ψ θ l hC.hψ hC.hθ hC.hl τ
    unfold cLoc
    have : 0 < |l τ| := abs_pos.mpr hne
    positivity
  have hf0 : IsSch (fP (cLoc l τ) P) := hS _ _ _ hc P
  rw [phiS_eq' (hAw.2 _ hf0)]
  exact hL2 y Ψ hAw _ hf0

end PositivityTheory.Rg.Sw.Glob
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocalL2IsometryAlt
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct ComplexOrder
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

variable {D : D7} {n : ℕ}

def ftLoc {m : ℕ} (ε : Fin m → Bool) (t : ℝ) (f : (Fin m → Fin n → ℂ) → ℂ) (u : Fin m → Fin n → ℂ) : ℂ :=
  ∫ y : Fin m → Fin n → ℂ, f y *
    Complex.exp (Complex.I * ((2 * t : ℝ) : ℂ) * (((Matrix.of u)ᴴ * Matrix.diagonal (sgn ε) * Matrix.of y).trace.re : ℂ))

def FTfact : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν τ ε fr ι, Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι → ∀ w : G D n, mat w = blk4 0 1 (-1) 0 →
    ∃ (κ : ℂ) (A A' : (Mx D V.rank n → ℂ) → (Mx D V.rank n → ℂ)), κ ≠ 0 ∧ ∀ Ψ (hΨ : AwayCls θ τ fr Ψ),
      AwayCls θ τ fr (A Ψ) ∧ AwayCls θ τ fr (A' Ψ) ∧ ∀ f (hf : IsSch f),
        IsSch (fun u => κ * ftLoc ε (tLoc l τ) f u) ∧ IsSch (fun u => κ⁻¹ * ftLoc ε (-tLoc l τ) f u) ∧
        (ω w ⟨tens θ τ fr f Ψ, hΨ.2 f hf⟩).1 = tens θ τ fr (fun u => κ * ftLoc ε (tLoc l τ) f u) (A Ψ) ∧
        (ω w⁻¹ ⟨tens θ τ fr f Ψ, hΨ.2 f hf⟩).1 = tens θ τ fr (fun u => κ⁻¹ * ftLoc ε (-tLoc l τ) f u) (A' Ψ)

def GenA : Prop :=
  ∀ (D : D7) (n : ℕ), Subgroup.closure {g : G D n | (∃ b, mat g = blk4 1 b 0 1) ∨ (∃ a d, mat g = blk4 a 0 0 d) ∨
    (∃ c, mat g = blk4 1 0 c 1)} = ⊤

def LocalL2Isometry : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν τ ε fr ι, Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι → ∀ L, IsLocFact ω τ fr ι L →
    ∀ y : GR n, ∃ κ : ℝ, 0 < κ ∧ ∀ f, IsSch f → ∫ u, ‖L y f u‖ ^ 2 = κ * ∫ u, ‖f u‖ ^ 2

end PositivityTheory.Rg.Sw.Glob
end
end

