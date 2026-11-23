module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0268
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH
public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0014
public import Formalism.SharpRestriction.CuspSpanNormBounds.KappaEndpoints
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.Bundle0006

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TransportRealPointsBijectiveMultiplicative
section
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.PoincareInHH.PoincareSetting GlobalTheory.CovDom
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CovDom.RealPts

theorem jm_mul_self {n : ℕ} (ε : Fin n → Bool) : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := by
  unfold Formalism.REAL.Jm
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  split_ifs <;> norm_num

def mkUJc {n : ℕ} (ε : Fin n → Bool) (A : Matrix (Fin n) (Fin n) ℂ)
    (h : Aᴴ * Formalism.REAL.Jm ε * A = Formalism.REAL.Jm ε) : Formalism.REAL.UJ ε :=
  ⟨⟨A, Formalism.REAL.Jm ε * Aᴴ * Formalism.REAL.Jm ε,
    by
      rw [mul_eq_one_comm]
      rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Aᴴ, h, jm_mul_self],
    by rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Aᴴ, h, jm_mul_self]⟩, h⟩

theorem uMat_mkUJc {n : ℕ} (ε : Fin n → Bool) (A : Matrix (Fin n) (Fin n) ℂ)
    (h : Aᴴ * Formalism.REAL.Jm ε * A = Formalism.REAL.Jm ε) : Formalism.MainNotions.S.uMat (mkUJc ε A h) = A := rfl

theorem hpk_star (k r : ℕ) : (Formalism.QuantumDeterminants.Hpk k r).map star = Formalism.QuantumDeterminants.Hpk k r := by
  ext i j
  simp only [Matrix.map_apply]
  unfold Formalism.QuantumDeterminants.Hpk
  split_ifs <;> simp

theorem tauOf_spec (D : D7) (w : InfinitePlace D.host.E) : InfinitePlace.mk (embS D (tauOf D w)) = w := by
  unfold tauOf
  exact (GlobalTheory.RealPlaces.existsUnique_place D w).exists.choose_spec

theorem tauOf_mk (D : D7) (τ : D.what₂.Tau) : tauOf D (InfinitePlace.mk (embS D τ)) = τ :=
  (GlobalTheory.RealPlaces.existsUnique_place D _).unique (tauOf_spec D _) rfl

theorem cjw_cjw (D : D7) (w : InfinitePlace D.host.E) (M : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS) :
    cjw D w (cjw D w M) = M := by
  unfold cjw
  split_ifs with h
  · rfl
  · funext i j
    simp

theorem cjw_injective (D : D7) (w : InfinitePlace D.host.E) : Function.Injective (cjw D w) := by
  intro M N hMN
  rw [← cjw_cjw D w M, hMN, cjw_cjw]

theorem of_cjw_mul (D : D7) (w : InfinitePlace D.host.E) (A B : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS) :
    Matrix.of (cjw D w (Matrix.of.symm (Matrix.of A * Matrix.of B))) =
      Matrix.of (cjw D w A) * Matrix.of (cjw D w B) := by
  unfold cjw
  split_ifs with h
  · ext i j
    rfl
  · ext i j
    simp [Matrix.mul_apply, star_sum]

private theorem hpk_apply_of_outer_index (k r : ℕ) (i j : Fin (2 * r + k + 1)) :
    star (Formalism.QuantumDeterminants.Hpk k r i j) = Formalism.QuantumDeterminants.Hpk k r i j := by
  have e := congrFun (congrFun (hpk_star k r) i) j
  simpa only [Matrix.map_apply] using e

theorem cjw_mem (D : D7) (w : InfinitePlace D.host.E) (M : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)
    (hM : Matrix.of M ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)) :
    Matrix.of (cjw D w M) ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS) := by
  unfold cjw
  split_ifs with h
  · exact hM
  · simp only [Formalism.QuantumDeterminants.UH, Set.mem_setOf_eq] at hM ⊢
    have e : (Matrix.of fun i j => star (M i j))ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * (Matrix.of fun i j => star (M i j))
        = ((Matrix.of M)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * Matrix.of M).map star := by
      ext i j
      simp only [Matrix.map_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, star_sum,
        star_mul', star_star, hpk_apply_of_outer_index]
    rw [e, hM, hpk_star]

end GlobalTheory.CovDom.RealPts

namespace GlobalTheory.CovDom.RealPts

theorem trX_of {D : D7} (X : HidaSetting D) {θ : ℝ} (C : Choice X θ) (g : X.B.I.Ginf) (τ : D.what₂.Tau) :
    Matrix.of (trX X C g τ) = C.Qi τ * Formalism.MainNotions.S.uMat (g (vOf X τ)) * C.Q τ := rfl

private theorem of_trX_mul_eq_mul {D : D7} (X : HidaSetting D) {θ : ℝ} (C : Choice X θ) (s g : X.B.I.Ginf)
    (τ : D.what₂.Tau) :
    Matrix.of (trX X C (s * g) τ) = Matrix.of (trX X C s τ) * Matrix.of (trX X C g τ) := by
  have hQ : C.Q τ * C.Qi τ = 1 := (C.isT τ).2.1
  rw [trX_of, trX_of, trX_of]
  simp only [Pi.mul_apply, Formalism.MainNotions.S.uMat, Subgroup.coe_mul, Units.val_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (C.Q τ) (C.Qi τ), hQ, Matrix.one_mul]

private theorem eq_of_mul_mul_eq_of_det_ne_zero {n m : ℕ} (Q : Matrix (Fin n) (Fin m) ℂ) (Qi : Matrix (Fin m) (Fin n) ℂ)
    (hQ : Q * Qi = 1) (A : Matrix (Fin n) (Fin n) ℂ) : Q * (Qi * A * Q) * Qi = A := by
  simp only [← Matrix.mul_assoc, hQ, Matrix.one_mul]
  rw [Matrix.mul_assoc, hQ, Matrix.mul_one]

private theorem hcompl_unit_property_of_isPrime {n m : ℕ} (J : Matrix (Fin n) (Fin n) ℂ) (H N : Matrix (Fin m) (Fin m) ℂ)
    (Q : Matrix (Fin n) (Fin m) ℂ) (Qi : Matrix (Fin m) (Fin n) ℂ)
    (hQ : Q * Qi = 1) (hJ : Qᴴ * J * Q = H) (hN : Nᴴ * H * N = H) :
    (Q * N * Qi)ᴴ * J * (Q * N * Qi) = J := by
  have e : (Q * N * Qi)ᴴ * J * (Q * N * Qi) = Qiᴴ * (Nᴴ * (Qᴴ * J * Q) * N) * Qi := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  have e' : (Q * Qi)ᴴ * J * (Q * Qi) = Qiᴴ * (Qᴴ * J * Q) * Qi := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [e, hJ, hN, ← hJ, ← e', hQ]
  simp

end GlobalTheory.CovDom.RealPts

namespace GlobalTheory.CovDom

open GlobalTheory.CovDom.RealPts

theorem transport_real_points : ∀ (D : D7) (X : HidaSetting D) (θ : ℝ) (C : Choice X θ),
    (∀ x : InfinitePlace D.host.E → Formalism.QuantumDeterminants.Mt D.R.k D.R.rS, (∀ w, Matrix.of (x w) ∈ Formalism.QuantumDeterminants.Nset D.R.k D.R.rS) →
      ∃ g : X.B.I.Ginf, Gm D (trX X C g) = x) ∧
    Function.Injective (fun g : X.B.I.Ginf => Gm D (trX X C g)) ∧
    ∀ (s g : X.B.I.Ginf) (w : InfinitePlace D.host.E),
      Matrix.of (Gm D (trX X C (s * g)) w) = Matrix.of (Gm D (trX X C s) w) * Matrix.of (Gm D (trX X C g) w) := by
  intro D X θ C
  refine ⟨?_, ?_, ?_⟩
  ·
    intro x hx
    have hM : ∀ τ, Matrix.of (cjw D (InfinitePlace.mk (embS D τ)) (x (InfinitePlace.mk (embS D τ)))) ∈
        Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS) :=
      fun τ => cjw_mem D _ _ (hx _).1
    have hU : ∀ v, (C.Q (X.pl v) * Matrix.of (cjw D (InfinitePlace.mk (embS D (X.pl v)))
          (x (InfinitePlace.mk (embS D (X.pl v))))) * C.Qi (X.pl v))ᴴ * Formalism.REAL.Jm (X.B.I.ε v) *
        (C.Q (X.pl v) * Matrix.of (cjw D (InfinitePlace.mk (embS D (X.pl v)))
          (x (InfinitePlace.mk (embS D (X.pl v))))) * C.Qi (X.pl v)) = Formalism.REAL.Jm (X.B.I.ε v) := by
      intro v
      have hT := C.isT (X.pl v)
      simp only [IsTranspC, vOf, Equiv.symm_apply_apply] at hT
      exact hcompl_unit_property_of_isPrime _ _ _ _ _ hT.2.1 hT.2.2.1 (hM _)
    refine ⟨fun v => mkUJc (X.B.I.ε v) _ (hU v), ?_⟩
    have key : ∀ τ, trX X C (fun v => mkUJc (X.B.I.ε v) _ (hU v)) τ =
        cjw D (InfinitePlace.mk (embS D τ)) (x (InfinitePlace.mk (embS D τ))) := by
      intro τ
      apply Matrix.of.injective
      have hQi : C.Qi τ * C.Q τ = 1 := (C.isT τ).1
      simp only [trX_of, uMat_mkUJc, vOf, Equiv.apply_symm_apply]
      exact eq_of_mul_mul_eq_of_det_ne_zero (C.Qi τ) (C.Q τ) hQi _
    funext w
    simp only [Gm, key, tauOf_spec, cjw_cjw]
  ·
    intro s g hsg
    funext v
    obtain ⟨τ, rfl⟩ : ∃ τ, vOf X τ = v := ⟨X.pl v, X.pl.symm_apply_apply v⟩
    have hw := congrFun hsg (InfinitePlace.mk (embS D τ))
    simp only [Gm, tauOf_mk] at hw
    have h2 := congrArg Matrix.of (cjw_injective D _ hw)
    rw [trX_of, trX_of] at h2
    have h3 := congrArg (fun N => C.Q τ * N * C.Qi τ) h2
    simp only [eq_of_mul_mul_eq_of_det_ne_zero (C.Q τ) (C.Qi τ) (C.isT τ).2.1] at h3
    exact Subtype.ext (Units.ext h3)
  ·
    intro s g w
    simp only [Gm]
    rw [← of_cjw_mul, ← of_trX_mul_eq_mul, Equiv.symm_apply_apply]

end GlobalTheory.CovDom
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnipotentRightChangeMovesFlagComplement
section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.UnipRight

theorem Xflag_eq_Xsp {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T : E}
    (F : LFlag S r T) {j : ℕ} (hj : r ≤ j) : Xflag F j = Xsp F := by
  show Submodule.span E (F.fl.e '' {i | i.1 < j}) = Submodule.span E (Set.range F.fl.e)
  congr 1
  ext v
  simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_range]
  exact ⟨fun ⟨i, _, h⟩ => ⟨i, h⟩, fun ⟨i, h⟩ => ⟨i, lt_of_lt_of_le i.2 hj, h⟩⟩

theorem map_Xsp_NRat {D : D7} {T : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) (n : GV D) (hn : n ∈ NRat F) :
    (Xsp F).map (n : (VS D).V →ₗ[D.host.E] (VS D).V) = Xsp F := by
  have hle : (Xsp F).map (n : (VS D).V →ₗ[D.host.E] (VS D).V) ≤ Xsp F := by
    rintro _ ⟨x, hx, rfl⟩
    have h1 : x ∈ Xflag F (D.R.rS + 1) := by rw [Xflag_eq_Xsp F (by omega)]; exact hx
    have h2 := hn.2.1 D.R.rS x h1
    rw [Xflag_eq_Xsp F le_rfl] at h2
    have := (Xsp F).add_mem h2 hx
    simpa using this
  haveI : FiniteDimensional D.host.E (Xsp F) :=
    FiniteDimensional.span_of_finite _ (Set.finite_range _)
  exact Submodule.eq_of_le_of_finrank_eq hle
    (LinearEquiv.finrank_map_eq n (Xsp F))

theorem Xsp_mapLF' {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T : E}
    (γ : S.V ≃ₗ[E] S.V) (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (F : LFlag S r T) :
    Xsp (mapLF γ F) = (Xsp F).map (γ : S.V →ₗ[E] S.V) := by
  unfold mapLF
  rw [dite_eq_left hγ]
  show Submodule.span E (Set.range fun a => γ (F.fl.e a)) =
    (Submodule.span E (Set.range F.fl.e)).map (γ : S.V →ₗ[E] S.V)
  rw [Submodule.map_span, ← Set.range_comp]
  rfl

theorem unip_right : ∀ (D : D7) (T' : D.host.E) (F' : LFlag (D.sp.Y 0) D.R.rS T') (γ₁ γ₂ m n' : GV D),
    γ₁ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT → m ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT → n' ∈ NRat F' → γ₂ = m * γ₁ * n' →
      ∀ x' ∈ orth (VS D) (Xsp (mapLF γ₁ F')), m x' - (γ₂ * γ₁⁻¹) x' ∈ Xsp (mapLF γ₂ F') := by
  intro D T' F' γ₁ γ₂ m n' h1 hm hn hγ x' hx'
  have h2 : γ₂ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := by
    rw [hγ]; exact (Formalism.HermitianLatticesTheory.isom _).mul_mem ((Formalism.HermitianLatticesTheory.isom _).mul_mem hm h1) hn.1
  set y := γ₁.symm x' with hy
  have hyo : y ∈ orth (VS D) (Xsp F') := by
    simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker] at hx' ⊢
    intro z hz
    have hz' : γ₁ z ∈ Xsp (mapLF γ₁ F') := by
      rw [Xsp_mapLF' γ₁ h1]; exact ⟨z, hz, rfl⟩
    have := hx' (γ₁ z) hz'
    rw [← h1 z y, hy]
    simpa using this
  have hd : n' y - y ∈ Xsp F' := hn.2.2 y hyo
  have hd' : y - n' y ∈ Xsp F' := by
    have := (Xsp F').neg_mem hd; simpa using this
  rw [← map_Xsp_NRat F' n' hn] at hd'
  obtain ⟨w, hw, hwe⟩ := hd'
  rw [Xsp_mapLF' γ₂ h2]
  refine ⟨w, hw, ?_⟩
  have hx'y : x' = γ₁ y := by simp [hy]
  show γ₂ w = m x' - (γ₂ * γ₁⁻¹) x'
  rw [hγ, hx'y]
  simp only [LinearEquiv.mul_apply]
  have hinv : γ₁⁻¹ (γ₁ y) = y := by
    show γ₁.symm (γ₁ y) = y
    simp
  have hwe' : n' w = y - n' y := hwe
  rw [hinv, hwe', map_sub, map_sub]

end GlobalTheory.UnipRight
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryHostFieldArithmeticConditionsProof
section
noncomputable section
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

namespace GlobalTheory.TypeAsm.HostArith

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7)

theorem places : GlobalTheory.DegVol.IsPlaces (embS D) := by
  have := D.host.toHostAx.isCMField_hostE
  have : IsGalois ℚ D.host.E := D.host.toHostAx.hostE_isGalois
  have hcc : ∀ g : D.R.GG, (D.R.toFrame.cc * g).1.2 = - g.1.2 := by
    intro g
    simp [Formalism.HC.Frame.cc, Formalism.FrobeniusOrbits.c0]
  have hemb : ∀ (τ : D.what₂.Tau) (x : D.host.E),
      embS D τ x = D.host.φ₀ (D.host.gal.symm (D.eTau τ : D.R.GG) x) := fun _ _ => rfl
  have hconj : ∀ y : D.host.E, D.host.φ₀ (D.host.conj y) = starRingEnd ℂ (D.host.φ₀ y) :=
    fun y => D.host.toHostAx.conjE_apply _ y
  refine ⟨fun τ a => D.sp.cm.cmUnram.2.1 _ a, fun w => ?_⟩

  have key : ∀ τ₁ τ₂ : D.what₂.Tau, NumberField.InfinitePlace.mk (embS D τ₁) =
      NumberField.InfinitePlace.mk (embS D τ₂) → τ₁ = τ₂ := by
    intro τ₁ τ₂ h
    rw [NumberField.InfinitePlace.mk_eq_iff] at h
    have h1 := (D.eTau τ₁).2
    have h2 := (D.eTau τ₂).2
    rw [Formalism.HC.Frame.mem_Psi_iff] at h1 h2
    apply D.eTau.injective
    apply Subtype.ext
    apply D.host.gal.symm.injective
    rcases h with h | h
    · ext x
      apply D.host.φ₀.injective
      have := DFunLike.congr_fun h x
      rwa [hemb, hemb] at this
    · exfalso
      have heq : D.host.conj * D.host.gal.symm (D.eTau τ₁ : D.R.GG) =
          D.host.gal.symm (D.eTau τ₂ : D.R.GG) := by
        ext x
        apply D.host.φ₀.injective
        have := DFunLike.congr_fun h x
        rw [NumberField.ComplexEmbedding.conjugate_coe_eq, hemb, hemb] at this
        rw [AlgEquiv.mul_apply, hconj]
        exact this
      have h3 := congrArg (fun g : D.R.GG => g.1.2) (congrArg D.host.gal heq)
      simp only [map_mul, MulEquiv.apply_symm_apply] at h3
      rw [show D.host.gal D.host.conj = D.R.toFrame.cc from D.host.gal.apply_symm_apply _,
        hcc, h1, h2] at h3
      exact absurd h3 (by decide)

  obtain ⟨σ, hσ⟩ := NumberField.ComplexEmbedding.exists_comp_symm_eq_of_comp_eq (k := ℚ)
    D.host.φ₀ w.embedding (Subsingleton.elim _ _)
  have hwρ : ∀ x, D.host.φ₀ (σ.symm x) = w.embedding x := fun x => by rw [← hσ]; rfl
  have hex : ∃ τ : D.what₂.Tau, NumberField.InfinitePlace.mk (embS D τ) = w := by
    by_cases hgP : D.host.gal σ.symm ∈ D.R.Psi
    · refine ⟨D.eTau.symm ⟨_, hgP⟩, ?_⟩
      have : embS D (D.eTau.symm ⟨_, hgP⟩) = w.embedding := by
        ext x
        rw [hemb, Equiv.apply_symm_apply]
        simp only [MulEquiv.symm_apply_apply]
        exact hwρ x
      rw [this, NumberField.InfinitePlace.mk_embedding]
    · have hg' : D.R.toFrame.cc * D.host.gal σ.symm ∈ D.R.Psi := by
        rw [Formalism.HC.Frame.mem_Psi_iff] at hgP ⊢
        rw [hcc]
        rcases Int.units_eq_one_or (D.host.gal σ.symm).1.2 with h | h
        · exact absurd h hgP
        · rw [h, neg_neg]
      refine ⟨D.eTau.symm ⟨_, hg'⟩, ?_⟩
      have : embS D (D.eTau.symm ⟨_, hg'⟩) = NumberField.ComplexEmbedding.conjugate w.embedding := by
        ext x
        rw [hemb, Equiv.apply_symm_apply, NumberField.ComplexEmbedding.conjugate_coe_eq]
        simp only [map_mul, MulEquiv.symm_apply_apply, AlgEquiv.mul_apply]
        rw [show D.host.gal.symm D.R.toFrame.cc = D.host.conj from rfl, hconj, hwρ]
      rw [this, NumberField.InfinitePlace.mk_conjugate_eq, NumberField.InfinitePlace.mk_embedding]
  obtain ⟨τ, hτ⟩ := hex
  exact ⟨τ, hτ, fun τ' hτ' => key τ' τ (hτ'.trans hτ.symm)⟩

theorem finrank_eq : Module.finrank ℚ D.host.E = 2 * D.R.f := by
  rw [D.host.toHostAx.finrank_cmField]
  simp only [Formalism.BasicNotions.Ranks.f, Formalism.BasicNotions.Ranks.n]
  ring

theorem fDeg_eq : Formalism.HermitianLatticesTheory.fDeg D.host.E = D.R.f := by
  have := D.host.toHostAx.isCMField_hostE
  have h1 := NumberField.IsTotallyComplex.finrank (K := D.host.E)
  have h2 := GlobalTheory.TypeAsm.HostArith.finrank_eq D
  unfold Formalism.HermitianLatticesTheory.fDeg
  rw [NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    NumberField.IsTotallyComplex.nrRealPlaces_eq_zero, zero_add]
  omega

end GlobalTheory.TypeAsm.HostArith

namespace GlobalTheory.TypeAsm.HostArith

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7)

theorem vInv_eq : Formalism.HermitianLatticesTheory.vInv D.host.E = D.host.v := by
  have h1 := GlobalTheory.TypeAsm.HostArith.fDeg_eq D
  have h2 := GlobalTheory.TypeAsm.HostArith.finrank_eq D
  unfold Formalism.HermitianLatticesTheory.vInv Formalism.BasicNotions.Host.v Formalism.BasicNotions.Host.rdE
  rw [h1, h2]
  push_cast
  rfl

theorem finrank_O : Module.finrank (𝓞 D.host.F) (𝓞 D.host.E) = 2 := by
  have := D.host.toHostAx.isCMField_hostE
  rw [← IsFractionRing.finrank_eq (𝓞 D.host.F) D.host.F (𝓞 D.host.E) D.host.E]
  exact Algebra.IsQuadraticExtension.finrank_eq_two _ _

private theorem absNorm_dI_eq_abs_discr_of_discr_eq_sq (hd : NumberField.discr D.host.E = NumberField.discr D.host.F ^ 2) :
    (Ideal.absNorm (dI D) : ℝ) = |(NumberField.discr D.host.E : ℝ)| := by
  have := D.host.toHostAx.isCMField_hostE
  unfold dI
  rw [Ideal.absNorm_algebraMap, GlobalTheory.TypeAsm.HostArith.finrank_O,
    NumberField.absNorm_differentIdeal D.host.F (𝓞 D.host.F), hd]
  push_cast
  rw [abs_pow, Nat.cast_natAbs, Int.cast_abs]

private theorem one_le_host_v : 1 ≤ D.host.v := by
  have h := D.host.toHostAx.der.rd_sq_ge
  have ho : (1 : ℝ) ≤ D.R.toFrame.ord := by exact_mod_cast D.R.toFrame.ord_pos
  have hrd : D.host.rdE = D.host.toHostRaw.rd := rfl
  have hnn : 0 ≤ D.host.rdE := by unfold Formalism.BasicNotions.Host.rdE; positivity
  rw [← hrd] at h
  unfold Formalism.BasicNotions.Host.v
  nlinarith

theorem absNorm_dI (hd : NumberField.discr D.host.E = NumberField.discr D.host.F ^ 2) :
    (Ideal.absNorm (dI D) : ℝ) = (2 * D.host.v) ^ (2 * D.R.f) := by
  rw [absNorm_dI_eq_abs_discr_of_discr_eq_sq D hd]
  have h2 := GlobalTheory.TypeAsm.HostArith.finrank_eq D
  have hf : (0 : ℝ) < ((2 * D.R.f : ℕ) : ℝ) := by
    rw [← h2]; exact_mod_cast Module.finrank_pos
  have hv : 2 * D.host.v = D.host.rdE := by unfold Formalism.BasicNotions.Host.v; ring
  rw [hv]
  unfold Formalism.BasicNotions.Host.rdE
  rw [h2, ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _), one_div,
    inv_mul_cancel₀ hf.ne', Real.rpow_one]

theorem dI_star : ∀ x ∈ dI D, ∃ y ∈ dI D, (y : D.host.E) = star (x : D.host.E) := by
  have := D.host.toHostAx.isCMField_hostE
  intro x hx

  have key : dI D ≤ Ideal.comap (NumberField.IsCMField.ringOfIntegersComplexConj D.host.E) (dI D) := by
    show Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) _ ≤ _
    rw [Ideal.map_le_iff_le_comap]
    intro i hi
    simp only [Ideal.mem_comap]
    rw [AlgEquiv.commutes]
    exact Ideal.mem_map_of_mem _ hi
  exact ⟨NumberField.IsCMField.ringOfIntegersComplexConj D.host.E x, key hx, rfl⟩

theorem dI_ne_bot (hd : NumberField.discr D.host.E = NumberField.discr D.host.F ^ 2) : dI D ≠ ⊥ := by
  intro h
  have h1 := absNorm_dI D hd
  rw [h, Ideal.absNorm_bot, Nat.cast_zero] at h1
  have hv := one_le_host_v D
  have : (0 : ℝ) < (2 * D.host.v) ^ (2 * D.R.f) := pow_pos (by linarith) _
  linarith

theorem rank_VS : Module.finrank D.host.E (VS D).V = 2 * D.R.rS + D.R.k + 1 := by
  rw [(VS D).rank_eq]
  have h := D.sp.Y_rank 0 (Nat.zero_le _)
  obtain ⟨j, hj⟩ := D.R.m_even
  have hm2 := D.R.two_le_m
  simp only [Formalism.BasicNotions.Ranks.rankY, Formalism.BasicNotions.Ranks.r, Formalism.BasicNotions.Ranks.rS] at h ⊢
  show (D.sp.Y 0).rank = _
  rw [h]
  omega

theorem two_le_gS : 2 ≤ gS D := by
  have h0 := (D.host.g_prime 0).two_le
  have h1 := (D.host.g_prime 1).two_le
  show 2 ≤ D.host.g 0 * D.host.g 1
  nlinarith

private theorem card_Tau_eq_f : Fintype.card D.what₂.Tau = D.R.f := by
  have hP := (HostArith.places D).2
  have hb : Function.Bijective (fun τ => NumberField.InfinitePlace.mk (embS D τ)) :=
    ⟨fun a b h => (hP _).unique h rfl, fun w => (hP w).exists⟩
  rw [Fintype.card_of_bijective hb]
  exact HostArith.fDeg_eq D

end GlobalTheory.TypeAsm.HostArith

namespace GlobalTheory.TypeAsm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem hostC : HostC := by
  intro D large₂ hStd
  obtain ⟨C', Cl, Cg, cb, Cw, cT, CT, C0, hK⟩ := hStd
  obtain ⟨⟨-, hD0, -⟩, -⟩ := hK
  obtain ⟨-, -, -, -, -, -, -, -, hsplit, -⟩ := hD0
  have hd : NumberField.discr D.host.E = NumberField.discr D.host.F ^ 2 := D.host.toHostAx.der.discr_sq
  exact ⟨D.sp.cm.cmUnram, HostArith.places D, HostArith.vInv_eq D, HostArith.one_le_host_v D,
    HostArith.fDeg_eq D, HostArith.card_Tau_eq_f D, HostArith.finrank_eq D, HostArith.dI_ne_bot D hd,
    HostArith.dI_star D, HostArith.absNorm_dI D hd, HostArith.rank_VS D, HostArith.two_le_gS D,
    fun u => ⟨(D.mem u).A.T_prime, (hsplit u).1⟩⟩

end GlobalTheory.TypeAsm
end
end

