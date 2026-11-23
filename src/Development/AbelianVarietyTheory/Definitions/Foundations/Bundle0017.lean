module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
public import Development.AbelianVarietyTheory.Definitions.Foundations.MemSiegelOfIffRightAct
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.Foundations.ExistsGLSubmatrix
section
noncomputable section

namespace GlobalTheory.Doubling

open NumberField Matrix Formalism.BasicNotions Formalism.UG GlobalTheory.AdelicU

theorem mem_hdual {S K V : Type} [CommRing S] [Field K] [StarRing K] [Algebra S K] [AddCommGroup V]
    [Module K V] [Module S V] [IsScalarTower S K V] {B : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule S V} {x : V} :
    x ∈ Formalism.HermitianLatticesTheory.dual B L ↔ ∀ y ∈ L, B y x ∈ (1 : Submodule S K) := by
  simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply]

variable {E : Type} [Field E] [NumberField E] [StarRing E]

@[reducible] def hneg (V : HSpace E) : HSpace E where
  V := V.V
  hT := -V.hT
  herm := ⟨fun x y => by simp [V.herm.eq x y]⟩
  nondeg := ⟨fun x h => V.nondeg.1 x fun y => neg_eq_zero.1 (h y), fun x h => V.nondeg.2 x fun y => neg_eq_zero.1 (h y)⟩
  rank := V.rank
  rank_eq := V.rank_eq
  frame := V.frame
  sig τ := ((V.sig τ).2, (V.sig τ).1)
  L0 := V.L0
  standardTuple_isLattice := V.standardTuple_isLattice
  baseLattice_isUnimodular := by
    refine Eq.trans (Submodule.ext fun x => ?_) V.baseLattice_isUnimodular
    simp only [mem_hdual, LinearMap.neg_apply, neg_mem_iff]

theorem orthSum_apply (V W : HSpace E) (x y : V.V × W.V) :
    Formalism.E.orthSum V.hT W.hT x y = V.hT x.1 y.1 + W.hT x.2 y.2 := rfl

@[reducible] def hsum (V W : HSpace E) : HSpace E where
  V := V.V × W.V
  hT := Formalism.E.orthSum V.hT W.hT
  herm := ⟨fun x y => by rw [orthSum_apply, orthSum_apply, map_add (f := _), V.herm.eq, W.herm.eq]⟩
  nondeg := ⟨fun x h => Prod.ext (V.nondeg.1 _ fun y => by simpa [orthSum_apply] using h (y, 0))
      (W.nondeg.1 _ fun y => by simpa [orthSum_apply] using h (0, y)),
    fun x h => Prod.ext (V.nondeg.2 _ fun y => by simpa [orthSum_apply] using h (y, 0))
      (W.nondeg.2 _ fun y => by simpa [orthSum_apply] using h (0, y))⟩
  rank := V.rank + W.rank
  rank_eq := by rw [Module.finrank_prod, V.rank_eq, W.rank_eq]
  frame := (V.frame.prod W.frame).reindex finSumFinEquiv
  sig τ := V.sig τ + W.sig τ
  L0 := V.L0.prod W.L0
  standardTuple_isLattice :=
    Submodule.IsLattice.of_fg E (V.standardTuple_isLattice.fg.prod W.standardTuple_isLattice.fg)
  baseLattice_isUnimodular := Submodule.ext fun x => by
    have h1 := SetLike.ext_iff.1 V.baseLattice_isUnimodular x.1
    have h2 := SetLike.ext_iff.1 W.baseLattice_isUnimodular x.2
    rw [Submodule.mem_prod, ← h1, ← h2, mem_hdual, mem_hdual, mem_hdual]
    exact ⟨fun h => ⟨fun y hy => by simpa [orthSum_apply] using h (y, 0) ⟨hy, zero_mem _⟩,
      fun y hy => by simpa [orthSum_apply] using h (0, y) ⟨zero_mem _, hy⟩⟩,
      fun h y hy => add_mem (h.1 _ hy.1) (h.2 _ hy.2)⟩

@[reducible] def hdbl (V : HSpace E) : HSpace E := hsum V (hneg V)

theorem gram_hneg (V : HSpace E) : (hneg V).gram = -V.gram := rfl

theorem frame_hsum_inl (V W : HSpace E) (i : Fin V.rank) :
    (hsum V W).frame (finSumFinEquiv (.inl i)) = (V.frame i, 0) := by
  simp [Module.Basis.prod_apply]

theorem frame_hsum_inr (V W : HSpace E) (i : Fin W.rank) :
    (hsum V W).frame (finSumFinEquiv (.inr i)) = (0, W.frame i) := by
  simp [Module.Basis.prod_apply]

theorem gram_hsum (V W : HSpace E) : (hsum V W).gram = blkMat finSumFinEquiv V.gram W.gram := by
  ext i j
  obtain ⟨a, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨b, rfl⟩ := finSumFinEquiv.surjective j
  have key : ∀ u v, (hsum V W).hT u v = V.hT u.1 v.1 + W.hT u.2 v.2 := fun u v => orthSum_apply V W u v
  rcases a with a | a <;> rcases b with b | b <;>
    simp [HSpace.gram, blkMat, key, frame_hsum_inl, frame_hsum_inr]

theorem gram_hdbl (V : HSpace E) : (hdbl V).gram = dblGram finSumFinEquiv V.gram := by
  show (hsum V (hneg V)).gram = _
  rw [gram_hsum, gram_hneg]
  rfl

theorem sum_pairVec_frame (V W : HSpace E) (x : Fin V.rank → E) (y : Fin W.rank → E) :
    ∑ i, pairVec finSumFinEquiv x y i • (hsum V W).frame i = (∑ i, x i • V.frame i, ∑ i, y i • W.frame i) := by
  rw [← Equiv.sum_comp finSumFinEquiv, Fintype.sum_sum_type]
  simp only [pairVec_inl, pairVec_inr, frame_hsum_inl, frame_hsum_inr, Prod.smul_mk, smul_zero]
  ext <;> simp [Prod.fst_sum, Prod.snd_sum]

theorem frameLat_hsum (V W : HSpace E) : frameLat (hsum V W) = sumLat finSumFinEquiv (frameLat V) (frameLat W) := by
  ext w
  rw [mem_sumLat, mem_frameLat, mem_frameLat, mem_frameLat]
  conv_lhs => rw [← pairVec_eta finSumFinEquiv w]
  rw [sum_pairVec_frame]
  exact Submodule.mem_prod

theorem isLattice_frameLat (V : HSpace E) : Submodule.IsLattice E (frameLat V) :=
  Submodule.IsLattice.of_fg E (frameLat_fg V)

theorem isIsomEmb_inl (V W : HSpace E) : HSpace.IsIsomEmb V (hsum V W) (LinearMap.inl E V.V W.V) := by
  intro x y
  show Formalism.E.orthSum V.hT W.hT _ _ = _
  rw [orthSum_apply]
  simp

theorem isIsomEmb_inr (V W : HSpace E) : HSpace.IsIsomEmb W (hsum V W) (LinearMap.inr E V.V W.V) := by
  intro x y
  show Formalism.E.orthSum V.hT W.hT _ _ = _
  rw [orthSum_apply]
  simp

theorem exists_GL_submatrix {A m n : Type} [CommRing A] [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (P : GL m A) (e : n ≃ m) : ∃ P' : GL n A, P'.1 = P.1.submatrix e e := by
  refine ⟨⟨P.1.submatrix e e, (P⁻¹).1.submatrix e e, ?_, ?_⟩, rfl⟩
  · rw [Matrix.submatrix_mul_equiv, P.mul_inv, Matrix.submatrix_one_equiv]
  · rw [Matrix.submatrix_mul_equiv, P.inv_mul, Matrix.submatrix_one_equiv]

private lemma cT_submatrix_mul_mul {m n : Type} [Fintype m] [Fintype n] (σ : ℂ →+* ℂ) (e : n ≃ m)
    (P J Q : Matrix m m ℂ) :
    cT σ (P.submatrix e e) * J.submatrix e e * Q.submatrix e e = (cT σ P * J * Q).submatrix e e := by
  have hc : cT σ (P.submatrix e e) = (cT σ P).submatrix e e := by
    ext i j
    rfl
  rw [hc, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]

theorem hasSignature_iff {n : Type} [Fintype n] [DecidableEq n] {J : Matrix n n ℂ} {p q : ℕ} : HasSignature J p q ↔
    ∃ (e : Fin p ⊕ Fin q ≃ n) (P : GL n ℂ), cT (starRingEnd ℂ) P.1 * J * P.1 = blkMat e 1 (-1) := by
  unfold Formalism.UG.HasSignature
  constructor
  · rintro ⟨e, P, h⟩
    obtain ⟨P', hP'⟩ := exists_GL_submatrix P e
    refine ⟨e.symm, P', ?_⟩
    have hJ : J = ((reindex e e) J).submatrix e e := by
      ext i j
      simp [Matrix.reindex_apply]
    rw [hP', hJ, cT_submatrix_mul_mul, h]
    ext i j
    simp [blkMat, Formalism.UG.Jpq]
  · rintro ⟨e, P, h⟩
    obtain ⟨P', hP'⟩ := exists_GL_submatrix P e
    refine ⟨e.symm, P', ?_⟩
    rw [hP', Matrix.reindex_apply, Equiv.symm_symm, cT_submatrix_mul_mul, h]
    ext i j
    simp [blkMat, Formalism.UG.Jpq]

private lemma blkMat_diagonal_eq_diagonal {m n ι : Type} [DecidableEq m] [DecidableEq n] [DecidableEq ι] (e : m ⊕ n ≃ ι)
    (d₁ : m → ℂ) (d₂ : n → ℂ) :
    blkMat e (Matrix.diagonal d₁) (Matrix.diagonal d₂) = Matrix.diagonal (fun i => Sum.elim d₁ d₂ (e.symm i)) := by
  unfold blkMat
  rw [Matrix.fromBlocks_diagonal, Matrix.submatrix_diagonal_equiv]
  rfl

private lemma blkMat_one_neg_one_eq_diagonal {m n ι : Type} [DecidableEq m] [DecidableEq n] [DecidableEq ι] (e : m ⊕ n ≃ ι) :
    blkMat e (1 : Matrix m m ℂ) (-1) = Matrix.diagonal (fun i => Sum.elim (fun _ => (1 : ℂ)) (fun _ => -1) (e.symm i)) := by
  have h1 : (1 : Matrix m m ℂ) = Matrix.diagonal (fun _ => 1) := Matrix.diagonal_one.symm
  have h2 : (-1 : Matrix n n ℂ) = Matrix.diagonal (fun _ => -1) := by
    rw [← Matrix.diagonal_one, Matrix.diagonal_neg]
  rw [h1, h2]
  exact blkMat_diagonal_eq_diagonal e _ _

theorem sigOK_hneg {V : HSpace E} (h : V.SigOK) : (hneg V).SigOK := by
  intro τ
  obtain ⟨e, P, hP⟩ := hasSignature_iff.1 (h τ)
  refine hasSignature_iff.2 ⟨(Equiv.sumComm _ _).trans e, P, ?_⟩
  have hg : (hneg V).gram.map τ = -(V.gram.map τ) := by
    rw [gram_hneg]
    ext i j
    simp
  rw [hg, Matrix.mul_neg, Matrix.neg_mul, hP, blkMat_one_neg_one_eq_diagonal, blkMat_one_neg_one_eq_diagonal, Matrix.diagonal_neg]
  congr 1
  funext i
  rcases hi : e.symm i with a | a <;> simp [hi]

theorem sigOK_hsum {V W : HSpace E} (h : V.SigOK) (h' : W.SigOK) : (hsum V W).SigOK := by
  intro τ
  obtain ⟨e1, P1, h1⟩ := hasSignature_iff.1 (h τ)
  obtain ⟨e2, P2, h2⟩ := hasSignature_iff.1 (h' τ)
  have hg : (hsum V W).gram.map τ = blkMat finSumFinEquiv (V.gram.map τ) (W.gram.map τ) := by
    rw [gram_hsum, blkMat_map _ _ (map_zero τ)]
  refine hasSignature_iff.2
    ⟨((Equiv.sumCongr (finSumFinEquiv (m := (V.sig τ).1) (n := (W.sig τ).1)).symm
        (finSumFinEquiv (m := (V.sig τ).2) (n := (W.sig τ).2)).symm).trans
      ((Equiv.sumSumSumComm _ _ _ _).trans ((Equiv.sumCongr e1 e2).trans finSumFinEquiv))),
      blkGL finSumFinEquiv (P1, P2), ?_⟩
  rw [hg, val_blkGL, cT_blkMat, blkMat_mul, blkMat_mul, h1, h2, blkMat_one_neg_one_eq_diagonal, blkMat_one_neg_one_eq_diagonal,
    blkMat_one_neg_one_eq_diagonal, blkMat_diagonal_eq_diagonal]
  congr 1
  funext i
  obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective i
  rcases s with k | k
  · rcases hk : e1.symm k with a | a <;> simp [hk]
  · rcases hk : e2.symm k with a | a <;> simp [hk]

theorem sigOK_hdbl {V : HSpace E} (h : V.SigOK) : (hdbl V).SigOK := sigOK_hsum h (sigOK_hneg h)

end GlobalTheory.Doubling

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSelfDualAtScaled
section
noncomputable section

namespace GlobalTheory.AdelicU.Model

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)








section Supp

omit [NumberField E] in
theorem map_map_tens {R R' R'' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R'] [CommRing R'']
    [Algebra F R''] (φ : R →ₐ[F] R') (ψ : R' →ₐ[F] R'') (y : R ⊗[F] E) :
    Algebra.TensorProduct.map ψ (AlgHom.id F E) (Algebra.TensorProduct.map φ (AlgHom.id F E) y) =
      Algebra.TensorProduct.map (ψ.comp φ) (AlgHom.id F E) y := by
  rw [← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp, AlgHom.comp_id]

omit [NumberField E] in
theorem adTens_eq_one {y : AF F ⊗[F] E} (h1 : ∀ w, compInf F E w y = 1) (h2 : ∀ v, compFin F E v y = 1) : y = 1 := by
  have := GlobalTheory.AutFunCounterexample.tens_inj (F := F) (E := E) (A := Ainf F) (B := Af F) (n := 1) (Matrix.of fun _ _ => y)
    (by
      ext i j
      rw [Subsingleton.elim i j, Matrix.one_apply_eq]
      exact GlobalTheory.AutFunCompare.infTens_ext fun w => (map_map_tens _ _ y).trans ((h1 w).trans (map_one _).symm))
    (by
      ext i j
      rw [Subsingleton.elim i j, Matrix.one_apply_eq]
      exact GlobalTheory.LatticeLocalGlobal.ext_components _ _ fun v =>
        (map_map_tens _ _ y).trans ((h2 v).trans (map_one _).symm))
  exact congrFun (congrFun this 0) 0

theorem idem_supp_iff {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F)) (ε : AF F)
    (e0 : ∀ w, evInf F w ε = 0) (e1 : evFin F v ε = 1) (e2 : ∀ u, u ≠ v → evFin F u ε = 0) (g : GAd σ J) :
    (∀ i j, algebraMap (AF F) (AF F ⊗[F] E) ε * ((matHom _ σ J g).1 - 1) i j = ((matHom _ σ J g).1 - 1) i j) ↔
      g ∈ (emb σ J v).range := by
  have c0 : ∀ w, compInf F E w (algebraMap (AF F) (AF F ⊗[F] E) ε) = 0 := fun w => by
    change evInf F w ε ⊗ₜ[F] (1 : E) = 0
    rw [e0, TensorProduct.zero_tmul]
  have c1 : compFin F E v (algebraMap (AF F) (AF F ⊗[F] E) ε) = 1 := by
    change evFin F v ε ⊗ₜ[F] (1 : E) = 1
    rw [e1]; rfl
  have c2 : ∀ u, u ≠ v → compFin F E u (algebraMap (AF F) (AF F ⊗[F] E) ε) = 0 := fun u hu => by
    change evFin F u ε ⊗ₜ[F] (1 : E) = 0
    rw [e2 u hu, TensorProduct.zero_tmul]
  have one : ∀ {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (m : Matrix (Fin n) (Fin n) A),
      m.map φ = 1 ↔ ∀ i j, φ ((m - 1) i j) = 0 := fun φ m => by
    rw [← Matrix.ext_iff]
    refine forall₂_congr fun i j => ?_
    rw [Matrix.sub_apply, map_sub, sub_eq_zero, Matrix.map_apply]
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  have pf : ∀ u, proj σ J u g = 1 ↔ ∀ i j, compFin F E u (((matHom _ σ J g).1 - 1) i j) = 0 := fun u =>
    Iff.trans ⟨fun h => congrArg (fun x => (matHom _ σ J x).1) h, fun h => Subtype.ext (Units.ext h)⟩ (one _ _)
  have pa : ∀ w, projArch σ J w g = 1 ↔ ∀ i j, compInf F E w (((matHom _ σ J g).1 - 1) i j) = 0 := fun u =>
    Iff.trans ⟨fun h => congrArg (fun x => (matHom _ σ J x).1) h, fun h => Subtype.ext (Units.ext h)⟩ (one _ _)
  rw [range_emb, mem_atPts, mem_finPts_iff_forall]
  simp only [pf, pa, Finset.mem_singleton]
  constructor
  · intro h
    exact ⟨fun w i j => by rw [← h, map_mul, c0, zero_mul], fun u hu i j => by rw [← h, map_mul, c2 u hu, zero_mul]⟩
  · rintro ⟨h1, h2⟩ i j
    rw [← sub_eq_zero, ← add_eq_right (b := 1)]
    refine adTens_eq_one (fun w => ?_) fun u => ?_
    · rw [map_add (f := _), map_sub, map_mul, h1, map_one]; simp
    · rw [map_add (f := _), map_sub, map_mul, map_one]
      by_cases hu : u = v
      · subst hu; rw [c1]; simp
      · rw [h2 u hu]; simp

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem suppF_iff {D : D7} (V : HSp D) {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F}
    (h : IsPlaceIdem D v ε) (g : GA D V) :
    Formalism.IndefR.Mult.SuppF V (algebraMap (AF D.host.F) (AE D) ε) g ↔ g ∈ (emb D.sp.cm.sig V.gram v).range := by
  obtain ⟨α, rfl, h1, h2⟩ := h
  exact idem_supp_iff _ _ v _ (fun _ => rfl) h1 h2 g

theorem emb_mem_KsphC_iff {D : D7} (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F))
    (x : GLoc D.sp.cm.sig V.gram v) :
    emb D.sp.cm.sig V.gram v x ∈ KsphC V ∅ ↔ x ∈ stabLoc D.sp.cm.sig V.gram (frameLat V) v := by
  rw [KsphC_eq]
  exact ⟨fun h => by simpa using (mem_levelOff.1 h).2.2 v (by simp), emb_mem_levelOff (by simp)⟩

end Supp

section More

end More

end GlobalTheory.AdelicU.Model
end
end

