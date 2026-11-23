module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.AdelicProofs.LocGram
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
public import Development.AutomorphicSpectrum.Proofs.MembershipProofs.Bundle0003
public import Development.AutomorphicSpectrum.Proofs.MembershipProofs.Bundle0004

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.AdelicProofs.HasIwasawaOfFrame
section
noncomputable section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.CompanionTheory.IwaDbl

namespace GlobalTheory.CompanionTheory.IwaDbl.FrameCore

section Generic

open Matrix GlobalTheory.WeilM GlobalTheory.CompanionTheory.VacLoc

variable {S : Type} [CommRing S]

theorem diagCols_isotropic (c : S →ₐ[ℤ] S) {β : Type} [Fintype β] [DecidableEq β] (H : Matrix β β S) :
    (diagCols β : Matrix (β ⊕ β) β S)ᵀ * dbl H * (diagCols β : Matrix (β ⊕ β) β S).map c = 0 := by
  have h : (diagCols β : Matrix (β ⊕ β) β S).map c = diagCols β := by
    ext (i | i) j <;> simp [diagCols, Matrix.one_apply, apply_ite c]
  rw [h]
  simp [diagCols, dbl, Matrix.transpose_fromRows, Matrix.fromCols_mul_fromBlocks, Matrix.fromCols_mul_fromRows]

theorem iso_iff {n : ℕ} (c : S →+* S) (J₀ : Matrix (Fin n) (Fin n) S) (x : Matrix (Fin (n + n)) (Fin (n + n)) S) :
    cT c x * dblGram finSumFinEquiv J₀ * x = dblGram finSumFinEquiv J₀ ↔
      (x.submatrix finSumFinEquiv finSumFinEquiv)ᵀ * dbl J₀ᵀ * (x.submatrix finSumFinEquiv finSumFinEquiv).map c =
        dbl J₀ᵀ := by
  have hd : dbl J₀ᵀ = ((dblGram finSumFinEquiv J₀)ᵀ).submatrix finSumFinEquiv finSumFinEquiv := by
    rw [← Matrix.transpose_submatrix, dblGram, submatrix_blkMat, dbl, Matrix.fromBlocks_transpose]
    simp
  have hL : (x.submatrix finSumFinEquiv finSumFinEquiv)ᵀ *
      ((dblGram finSumFinEquiv J₀)ᵀ).submatrix finSumFinEquiv finSumFinEquiv *
      (x.submatrix finSumFinEquiv finSumFinEquiv).map c =
      ((cT c x * dblGram finSumFinEquiv J₀ * x)ᵀ).submatrix finSumFinEquiv finSumFinEquiv := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, cT, Matrix.transpose_transpose, Matrix.transpose_submatrix,
      Matrix.submatrix_mul_equiv, ← Matrix.submatrix_map, Matrix.submatrix_mul_equiv, Matrix.mul_assoc]
  rw [hd, hL]
  constructor
  · intro h; rw [h]
  · intro h
    have := congrArg (fun X => (X.submatrix finSumFinEquiv.symm finSumFinEquiv.symm)ᵀ) h
    simpa using this

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem cT_unit_mul (c : S →+* S) (B : GL ι S) : cT c (B⁻¹).1 * cT c B.1 = 1 := by
  rw [← cT_mul, Units.mul_inv]
  simp [cT, Matrix.map_one _ (map_zero c) (map_one c)]

theorem conj_iso (c : S →+* S) {Q' Q₀ : Matrix ι ι S} (B : GL ι S) (hB : cT c B.1 * Q' * B.1 = Q₀) {X : GL ι S}
    (hX : cT c X.1 * Q' * X.1 = Q') : cT c (B⁻¹ * X * B).1 * Q₀ * (B⁻¹ * X * B).1 = Q₀ := by
  subst hB
  simp only [Units.val_mul, cT_mul]
  calc _ = cT c B.1 * (cT c X.1 * (cT c (B⁻¹).1 * cT c B.1) * Q' * (B.1 * (B⁻¹).1) * X.1) * B.1 := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [cT_unit_mul, Units.mul_inv, Matrix.mul_one, Matrix.mul_one, hX]

theorem conj_back (c : S →+* S) {Q' Q₀ : Matrix ι ι S} (B : GL ι S) (hB : cT c B.1 * Q' * B.1 = Q₀) :
    cT c (B⁻¹).1 * Q₀ * (B⁻¹).1 = Q' := by
  subst hB
  calc _ = (cT c (B⁻¹).1 * cT c B.1) * Q' * (B.1 * (B⁻¹).1) := by simp only [Matrix.mul_assoc]
    _ = Q' := by rw [cT_unit_mul, Units.mul_inv, Matrix.one_mul, Matrix.mul_one]

def reGL {α : Type} [Fintype α] [DecidableEq α] (e : α ≃ ι) (u : GL α S) : GL ι S :=
  ⟨u.1.submatrix e.symm e.symm, (u⁻¹).1.submatrix e.symm e.symm,
    by rw [Matrix.submatrix_mul_equiv, Units.mul_inv, Matrix.submatrix_one_equiv],
    by rw [Matrix.submatrix_mul_equiv, Units.inv_mul, Matrix.submatrix_one_equiv]⟩

theorem mulVec_diagCols {n : ℕ} (M : Matrix (Fin (n + n)) (Fin (n + n)) S) (u : Fin n → S) :
    (M.submatrix finSumFinEquiv finSumFinEquiv * diagCols (E := S) (Fin n)) *ᵥ u =
      (M *ᵥ pairVec finSumFinEquiv u u) ∘ finSumFinEquiv := by
  rw [← Matrix.mulVec_mulVec, Matrix.submatrix_mulVec_equiv]
  congr 2
  funext j
  simp [pairVec, diagCols, Matrix.fromRows_mulVec]

theorem keepsDiag_of_frame {n : ℕ} (G : GL (Fin (n + n)) S) (b : GL (Fin n) S) (Y : GL (Fin (n + n)) S)
    (t : Matrix (Fin n) (Fin n) S)
    (hY : Y.1.submatrix finSumFinEquiv finSumFinEquiv * diagCols (E := S) (Fin n) =
      ((blkGL finSumFinEquiv (b, b))⁻¹ * G⁻¹ * blkGL finSumFinEquiv (b, b)).1.submatrix finSumFinEquiv finSumFinEquiv *
        diagCols (E := S) (Fin n) * t) :
    KeepsDiag finSumFinEquiv (G * (blkGL finSumFinEquiv (b, b) * Y * (blkGL finSumFinEquiv (b, b))⁻¹)).1 := by
  set B := blkGL finSumFinEquiv (b, b) with hBdef
  set x := B⁻¹ * G⁻¹ * B with hx
  have hB : G * B * x = B := by rw [hx]; group
  refine keepsDiag_of_mulVec fun w hw => ?_
  obtain ⟨z, rfl⟩ := (mem_diagSub finSumFinEquiv).1 hw
  obtain ⟨u, hu⟩ : ∃ u, u = (b⁻¹).1 *ᵥ z := ⟨_, rfl⟩
  have e1 : (B⁻¹).1 *ᵥ pairVec finSumFinEquiv z z = pairVec finSumFinEquiv u u := by
    have : B⁻¹ = blkGL finSumFinEquiv (b⁻¹, b⁻¹) := by rw [hBdef, ← map_inv, Prod.inv_mk]
    rw [this, val_blkGL, hu]
    exact blkMat_mulVec _ _ _ _ _
  have e2 : Y.1 *ᵥ pairVec finSumFinEquiv u u = x.1 *ᵥ pairVec finSumFinEquiv (t *ᵥ u) (t *ᵥ u) := by
    have h : (Y.1 *ᵥ pairVec finSumFinEquiv u u) ∘ finSumFinEquiv =
        (x.1 *ᵥ pairVec finSumFinEquiv (t *ᵥ u) (t *ᵥ u)) ∘ finSumFinEquiv := by
      rw [← mulVec_diagCols, ← mulVec_diagCols, hY, Matrix.mulVec_mulVec]
    exact finSumFinEquiv.surjective.injective_comp_right h
  have e3 : (G * (B * Y * B⁻¹)).1 *ᵥ pairVec finSumFinEquiv z z =
      pairVec finSumFinEquiv (b.1 *ᵥ t *ᵥ u) (b.1 *ᵥ t *ᵥ u) := by
    calc _ = (G * B).1 *ᵥ (Y.1 *ᵥ ((B⁻¹).1 *ᵥ pairVec finSumFinEquiv z z)) := by
          simp only [Units.val_mul, Matrix.mulVec_mulVec, Matrix.mul_assoc]
      _ = (G * B).1 *ᵥ (x.1 *ᵥ pairVec finSumFinEquiv (t *ᵥ u) (t *ᵥ u)) := by rw [e1, e2]
      _ = (G * B * x).1 *ᵥ pairVec finSumFinEquiv (t *ᵥ u) (t *ᵥ u) := by
          simp only [Units.val_mul, Matrix.mulVec_mulVec]
      _ = B.1 *ᵥ pairVec finSumFinEquiv (t *ᵥ u) (t *ᵥ u) := by rw [hB]
      _ = _ := by rw [hBdef, val_blkGL]; exact blkMat_mulVec _ _ _ _ _
  rw [e3]
  exact (mem_diagSub finSumFinEquiv).2 ⟨_, rfl⟩

end Generic

section Points

variable {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R] {n : ℕ}

theorem gram_blk (σ : E →ₐ[F] E) {J : Matrix (Fin n) (Fin n) E} {Q : Matrix (Fin (n + n)) (Fin (n + n)) E}
    (hQ : Q = dblGram finSumFinEquiv J) (b : GL (Fin n) (R ⊗[F] E)) :
    cT (sigR R σ) (blkGL finSumFinEquiv (b, b)).1 * JR R Q * (blkGL finSumFinEquiv (b, b)).1 =
      dblGram finSumFinEquiv (locGram σ J b) := by
  subst hQ
  rw [JR_dblGram, val_blkGL, cT_blkMat, dblGram, blkMat_mul, blkMat_mul, dblGram, locGram]
  simp only [Matrix.mul_neg, Matrix.neg_mul]

theorem cT_locGram (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {J : Matrix (Fin n) (Fin n) E}
    (hJ : ∀ i j, σ (J j i) = J i j) (b : GL (Fin n) (R ⊗[F] E)) :
    cT (sigR R σ) (locGram σ J b) = locGram σ J b := by
  have h1 : cT (sigR R σ) (JR (F := F) R J) = JR R J := by
    ext i j
    simp only [cT, JR, Matrix.transpose_apply, Matrix.map_apply]
    rw [← hJ i j]
    rfl
  have h2 : cT (sigR R σ) (cT (sigR R σ) b.1) = b.1 := by
    ext i j
    simp [cT, GlobalTheory.Doubling.sigR_invol hσ]
  rw [locGram, cT_mul, cT_mul, h1, h2, Matrix.mul_assoc]

end Points

end GlobalTheory.CompanionTheory.IwaDbl.FrameCore

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AdelicProofs.HasSatOfFamily
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.CompanionTheory.IwaDbl

namespace GlobalTheory.CompanionTheory.IwaDbl

theorem hasSat_of_family {B K O I : Type} [CommRing B] [Field K] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra O K] [IsFractionRing O K] (π : I → B →+* K) (hinj : ∀ y z : B, (∀ i, π i y = π i z) → y = z)
    (hsurj : ∀ f : I → K, ∃ y : B, ∀ i, π i y = f i) (A : Subring B)
    (hA : ∀ y, y ∈ A ↔ ∀ i, π i y ∈ (algebraMap O K).range) (β : Type) [Fintype β] [DecidableEq β] : HasSat A β := by
  have hlift : ∀ {m n : Type} (f : I → Matrix m n K), ∃ X : Matrix m n B, ∀ i, X.map (π i) = f i := by
    intro m n f
    choose g hg using fun p : m × n => hsurj fun i => f i p.1 p.2
    exact ⟨Matrix.of fun a b => g (a, b), fun i => Matrix.ext fun a b => by simp [hg]⟩
  have hext : ∀ {m n : Type} (X Y : Matrix m n B), (∀ i, X.map (π i) = Y.map (π i)) → X = Y := by
    intro m n X Y h
    exact Matrix.ext fun a b => hinj _ _ fun i => by simpa using congrFun (congrFun (h i) a) b
  have hmem : ∀ {m n : Type} (X : Matrix m n B) (Y : I → Matrix m n O),
      (∀ i, X.map (π i) = (Y i).map (algebraMap O K)) → ∀ a b, X a b ∈ A := by
    intro m n X Y h a b
    refine (hA _).2 fun i => RingHom.mem_range.2 ⟨Y i a b, ?_⟩
    simpa using (congrFun (congrFun (h i) a) b).symm
  intro C N hNC
  have hleft : ∀ i, ∃ L : Matrix β (β ⊕ β) K, L * C.map (π i) = 1 := fun i =>
    ⟨N.map (π i), by rw [← Matrix.map_mul, hNC]; simp⟩
  choose t C₀ D htC hdet using fun i =>
    GlobalTheory.CompanionTheory.MatSat.exists_saturation (O := O) (C.map (π i)) (hleft i)
  obtain ⟨T, hT⟩ := hlift fun i => Units.val (t i)
  obtain ⟨T', hT'⟩ := hlift fun i => Units.val (t i)⁻¹
  obtain ⟨Dl, hDl⟩ := hlift fun i => (D i).map (algebraMap O K)
  obtain ⟨Ml, hMl⟩ := hlift fun i => ((Matrix.fromCols (C₀ i) (D i))⁻¹).map (algebraMap O K)
  have hCT : ∀ i, (C * T).map (π i) = (C₀ i).map (algebraMap O K) := fun i => by
    rw [Matrix.map_mul, hT]
    exact htC i
  refine ⟨T, T', Dl, Ml, ?_, hmem _ C₀ hCT, hmem _ D hDl,
    hmem _ (fun i => (Matrix.fromCols (C₀ i) (D i))⁻¹) hMl, ?_⟩
  · refine hext _ _ fun i => ?_
    rw [Matrix.map_mul, hT, hT', Units.mul_inv]
    simp
  · refine hext _ _ fun i => ?_
    rw [Matrix.map_mul, Matrix.fromCols_map, hMl, hCT, hDl, ← Matrix.fromCols_map, ← Matrix.map_mul,
      Matrix.nonsing_inv_mul _ (hdet i)]
    simp

end GlobalTheory.CompanionTheory.IwaDbl
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AdelicProofs.MemKFinOfFrameIntegral
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.CompanionTheory.IwaDbl

noncomputable section

namespace GlobalTheory.CompanionTheory.IwaDbl

theorem mem_KFin_of_frame_integral {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (σ : E →ₐ[F] E) {Q : Matrix (Fin (n + n)) (Fin (n + n)) E} {L : Submodule (𝓞 E) (Fin n → E)}
    {v : HeightOneSpectrum (𝓞 F)} (b : GL (Fin n) (Fv F v ⊗[F] E))
    (hb : ∀ y : Fin n → Fv F v ⊗[F] E, (∀ i, y i ∈ intLoc F E v) ↔ b.1 *ᵥ y ∈ latLoc F L v) (k : GLoc σ Q v)
    (h1 : ∀ i j, ((blkGL finSumFinEquiv (b, b))⁻¹ * matHom _ σ Q k * blkGL finSumFinEquiv (b, b)).1 i j ∈ intLoc F E v)
    (h2 : ∀ i j, ((blkGL finSumFinEquiv (b, b))⁻¹ * (matHom _ σ Q k)⁻¹ * blkGL finSumFinEquiv (b, b)).1 i j ∈ intLoc F E v) :
    k ∈ KFin σ Q L v := by
  have hB : ∀ y : Fin (n + n) → Fv F v ⊗[F] E, (∀ i, y i ∈ intLoc F E v) ↔
      (blkGL finSumFinEquiv (b, b)).1 *ᵥ y ∈ latLoc F (sumLat finSumFinEquiv L L) v := by
    intro y
    rw [latLoc_sumLat]
    conv_rhs => rw [← pairVec_eta finSumFinEquiv y]
    rw [val_blkGL, blkMat_mulVec, pairVec_mem_sumLat, ← hb, ← hb]
    constructor
    · exact fun h => ⟨fun i => h _, fun i => h _⟩
    · rintro ⟨h, h'⟩ j
      obtain ⟨i | i, rfl⟩ := finSumFinEquiv.surjective j
      exacts [h i, h' i]
  have hint : ∀ K : Matrix (Fin (n + n)) (Fin (n + n)) (Fv F v ⊗[F] E), (∀ i j, K i j ∈ intLoc F E v) →
      ∀ z : Fin (n + n) → Fv F v ⊗[F] E, (∀ i, z i ∈ intLoc F E v) → ∀ i, (K *ᵥ z) i ∈ intLoc F E v :=
    fun K hK z hz i => by
      change ∑ j, K i j * z j ∈ _
      exact sum_mem fun j _ => mul_mem (hK i j) (hz j)
  refine mem_stabLoc.2 fun y => ?_
  generalize blkGL finSumFinEquiv (b, b) = B at hB h1 h2
  generalize matHom _ σ Q k = M at h1 h2 ⊢
  have e0 : y = B.1 *ᵥ ((B⁻¹).1 *ᵥ y) := by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  have e1 : M.1 *ᵥ y = B.1 *ᵥ ((B⁻¹ * M * B).1 *ᵥ ((B⁻¹).1 *ᵥ y)) := by
    simp only [Matrix.mulVec_mulVec, ← Units.val_mul]
    congr 2
    group
  have e2 : (B⁻¹).1 *ᵥ y = (B⁻¹ * M⁻¹ * B).1 *ᵥ ((B⁻¹ * M * B).1 *ᵥ ((B⁻¹).1 *ᵥ y)) := by
    simp only [Matrix.mulVec_mulVec, ← Units.val_mul]
    congr 2
    group
  have hy : y ∈ latLoc F (sumLat finSumFinEquiv L L) v ↔ ∀ i, ((B⁻¹).1 *ᵥ y) i ∈ intLoc F E v := by
    rw [hB, ← e0]
  have hMy : M.1 *ᵥ y ∈ latLoc F (sumLat finSumFinEquiv L L) v ↔
      ∀ i, ((B⁻¹ * M * B).1 *ᵥ ((B⁻¹).1 *ᵥ y)) i ∈ intLoc F E v := by
    rw [hB, ← e1]
  rw [hy, hMy]
  refine ⟨hint _ h1 _, fun h => ?_⟩
  rw [e2]
  exact hint _ h2 _ h

end GlobalTheory.CompanionTheory.IwaDbl
end
end

