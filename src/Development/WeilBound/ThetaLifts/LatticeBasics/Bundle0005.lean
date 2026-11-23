module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.AdelicProofs.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AutomorphicSpectrum.Proofs.TwistedProofs.UnramDoublingInert

@[expose] public section

-- bundled from Development.WeilBound.ThetaLifts.LatticeBasics.HgtWitt
section
noncomputable section

open scoped TensorProduct Matrix
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.CompanionTheory.IwaDbl GlobalTheory.CompanionTheory.IwaDbl.FrameCore GlobalTheory.CompanionTheory.WittOrbit GlobalTheory.WeilM Matrix

namespace GlobalTheory.ThK.Dbl.Hgt

section Generic

variable {S : Type} [CommRing S] {c : S →ₐ[ℤ] S} {A : Subring S} {ε : S}

theorem form_star' {l m n : Type} [Fintype m] (hc : ∀ z, c (c z) = z) {H : Matrix m m S} (hH : (H.map c)ᵀ = ε • H)
    (X : Matrix m l S) (Y : Matrix m n S) : ((Xᵀ * H * Y.map c).map c)ᵀ = ε • (Yᵀ * H * X.map c) := by
  rw [map_mul', map_mul', map_map_eq hc, transpose_mul, transpose_mul, hH, Matrix.mul_assoc, Matrix.smul_mul, Matrix.mul_smul]
  rfl

theorem exists_partner' {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] (hc : ∀ z, c (c z) = z)
    (hε : IsUnit ε) (hs : ∀ z ∈ A, c z ∈ A) {w : S} (hw : w ∈ A) (htr : w + c w = 1) {H H' : Matrix m m S}
    (hH : (H.map c)ᵀ = ε • H) (hHA : ∀ i j, H i j ∈ A) (hH'A : ∀ i j, H' i j ∈ A) (hHH : H * H' = 1) {J J' : Matrix n n S}
    (hJ : (J.map c)ᵀ = ε • J) (hJA : ∀ i j, J i j ∈ A) (hJ'A : ∀ i j, J' i j ∈ A) (hJJ : J * J' = 1) {C : Matrix m n S}
    {N : Matrix n m S} (hCA : ∀ i j, C i j ∈ A) (hNA : ∀ i j, N i j ∈ A) (hN : N * C = 1) (hC : Cᵀ * H * C.map c = 0) :
    ∃ D : Matrix m n S, (∀ i j, D i j ∈ A) ∧ Cᵀ * H * D.map c = J ∧ Dᵀ * H * C.map c = J ∧ Dᵀ * H * D.map c = 0 := by
  have can : ∀ {X Y : Matrix n n S}, ε • X = ε • Y → X = Y := fun h => (hε.smul_left_cancel).1 h
  obtain ⟨D₁, hD₁A, h1⟩ : ∃ D₁ : Matrix m n S, (∀ i j, D₁ i j ∈ A) ∧ Cᵀ * H * D₁.map c = J := by
    refine ⟨(H' * Nᵀ * J).map c, int_map hs (int_mul (int_mul hH'A fun i j => hNA j i) hJA), ?_⟩
    rw [map_map_eq hc]
    calc Cᵀ * H * (H' * Nᵀ * J) = Cᵀ * (H * H') * Nᵀ * J := by simp only [Matrix.mul_assoc]
      _ = J := by rw [hHH, Matrix.mul_one, ← transpose_mul, hN, transpose_one, Matrix.one_mul]
  have h2 : D₁ᵀ * H * C.map c = J := can (by rw [← form_star' hc hH, h1, hJ])
  set G := D₁ᵀ * H * D₁.map c with hG
  have hGA : ∀ i j, G i j ∈ A := int_mul (int_mul (fun i j => hD₁A j i) hHA) (int_map hs hD₁A)
  have hGs : (G.map c)ᵀ = ε • G := form_star' hc hH _ _
  obtain ⟨T, hTA, hT⟩ : ∃ T : Matrix n n S, (∀ i j, T i j ∈ A) ∧ J * T.map c = w • G := by
    refine ⟨(w • (J' * G)).map c, int_map hs fun i j => mul_mem hw (int_mul hJ'A hGA i j), ?_⟩
    rw [map_map_eq hc, Matrix.mul_smul, ← Matrix.mul_assoc, hJJ, Matrix.one_mul]
  have hT' : Tᵀ * J = c w • G := can (by
    have := congrArg (fun X : Matrix n n S => (X.map c)ᵀ) hT
    simp only [map_mul', map_map_eq hc, transpose_mul, hJ, Matrix.mul_smul] at this
    rw [this, smul_comm, ← hGs]
    ext i j; simp)
  have hm : (D₁ - C * T).map c = D₁.map c - C.map c * T.map c := by
    rw [← map_mul']; ext i j; simp only [Matrix.map_apply, Matrix.sub_apply, map_sub]
  have h3 : Cᵀ * H * (D₁ - C * T).map c = J := by
    rw [hm, Matrix.mul_sub, h1, ← Matrix.mul_assoc, hC, Matrix.zero_mul, sub_zero]
  refine ⟨D₁ - C * T, fun i j => sub_mem (hD₁A i j) (int_mul hCA hTA i j), h3, can ?_, ?_⟩
  · rw [← form_star' hc hH, h3, hJ]
  · rw [transpose_sub, transpose_mul, Matrix.sub_mul, Matrix.sub_mul, Matrix.mul_assoc Tᵀ, Matrix.mul_assoc Tᵀ, h3, hT', hm,
      Matrix.mul_sub, ← Matrix.mul_assoc, h2, hT, ← hG, sub_sub, ← add_smul, htr, one_smul, sub_self]

variable {β : Type} [Fintype β] [DecidableEq β]

theorem exists_int_iso (hc : ∀ z, c (c z) = z) (hε : IsUnit ε) (hs : ∀ z ∈ A, c z ∈ A) {w₀ : S} (hw : w₀ ∈ A)
    (htr : w₀ + c w₀ = 1) {J J' : Matrix β β S} (hJ : (J.map c)ᵀ = ε • J) (hJA : ∀ i j, J i j ∈ A) (hJ'A : ∀ i j, J' i j ∈ A)
    (hJJ : J * J' = 1) {C : Matrix (β ⊕ β) β S} {N : Matrix β (β ⊕ β) S} (hCA : ∀ i j, C i j ∈ A) (hNA : ∀ i j, N i j ∈ A)
    (hN : N * C = 1) (hC : Cᵀ * dbl J * C.map c = 0) :
    ∃ k : GL (β ⊕ β) S, k.1ᵀ * dbl J * k.1.map c = dbl J ∧ (∀ i j, k.1 i j ∈ A) ∧ (∀ i j, (k⁻¹).1 i j ∈ A) ∧
      k.1 * diagCols β = C := by
  have hdA : ∀ {X : Matrix β β S}, (∀ i j, X i j ∈ A) → ∀ i j, dbl X i j ∈ A := by
    rintro X hX (i | i) (j | j)
    · exact hX i j
    · exact zero_mem _
    · exact zero_mem _
    · exact neg_mem (hX i j)
  have hJ1 : ∀ i j, c (J j i) = ε * J i j := fun i j => congrFun (congrFun hJ i) j
  have hH : ((dbl J).map c)ᵀ = ε • dbl J := by
    ext (i | i) (j | j) <;> simp [dbl, hJ1]
  have hHH : dbl J * dbl J' = 1 := by
    simp [dbl, fromBlocks_multiply, hJJ]
  obtain ⟨X, hXA, h1, h2, h3⟩ := exists_partner' hc hε hs hw htr hH (hdA hJA) (hdA hJ'A) hHH hJ hJA hJ'A hJJ hCA hNA hN hC
  set K : Matrix (β ⊕ β) (β ⊕ β) S := fromCols (c w₀ • C + X) (w₀ • C - X) with hK
  have hKA : ∀ i j, K i j ∈ A := by
    rintro i (j | j)
    · exact add_mem (mul_mem (hs _ hw) (hCA i j)) (hXA i j)
    · exact sub_mem (mul_mem hw (hCA i j)) (hXA i j)
  have hKm : K.map c = fromCols (w₀ • C.map c + X.map c) (c w₀ • C.map c - X.map c) := by
    ext i (j | j) <;> simp [hK, hc]
  have hU : Kᵀ * dbl J * K.map c = dbl J := by
    rw [hKm, hK, transpose_fromCols, fromRows_mul, fromRows_mul_fromCols]
    simp only [transpose_add, transpose_sub, transpose_smul, Matrix.add_mul, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_sub,
      Matrix.smul_mul, Matrix.mul_smul, hC, h1, h2, h3, smul_zero, zero_add, add_zero, zero_sub, sub_zero]
    have e : c w₀ = 1 - w₀ := by rw [← htr]; ring
    rw [e]
    refine fromBlocks_inj.mpr ⟨?_, ?_, ?_, ?_⟩ <;> module
  have hL : (dbl J' * Kᵀ * dbl J).map c * K = 1 := by
    have : dbl J' * Kᵀ * dbl J * K.map c = 1 := by
      rw [Matrix.mul_assoc (dbl J'), Matrix.mul_assoc (dbl J'), hU, mul_eq_one_comm.mp hHH]
    have := congrArg (fun Y : Matrix (β ⊕ β) (β ⊕ β) S => Y.map c) this
    simp only [map_mul' _ (K.map c), map_map_eq hc] at this
    rw [this]
    exact Matrix.map_one _ (map_zero c) (map_one c)
  refine ⟨⟨K, (dbl J' * Kᵀ * dbl J).map c, mul_eq_one_comm.mp hL, hL⟩, hU, hKA, ?_, ?_⟩
  · exact int_map hs (int_mul (int_mul (hdA hJ'A) fun i j => hKA j i) (hdA hJA))
  · show K * diagCols β = C
    refine (fromCols_mul_fromRows _ _ _ _).trans ?_
    rw [Matrix.mul_one, Matrix.mul_one, add_add_sub_cancel, ← add_smul, add_comm, htr, one_smul]

omit [Fintype β] [DecidableEq β] in
theorem dbl_smul (l : S) (H : Matrix β β S) : dbl (l • H) = l • dbl H := by
  simp [dbl, fromBlocks_smul]

theorem lagr_orbit' (hc : ∀ z, c (c z) = z) (hs : ∀ z ∈ A, c z ∈ A) {w₀ : S} (hw : w₀ ∈ A)
    (htr : w₀ + c w₀ = 1) {H H' : Matrix β β S} (hH : (H.map c)ᵀ = H) (l : Sˣ) (hHA : ∀ i j, l.1 * H i j ∈ A)
    (hH'A : ∀ i j, H' i j ∈ A) (hHH : (l.1 • H) * H' = 1) (hS : HasSat A β) (y y' : Matrix (β ⊕ β) (β ⊕ β) S)
    (hyy : y' * y = 1) (hy : yᵀ * dbl H * y.map c = dbl H) :
    ∃ k : GL (β ⊕ β) S, k.1ᵀ * dbl H * k.1.map c = dbl H ∧ (∀ i j, k.1 i j ∈ A) ∧ (∀ i j, (k⁻¹).1 i j ∈ A) ∧
      ∃ t : Matrix β β S, k.1 * diagCols (E := S) β = y * diagCols (E := S) β * t := by
  have hN : ((Matrix.fromCols (1 : Matrix β β S) (0 : Matrix β β S) : Matrix β (β ⊕ β) S) * y') *
      (y * diagCols (E := S) β) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc y', hyy, Matrix.one_mul, diagCols, Matrix.fromCols_mul_fromRows]
    simp
  obtain ⟨t, t', D, M, -, h2, h3, h4, h5⟩ := hS _ _ hN
  have hN' : M.toRows₁ * (y * diagCols (E := S) β * t) = 1 := by
    rw [← fromRows_toRows M, fromRows_mul_fromCols, ← fromBlocks_one] at h5
    exact (fromBlocks_inj.mp h5).1
  obtain ⟨κ, k1, k2, k3, k4⟩ := exists_int_iso (ε := c l * (l⁻¹).1) (J := l.1 • H) hc ((l.isUnit.map c).mul (l⁻¹).isUnit) hs hw htr
    (by
      rw [smul_smul, mul_assoc, Units.inv_mul, mul_one]
      conv_rhs => rw [← hH]
      ext i j; simp) hHA hH'A hHH h2 (N := M.toRows₁) (fun i j => h4 _ _) hN'
    (by
      rw [dbl_smul, Matrix.mul_smul, Matrix.smul_mul, map_mul', map_mul', Matrix.transpose_mul, Matrix.transpose_mul]
      calc _ = l.1 • (tᵀ * ((diagCols β : Matrix (β ⊕ β) β S)ᵀ * (yᵀ * dbl H * y.map c) *
            (diagCols β : Matrix (β ⊕ β) β S).map c) * t.map c) := by simp only [Matrix.mul_assoc]
        _ = 0 := by rw [hy, diagCols_isotropic, Matrix.mul_zero, Matrix.zero_mul, smul_zero])
  rw [dbl_smul, Matrix.mul_smul, Matrix.smul_mul] at k1
  exact ⟨κ, l.isUnit.smul_left_cancel.1 k1, k2, k3, t, k4⟩

end Generic

theorem hasIwasawa_of_frame' {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R] {n : ℕ}
    (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {J : Matrix (Fin n) (Fin n) E} {Q : Matrix (Fin (n + n)) (Fin (n + n)) E}
    (hQ : Q = dblGram finSumFinEquiv J) (hJ : ∀ i j, σ (J j i) = J i j) (A : Subring (R ⊗[F] E)) (w₀ : R ⊗[F] E)
    (hw : w₀ ∈ A) (htr : w₀ + Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R σ w₀ = 1) (hst : ∀ z ∈ A, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R σ z ∈ A)
    (b : GL (Fin n) (R ⊗[F] E)) (l : (R ⊗[F] E)ˣ) (hint : ∀ i j, l.1 * locGram σ J b i j ∈ A)
    (hinv : ∃ J' : Matrix (Fin n) (Fin n) (R ⊗[F] E), (∀ i j, J' i j ∈ A) ∧ J' * (l.1 • locGram σ J b) = 1)
    (hS : HasSat A (Fin n)) (K : Subgroup (HA R σ Q))
    (hK : ∀ k : HA R σ Q,
      (∀ i j, ((blkGL finSumFinEquiv (b, b))⁻¹ * matHom R σ Q k * blkGL finSumFinEquiv (b, b)).1 i j ∈ A) →
      (∀ i j, ((blkGL finSumFinEquiv (b, b))⁻¹ * (matHom R σ Q k)⁻¹ * blkGL finSumFinEquiv (b, b)).1 i j ∈ A) → k ∈ K) :
    HasIwasawa σ Q K := by
  intro g
  obtain ⟨J', hJ'A, hJJ'⟩ := hinv
  have hB := gram_blk (R := R) σ hQ b
  set B := blkGL finSumFinEquiv (b, b) with hBdef
  set J₀ := locGram σ J b with hJ₀
  set s := Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R σ
  let ca : (R ⊗[F] E) →ₐ[ℤ] (R ⊗[F] E) := s.toIntAlgHom
  have hca : ∀ z, ca (ca z) = z := fun z => GlobalTheory.Doubling.sigR_invol hσ z
  have hherm := cT_locGram (R := R) σ hσ hJ b
  rw [← hJ₀] at hherm
  have hg : cT s ((matHom R σ Q g)⁻¹).1 * JR R Q * ((matHom R σ Q g)⁻¹).1 = JR R Q := (g⁻¹).2
  have hx := FrameCore.conj_iso s B hB hg
  set x := B⁻¹ * (matHom R σ Q g)⁻¹ * B with hxdef
  obtain ⟨κ, hκ0, hκ1, hκ2, t, hκ⟩ := lagr_orbit' (c := ca) (H := J₀ᵀ) (H' := J'ᵀ) hca hst hw htr
    (congrArg transpose hherm) l (fun i j => hint j i) (fun i j => hJ'A j i)
    (by rw [← transpose_smul, ← transpose_mul, hJJ', transpose_one]) hS
    (x.1.submatrix finSumFinEquiv finSumFinEquiv) ((x⁻¹).1.submatrix finSumFinEquiv finSumFinEquiv)
    (by rw [Matrix.submatrix_mul_equiv, Units.inv_mul, Matrix.submatrix_one_equiv])
    ((iso_iff s J₀ x.1).1 hx)
  set Y : GL (Fin (n + n)) (R ⊗[F] E) := reGL finSumFinEquiv κ with hYdef
  have hYs : Y.1.submatrix finSumFinEquiv finSumFinEquiv = κ.1 := by
    simp [hYdef, reGL]
  have hY : cT s Y.1 * dblGram finSumFinEquiv J₀ * Y.1 = dblGram finSumFinEquiv J₀ :=
    (iso_iff s J₀ Y.1).2 (by rw [hYs]; exact hκ0)
  have hk : B * Y * B⁻¹ ∈ HR R σ Q := by
    have := FrameCore.conj_iso s B⁻¹ (FrameCore.conj_back s B hB) hY
    rwa [inv_inv] at this
  let kk : HA R σ Q := ⟨B * Y * B⁻¹, hk⟩
  have hkm : matHom R σ Q kk = B * Y * B⁻¹ := rfl
  have h1 : B⁻¹ * matHom R σ Q kk * B = Y := by rw [hkm]; group
  have h2 : B⁻¹ * (matHom R σ Q kk)⁻¹ * B = Y⁻¹ := by rw [hkm]; group
  have hkK : kk ∈ K := hK kk (fun i j => by rw [h1]; exact hκ1 _ _) (fun i j => by rw [h2]; exact hκ2 _ _)
  refine ⟨⟨g * kk, ?_⟩, kk⁻¹, K.inv_mem hkK, (mul_inv_cancel_right g kk).symm⟩
  refine mem_siegelOf.2 ?_
  rw [map_mul, hkm]
  exact keepsDiag_of_frame (matHom R σ Q g) b Y t (by rw [hYs]; exact hκ)

end GlobalTheory.ThK.Dbl.Hgt

end
end

-- bundled from Development.WeilBound.ThetaLifts.LatticeBasics.Hypotheses2
section
noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {m n : ℕ}


variable (σ) in
abbrev G2 (Y : Spc F E n) : Type := UG (cA σ) (dbl (incM F Y.J))

variable {Y : Spc F E n} {A : Spc F E m}

def mat2 (x : G2 σ Y) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E) := x.1.1


variable (σ Y) in
def rat2 : Subgroup (G2 σ Y) :=
  (Matrix.GeneralLinearGroup.map (n := Fin n ⊕ Fin n) (inclR (F := F) (E := E) (AF F))).range.subgroupOf _

def ht2 (x : G2 σ Y) : ℝ≥0 := heightGL F x.1

def IsPar (p : G2 σ Y) (t : GL (Fin n) (AE F E)) : Prop :=
  mat2 p * diagCols (Fin n) = diagCols (Fin n) * (t : Matrix (Fin n) (Fin n) (AE F E))


variable (σ Y) in
def par2 : Subgroup (G2 σ Y) := Subgroup.closure {p | ∃ t, IsPar p t}

def IsEmb (h h' : UA σ Y.J) (x : G2 σ Y) : Prop := mat2 x = Matrix.fromBlocks (mat h) 0 0 (mat h')

def IsStab2 (B : Base F E) (K : Subgroup (G2 σ Y)) : Prop :=
  ∀ k, k ∈ K ↔ (∀ w, Commute ((mat2 k).map (piInf (B.emb w))) (Matrix.fromBlocks (Y.θ w) 0 0 (-Y.θ w))) ∧
    ∀ z z', z ∈ latHat Y → z' ∈ latHat Y → ∀ k' ∈ ({k, k⁻¹} : Set (G2 σ Y)),
      (mat2 k' *ᵥ Sum.elim z z') ∘ Sum.inl ∈ latHat Y ∧ (mat2 k' *ᵥ Sum.elim z z') ∘ Sum.inr ∈ latHat Y

structure IsHgt (K : Subgroup (G2 σ Y)) (a : G2 σ Y → ℝ) : Prop where
  iwa : ∀ x : G2 σ Y, ∃ p t, IsPar p t ∧ ∃ k ∈ K, x = p * k
  val : ∀ p t, IsPar p t → ∀ k ∈ K, a (p * k) = (absE F E (Matrix.GeneralLinearGroup.det t) : ℝ)

def flat (a : G2 σ Y → ℝ) (f : G2 σ Y → ℂ) (s₀ s : ℂ) (x : G2 σ Y) : ℂ := (a x : ℂ) ^ (s - s₀) * f x

def eisTerm (f : G2 σ Y → ℂ) (x : G2 σ Y) (q : Quotient (QuotientGroup.rightRel ((par2 σ Y).subgroupOf (rat2 σ Y)))) : ℂ :=
  f ((Quotient.out q).1 * x)

structure IsEisCont (f : ℂ → G2 σ Y → ℂ) (U : Set ℂ) (Ê : ℂ → G2 σ Y → ℂ) : Prop where
  isOpen : IsOpen U
  conn : IsPreconnected U
  disc : ∀ s : ℂ, ∀ᶠ s' in 𝓝[≠] s, s' ∈ U
  half : ∃ t : ℝ, ∀ s : ℂ, t < s.re → s ∈ U ∧ ∀ x, HasSum (eisTerm (f s) x) (Ê s x)
  hol : ∀ x, DifferentiableOn ℂ (Ê · x) U
  cont : ContinuousOn (fun y : ℂ × G2 σ Y => Ê y.1 y.2) (U ×ˢ Set.univ)
  grow : ∀ s ∈ U, ∃ (ε C : ℝ) (N : ℕ), 0 < ε ∧ ∀ s' ∈ Metric.ball s ε, ∀ x, ‖Ê s' x‖ ≤ C * (ht2 x : ℝ) ^ N

structure IsDbl (ψ : AddChar (AF F) ℂ) {κ : Type} [Fintype κ]
    (dd : Darboux (symp (R := AF F) (cA σ) (-1) (incM F A.J) (dbl (incM F Y.J))) κ) (χ : Chr F E)
    (om : G2 σ Y →* Module.End ℂ ((κ → AF F) → ℂ)) (S : UA σ A.J →* Module.End ℂ ((κ → AF F) → ℂ))
    (l : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) : Prop where
  rat : ∀ x : Matrix (Fin m) (Fin n ⊕ Fin n) E, ∃ y z : κ → F,
    dd.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))
  weil : IsUWeilSplit (cA σ) (adeleClass F) ψ (-1) (incM F A.J) (dbl (incM F Y.J)) dd χ (diagCols (Fin n)) om
  lin : IsUSplitting (adeleClass F) ψ dd (fun (g : UA σ A.J) x => mat g * x) S
  adm : l ∈ (adeleClass F).adm κ
  kill : ∀ z : Matrix (Fin m) (Fin n) (AE F E), ∀ Φ ∈ schA F κ, l (dd.rho ψ (z * (diagCols (Fin n))ᵀ) Φ) = l Φ
  fix : ∀ g, ∀ Φ ∈ schA F κ, l (S g Φ) = l Φ
  theta : ∀ Φ ∈ schA F κ, HasSum (fun y : Matrix (Fin m) (Fin n) E =>
    l (dd.rho ψ (incM F (Matrix.fromCols y (-y))) Φ)) (thetaSum F Φ)

def EisValueAt (f : ℂ → G2 σ Y → ℂ) (s₀ : ℂ) (val : G2 σ Y → ℂ) : Prop :=
  ∀ x, ∃ e : ℂ → ℂ, MeromorphicOn e Set.univ ∧ (∃ t : ℝ, ∀ s : ℂ, t < s.re → HasSum (eisTerm (f s) x) (e s)) ∧
    AnalyticAt ℂ e s₀ ∧ e s₀ = val x

def SWAniso : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (m n : ℕ) (A : Spc F E m) (Y : Spc F E n) (M : Model σ A Y) r s r' s', B.IsGood σ → 1 ≤ m → 1 ≤ n → A.IsHerm σ B r s →
    min r s = 0 → Y.IsSkew σ B r' s' → M.IsGood B.ψ →
    ∀ χ : Chr F E, IsHecke F E χ → ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ m →
    ∀ dd om S l, IsDblCoord (cA σ) (-1) (incM F A.J) (incM F Y.J) M.co dd → IsDbl (σ := σ) (A := A) (Y := Y) B.ψ dd χ om S l →
    ∀ K a, IsStab2 B K → IsHgt K a → ∀ Φ₁ ∈ PolData B M, ∀ Φ₂ ∈ PolData B M,
      EisValueAt (flat a (fun x => l (om x (boxFun Φ₁ (star Φ₂)))) (((m : ℂ) - n) / 2)) (((m : ℂ) - n) / 2)
        fun x => (if n < m then 1 else 2) * ⨍ g in M.dom, thetaSum F (om x (S g (boxFun Φ₁ (star Φ₂)))) ∂M.μ

structure IsSec (K : Subgroup (G2 σ Y)) (χ : Chr F E) (s₁ : ℂ) (f : G2 σ Y → ℂ) : Prop where
  cont : Continuous f
  law : ∀ p t x, IsPar p t → f (p * x) = (χ (Matrix.GeneralLinearGroup.det t) : ℂ) *
    ((absE F E (Matrix.GeneralLinearGroup.det t) : ℝ) : ℂ) ^ (s₁ + n / 2) * f x
  fin : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : K => fun x => f (x * k.1)))

def IsRegAt (Ê : ℂ → G2 σ Y → ℂ) (s₀ : ℂ) (k : ℕ) : Prop :=
  ∃ (r : ℝ) (H : ℂ → G2 σ Y → ℂ), 0 < r ∧ (∀ s ∈ Metric.ball s₀ r, s ≠ s₀ → ∀ x, H s x = (s - s₀) ^ k * Ê s x) ∧
    (∀ x, DifferentiableOn ℂ (H · x) (Metric.ball s₀ r)) ∧
    ContinuousOn (fun y : ℂ × G2 σ Y => H y.1 y.2) (Metric.ball s₀ r ×ˢ Set.univ) ∧
    ∃ (C : ℝ) (N : ℕ), ∀ s ∈ Metric.ball s₀ r, ∀ x, ‖H s x‖ ≤ C * (ht2 x : ℝ) ^ N

def EisContinues : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (Y : Spc F E n) r s, B.IsGood σ → 1 ≤ n → (Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) →
    ∀ χ : Chr F E, IsHecke F E χ → ∀ b : ℕ, ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ b →
    ∀ K a, IsStab2 (σ := σ) (Y := Y) B K → IsHgt K a → ∀ s₁ f, IsSec K χ s₁ f →
      ∃ U Ê, IsEisCont (flat a f s₁) U Ê ∧ ∀ s₀, ∃ k, IsRegAt Ê s₀ k

end GlobalTheory.ThK.Dbl

end
end

-- bundled from Development.WeilBound.ThetaLifts.LatticeBasics.LocUnrInertN
section
noncomputable section

namespace GlobalTheory.ThK.Dbl.Inert

open MeasureTheory Formalism.UG GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables

theorem prod_fold (T : ℕ → ℂ) (n : ℕ) :
    (∏ i : Fin (n / 2), T (n - 1 - i) * T i) * (if Odd n then T (n / 2) else 1) = ∏ k ∈ Finset.range n, T k := by
  rw [Fin.prod_univ_eq_prod_range (fun i => T (n - 1 - i) * T i), Finset.prod_mul_distrib]
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
  · rw [if_neg (by simp), show 2 * m / 2 = m by omega, two_mul, Finset.prod_range_add, mul_one, mul_comm,
      ← Finset.prod_range_reflect (fun i => T (m + i))]
    exact congrArg _ (Finset.prod_congr rfl fun i hi => congrArg T (by have := Finset.mem_range.1 hi; omega))
  · rw [if_pos (by simp), show (2 * m + 1) / 2 = m by omega, show 2 * m + 1 = m + 1 + m by ring, Finset.prod_range_add,
      Finset.prod_range_succ, ← Finset.prod_range_reflect (fun i => T (m + 1 + i)), mul_assoc, mul_comm]
    exact congrArg _ (Finset.prod_congr rfl fun i hi => congrArg T (by have := Finset.mem_range.1 hi; omega))

theorem triv {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] {ϖ : Lˣ} {σ : L →+* L} {q n : ℕ}
    (hU : IsUnramInv (ϖ : L) σ q) [MeasurableSpace (GU σ n)] [BorelSpace (GU σ n)] (μ : Measure (GU σ n)) [μ.IsHaarMeasure]
    (hμ : μ (KU σ n) = 1) {s : ℂ} (hs : (n : ℝ) / 2 < s.re) {Φ : GD σ n → ℂ} (hΦ : IsSphSec σ q n 1 s Φ) :
    Integrable (fun g => Φ (io1 σ n g)) μ ∧ (∫ g, Φ (io1 σ n g) ∂μ) *
      ∏ i ∈ Finset.range n, (1 - (-1) ^ (n - (i + 1)) * (q : ℂ) ^ (-(2 * s + (i + 1 : ℕ))))⁻¹ =
      ∏ i ∈ Finset.range n, (1 - ((q ^ 2 : ℕ) : ℂ) ^ (-(s + n / 2 - i)))⁻¹ := by
  obtain ⟨α, hα, hw⟩ := isZonal_one hU n
  have h2 : 2 ≤ q := hU.2.2.2.2.2.1
  have hq : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hn : (0 : ℝ) ≤ n := n.cast_nonneg
  have lt : ∀ z : ℂ, z.re < 0 → ‖(q : ℂ) ^ z‖ < 1 := fun z hz => by
    rw [Complex.norm_natCast_cpow_of_pos (by omega)]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast h2) hz
  have y0 : varY q ((1 : Lˣ →* ℂˣ) ϖ) s = (q : ℂ) ^ (-(2 * s + 1)) := by simp [varY]
  have y1 : ∀ i, (q : ℂ) ^ (-(2 * s + 1)) * α i = (q : ℂ) ^ (-(2 * s + 1) + (n - 1 - 2 * (i.val : ℂ))) := fun i => by
    rw [hα, ← Complex.cpow_intCast, ← Complex.cpow_add _ _ hq]; push_cast; rfl
  have y2 : ∀ i, (q : ℂ) ^ (-(2 * s + 1)) / α i = (q : ℂ) ^ (-(2 * s + 1) - (n - 1 - 2 * (i.val : ℂ))) := fun i => by
    rw [hα, ← Complex.cpow_intCast, ← Complex.cpow_sub _ _ hq]; push_cast; rfl
  obtain ⟨h3, h4, -⟩ := (GlobalTheory.CompanionTheory.InertZetaTop.unramDoublingInert L ϖ σ q n hU μ hμ 1 (fun _ _ => rfl) s Φ hΦ α _ hw).1 (by
    rw [y0]
    refine ⟨lt _ (by simp; linarith), fun i => ?_⟩
    have h5 : 2 * (i.val : ℝ) + 1 ≤ n := by exact_mod_cast (by have := i.2; omega : 2 * i.val + 1 ≤ n)
    have h6 : (0 : ℝ) ≤ i.val := Nat.cast_nonneg _
    rw [← norm_mul, ← norm_inv, ← norm_mul, ← div_eq_mul_inv, y1, y2]
    exact ⟨lt _ (by simp; linarith), lt _ (by simp; linarith)⟩)
  simp only [mul_one] at h3 h4
  refine ⟨h3, ?_⟩
  have e : ∀ z : ℂ, ((q ^ 2 : ℕ) : ℂ) ^ z = (q : ℂ) ^ (2 * z) := fun z => by
    rw [Nat.cast_pow, ← Complex.natCast_cpow_natCast_mul]; rfl
  rw [h4, closedForm, y0, ← prod_fold (fun i => (1 - ((q ^ 2 : ℕ) : ℂ) ^ (-(s + n / 2 - i)))⁻¹), mul_assoc (Finset.prod _ _), mul_right_comm,
    ← Finset.prod_range_reflect, ← Finset.prod_mul_distrib, Finset.prod_eq_one, one_mul]
  · congr 1
    · refine Finset.prod_congr rfl fun i _ => ?_
      have := i.2
      rw [y1, y2, e, e, Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
      congr 4 <;> push_cast <;> ring
    · split_ifs with h
      · obtain ⟨m, rfl⟩ := h
        rw [e, show (2 * m + 1) / 2 = m by omega]
        congr 3; push_cast; ring
      · rfl
  · intro i hi
    have hi := Finset.mem_range.1 hi
    have e2 : (-(q : ℂ)) ^ (n - 1 - i) * varX q n ((1 : Lˣ →* ℂˣ) ϖ) s = (-1) ^ (n - (i + 1)) * (q : ℂ) ^ (-(2 * s + (i + 1 : ℕ))) := by
      rw [neg_pow, varX, MonoidHom.one_apply, Units.val_one, one_mul, mul_assoc, ← Complex.cpow_natCast (q : ℂ),
        ← Complex.cpow_add _ _ hq, Nat.cast_sub (by omega), Nat.cast_sub (by omega), show n - 1 - i = n - (i + 1) by omega]
      congr 2; push_cast; ring
    rw [e2]
    refine mul_inv_cancel₀ (sub_ne_zero.2 fun h => ?_)
    have h6 : (0 : ℝ) ≤ i := Nat.cast_nonneg _
    have := lt (-(2 * s + (i + 1 : ℕ))) (by simp; linarith)
    have h7 := congrArg norm h
    rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul] at h7
    exact this.ne h7.symm

end GlobalTheory.ThK.Dbl.Inert

end
end

-- bundled from Development.WeilBound.ThetaLifts.LatticeBasics.SchToPol
section
noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

def SchToPol : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → min r s = 0 → (∀ Φ ∈ PolData B M, M.I om Φ = 0) → ∀ Φ ∈ schA F _, M.I om Φ = 0

def PolSch : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ Φ ∈ PolData B M, Φ ∈ schA F _

def ToSo : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → G.q = 0 →
    ∀ Φ' ∈ PolData B G.M', ∃ Ψ ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁, G.M'.I om' Ψ = G.M'.I om' Φ'

def LeviEx : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (d d₁ : ℕ) (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ r s : ℕ), B.IsGood σ → W.IsSkew σ B r s →
    H'.IsAdapted σ B W W₁ i₀ i₁ → ∀ h₁ : UA σ W₁.J, ∃ m : UA σ W.J, IsLevi H' 1 h₁ m

end GlobalTheory.ThK.Dbl

end
end

