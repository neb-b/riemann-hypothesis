module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0043
public import ReciprocityTheory.SemistableReduction.Bundle0025
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1234
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDefiniteDatumGoodObj
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0046
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0019
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.GeomIntSelf
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0132

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExchangeIndependentCompletion
section
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

namespace GlobalTheory

theorem exchange_independent_completion (E M : Type) [Field E] [AddCommGroup M] [Module E M]
    (n d : ℕ) (v : Fin n → M) (w : Fin d → M) (hv : LinearIndependent E v)
    (hw : LinearIndependent E w) (hvw : ∀ k, v k ∈ Submodule.span E (Set.range w)) :
    ∃ K : Finset (Fin d), n + K.card = d ∧ LinearIndependent E (Sum.elim v fun k : K => w k) := by
  classical
  obtain ⟨b, hbt, hsb, htb, hb⟩ := exists_linearIndepOn_id_extension
    (s := Set.range v) (t := Set.range v ∪ Set.range w) (K := E)
    hv.linearIndepOn_id Set.subset_union_left
  let K : Finset (Fin d) := Finset.univ.filter (fun k => w k ∈ b ∧ w k ∉ Set.range v)
  let u : Fin n ⊕ K → M := Sum.elim v fun k : K => w k
  have hK : ∀ k : K, w k ∈ b ∧ w k ∉ Set.range v := fun k => (Finset.mem_filter.1 k.2).2
  have hu_inj : Function.Injective u := by
    rintro (i | i) (j | j) h
    · simp only [u, Sum.elim_inl] at h; rw [hv.injective h]
    · simp only [u, Sum.elim_inl, Sum.elim_inr] at h; exact absurd ⟨i, h⟩ (hK j).2
    · simp only [u, Sum.elim_inl, Sum.elim_inr] at h; exact absurd ⟨j, h.symm⟩ (hK i).2
    · simp only [u, Sum.elim_inr] at h; rw [Subtype.ext (hw.injective h)]
  have hu_mem : ∀ x, u x ∈ b := by
    rintro (i | i)
    · exact hsb ⟨i, rfl⟩
    · exact (hK i).1
  have hu_range : Set.range u = b := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩; exact hu_mem x
    · intro x hx
      by_cases hxv : x ∈ Set.range v
      · obtain ⟨i, rfl⟩ := hxv; exact ⟨Sum.inl i, rfl⟩
      · rcases hbt hx with ⟨i, rfl⟩ | ⟨k, rfl⟩
        · exact absurd ⟨i, rfl⟩ hxv
        · have hk : k ∈ K := Finset.mem_filter.2 ⟨Finset.mem_univ _, hx, hxv⟩
          exact ⟨Sum.inr ⟨k, hk⟩, rfl⟩
  have hli : LinearIndependent E u :=
    LinearIndependent.comp (show LinearIndependent E (fun x : b => (x : M)) from hb) (fun x => (⟨u x, hu_mem x⟩ : b)) (fun x y h => hu_inj (congrArg Subtype.val h))
  refine ⟨K, ?_, hli⟩
  have hspan : Submodule.span E (Set.range u) = Submodule.span E (Set.range w) := by
    apply le_antisymm
    · rw [Submodule.span_le, hu_range]
      intro x hx
      rcases hbt hx with ⟨i, rfl⟩ | ⟨k, rfl⟩
      · exact hvw i
      · exact Submodule.subset_span ⟨k, rfl⟩
    · rw [Submodule.span_le, hu_range]; exact Set.subset_union_right.trans htb
  have h1 := finrank_span_eq_card hli
  have h2 := finrank_span_eq_card hw
  rw [hspan, h2] at h1
  simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_coe] at h1
  omega

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicSkewHermitianCorrectionOfLocalSoluti
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.TransportBack

open Matrix

theorem map_mul_gen {R S Fh : Type*} [CommRing R] [CommRing S] [FunLike Fh R S]
    [NonUnitalRingHomClass Fh R S] (f : Fh) {m k p : Type*} [Fintype k]
    (X : Matrix m k R) (Y : Matrix k p R) : (X * Y).map f = X.map f * Y.map f := by
  ext i j; simp [Matrix.mul_apply, map_sum, map_mul]

theorem map_mulVec_gen {R S Fh : Type*} [CommRing R] [CommRing S] [FunLike Fh R S]
    [NonUnitalRingHomClass Fh R S] (f : Fh) {m k : Type*} [Fintype k]
    (X : Matrix m k R) (a : k → R) : X.map f *ᵥ (fun i => f (a i)) = fun i => f ((X *ᵥ a) i) := by
  ext i; simp [Matrix.mulVec, dotProduct, map_sum, map_mul]

theorem map_add_gen {R S Fh : Type*} [CommRing R] [CommRing S] [FunLike Fh R S]
    [NonUnitalRingHomClass Fh R S] (f : Fh) {m k : Type*}
    (X Y : Matrix m k R) : (X + Y).map f = X.map f + Y.map f := by
  ext i j; simp

theorem map_one_eq {R S : Type*} [CommRing R] [CommRing S] (ι : R →ₙ+* S) {n : Type*} [DecidableEq n] :
    (1 : Matrix n n R).map ι = ι 1 • (1 : Matrix n n S) := by
  ext i j; by_cases h : i = j <;> simp [Matrix.one_apply, h]

theorem map_neg_one_eq {R S : Type*} [CommRing R] [CommRing S] (ι : R →ₙ+* S) {n : Type*} [DecidableEq n] :
    (-1 : Matrix n n R).map ι = -(ι 1 • (1 : Matrix n n S)) := by
  ext i j; by_cases h : i = j <;> simp [Matrix.one_apply, h]

theorem assoc_a {R : Type*} [CommRing R] {a b c d e : Type*} [Fintype b] [Fintype c] [Fintype d]
    (A : Matrix a b R) (B : Matrix b c R) (C : Matrix c d R) (D : Matrix d e R) :
    A * B * C * D = A * (B * (C * D)) := by simp only [Matrix.mul_assoc]

theorem assoc_b {R : Type*} [CommRing R] {a b c d : Type*} [Fintype b] [Fintype c] [Fintype d]
    (A : Matrix a b R) (B : Matrix b c R) (C : Matrix c d R) (P₁ Y Q₁ P₂ : Matrix d d R) :
    A * B * C * (P₁ * Y * Q₁) * P₂ = A * (B * (C * (P₁ * (Y * (Q₁ * P₂))))) := by
  simp only [Matrix.mul_assoc]

theorem smul_mid_of {R : Type*} [CommRing R] {a b d : Type*} [Fintype b] [DecidableEq b]
    (s : R) (A : Matrix a b R) (B : Matrix b b R) (C : Matrix b d R) (h : s • B = s • 1) :
    s • (A * B * C) = s • (A * C) := by
  rw [← Matrix.smul_mul, ← Matrix.mul_smul, h, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]

theorem smul_last_of {R : Type*} [CommRing R] {a b c d e : Type*} [Fintype b] [Fintype c] [Fintype d]
    (s : R) (A : Matrix a b R) (B : Matrix b c R) (C : Matrix c d R) (Z : Matrix d e R) (h : s • Z = 0) :
    s • (A * B * C * Z) = 0 := by
  rw [← Matrix.mul_smul, h, Matrix.mul_zero]

end GlobalTheory.TransportBack

namespace GlobalTheory.TransportBack
open Matrix

theorem transport_back : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (n : ℕ) (X : Spc F E n) (v : Pl (F := F)) (O : Type) [CommRing O] (c : O →+* O) (ι : O →ₙ+* AE F E)
    (P Q : Matrix (Fin n) (Fin n) (AE F E)) (JL : Matrix (Fin n) (Fin n) O),
    At (evFin F v) (ι 1) → (∀ y : AE F E, At (evFin F v) y → ι 1 * y = y) → (∀ x, cA σ (ι x) = ι (c x)) →
    P * Q = ι 1 • (1 : Matrix (Fin n) (Fin n) (AE F E)) → Q * P = ι 1 • (1 : Matrix (Fin n) (Fin n) (AE F E)) →
    ι 1 • P = P → ι 1 • Q = Q → Pᵀ * incM F X.J * P.map (cA σ) = JL.map ι →
    (∀ z : Fin n → AE F E, z ∈ GlobalTheory.InertSph.latAt X v ↔ ∃ a : Fin n → O, z = P *ᵥ fun i => ι (a i)) →
    ∀ (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) (G : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) O)
      (ZL : Matrix (Fin n) (Fin n) O),
    At (evFin F v) (M - 1) → M * Matrix.fromBlocks P 0 0 P = Matrix.fromBlocks P 0 0 P * G.map ι →
    ZLᵀ * JL + JL * ZL.map c = 0 →
    IsUnit (((Matrix.fromRows (1 : Matrix (Fin n) (Fin n) O) (-1 : Matrix (Fin n) (Fin n) O))ᵀ : Matrix (Fin n) (Fin n ⊕ Fin n) O) * G * (Matrix.fromRows (1 : Matrix (Fin n) (Fin n) O) (-1 : Matrix (Fin n) (Fin n) O) : Matrix (Fin n ⊕ Fin n) (Fin n) O) +
        ((Matrix.fromRows (1 : Matrix (Fin n) (Fin n) O) (-1 : Matrix (Fin n) (Fin n) O))ᵀ : Matrix (Fin n) (Fin n ⊕ Fin n) O) * G * (Matrix.fromRows (1 : Matrix (Fin n) (Fin n) O) (1 : Matrix (Fin n) (Fin n) O) : Matrix (Fin n ⊕ Fin n) (Fin n) O) * ZL).det →
    ∃ Z : Matrix (Fin n) (Fin n) (AE F E), At (evFin F v) Z ∧
      (∀ z ∈ GlobalTheory.InertSph.latAt X v, Z *ᵥ z ∈ GlobalTheory.InertSph.latAt X v) ∧
      Zᵀ * incM F X.J + incM F X.J * Z.map (cA σ) = 0 ∧
      IsUnit ((GlobalTheory.DblVac.antiCols (F := F) (E := E) n)ᵀ * M * GlobalTheory.DblVac.antiCols n +
        (GlobalTheory.DblVac.antiCols (F := F) (E := E) n)ᵀ * M * (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E)) * Z).det ∧
      ∀ z ∈ GlobalTheory.InertSph.latAt X v,
        ((GlobalTheory.DblVac.antiCols (F := F) (E := E) n)ᵀ * M * GlobalTheory.DblVac.antiCols n +
          (GlobalTheory.DblVac.antiCols (F := F) (E := E) n)ᵀ * M * (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E)) * Z)⁻¹ *ᵥ z ∈
          GlobalTheory.InertSph.latAt X v := by
  intro F E _ _ _ _ _ σ n X v O _ c ι P Q JL hAe he hc hPQ hQP heP heQ hJ hlat M G ZL hM hMG hZL hN
  have heι : ∀ x, ι 1 * ι x = ι x := fun x => by rw [← map_mul, one_mul]
  have hιe : ∀ x, ι x * ι 1 = ι x := fun x => by rw [← map_mul, mul_one]
  have hee : ι 1 * ι 1 = ι 1 := heι 1
  have hce : cA σ (ι 1) = ι 1 := by rw [hc, map_one]
  have hmapE : ∀ {m k : Type} (Y : Matrix m k O), ι 1 • Y.map ι = Y.map ι := by
    intro m k Y; ext i j; simp [heι]
  have hePY : ∀ {k : Type} [Fintype k] (Y : Matrix (Fin n) k (AE F E)), ι 1 • (P * Y) = P * Y := by
    intro k _ Y; rw [← Matrix.smul_mul, heP]
  have hZP : P * ZL.map ι * Q * P = P * ZL.map ι := by
    rw [Matrix.mul_assoc, hQP, Matrix.mul_smul, Matrix.mul_one, hePY]
  have hvec : ∀ a : Fin n → O, Q *ᵥ (P *ᵥ fun i => ι (a i)) = fun i => ι (a i) := by
    intro a; rw [Matrix.mulVec_mulVec, hQP, Matrix.smul_mulVec, Matrix.one_mulVec]
    ext i; simp [heι]

  have hAtZ : At (evFin F v) (P * ZL.map ι * Q) := by
    intro u hu
    have hu' : u • Q = 0 := by rw [← heQ, ← smul_assoc, hAe u hu, zero_smul]
    rw [← Matrix.mul_smul, hu', Matrix.mul_zero]

  have hlatZ : ∀ z ∈ GlobalTheory.InertSph.latAt X v, (P * ZL.map ι * Q) *ᵥ z ∈ GlobalTheory.InertSph.latAt X v := by
    intro z hz
    obtain ⟨a, rfl⟩ := (hlat z).1 hz
    refine (hlat _).2 ⟨ZL *ᵥ a, ?_⟩
    rw [Matrix.mulVec_mulVec, hZP, ← Matrix.mulVec_mulVec, map_mulVec_gen]

  have hPcQc : P.map (cA σ) * Q.map (cA σ) = ι 1 • (1 : Matrix (Fin n) (Fin n) (AE F E)) := by
    rw [← map_mul_gen, hPQ]; ext i j; by_cases h : i = j <;> simp [Matrix.one_apply, h, hce]
  have h1 : Pᵀ * incM F X.J = JL.map ι * Q.map (cA σ) := by
    calc Pᵀ * incM F X.J = ι 1 • (Pᵀ * incM F X.J) := by
            rw [← Matrix.smul_mul, ← Matrix.transpose_smul, heP]
      _ = Pᵀ * incM F X.J * (P.map (cA σ) * Q.map (cA σ)) := by
            rw [hPcQc, Matrix.mul_smul, Matrix.mul_one]
      _ = JL.map ι * Q.map (cA σ) := by rw [← Matrix.mul_assoc, hJ]
  have hPc : ι 1 • P.map (cA σ) = P.map (cA σ) := by
    conv_rhs => rw [← heP]
    ext i j; simp [hce]
  have h2 : incM F X.J * P.map (cA σ) = Qᵀ * JL.map ι := by
    calc incM F X.J * P.map (cA σ) = ι 1 • (incM F X.J * P.map (cA σ)) := by
            rw [← Matrix.mul_smul, hPc]
      _ = (P * Q)ᵀ * incM F X.J * P.map (cA σ) := by
            rw [hPQ, Matrix.transpose_smul, Matrix.transpose_one, Matrix.smul_mul, Matrix.smul_mul,
              Matrix.one_mul]
      _ = Qᵀ * JL.map ι := by
            rw [Matrix.transpose_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Pᵀ, hJ]
  have hmapc : (ZL.map ι).map (cA σ) = (ZL.map c).map ι := by
    rw [Matrix.map_map, Matrix.map_map]; congr 1; funext x; exact hc x
  have hJZ : (P * ZL.map ι * Q)ᵀ * incM F X.J + incM F X.J * (P * ZL.map ι * Q).map (cA σ) = 0 := by
    have hz0 : (ZLᵀ * JL + JL * ZL.map c).map ι = 0 := by rw [hZL]; ext i j; simp
    rw [map_add_gen, map_mul_gen, map_mul_gen, Matrix.transpose_map] at hz0
    rw [map_mul_gen, map_mul_gen, hmapc, Matrix.transpose_mul, Matrix.transpose_mul]
    simp only [Matrix.mul_assoc]
    rw [h1, ← Matrix.mul_assoc (incM F X.J), h2]
    calc _ = Qᵀ * ((ZL.map ι)ᵀ * JL.map ι + JL.map ι * (ZL.map c).map ι) * Q.map (cA σ) := by
          simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
      _ = 0 := by rw [hz0]; simp

  set N := ((Matrix.fromRows (1 : Matrix (Fin n) (Fin n) O) (-1 : Matrix (Fin n) (Fin n) O))ᵀ : Matrix (Fin n) (Fin n ⊕ Fin n) O) * G * (Matrix.fromRows (1 : Matrix (Fin n) (Fin n) O) (-1 : Matrix (Fin n) (Fin n) O) : Matrix (Fin n ⊕ Fin n) (Fin n) O) +
        ((Matrix.fromRows (1 : Matrix (Fin n) (Fin n) O) (-1 : Matrix (Fin n) (Fin n) O))ᵀ : Matrix (Fin n) (Fin n ⊕ Fin n) O) * G * (Matrix.fromRows (1 : Matrix (Fin n) (Fin n) O) (1 : Matrix (Fin n) (Fin n) O) : Matrix (Fin n ⊕ Fin n) (Fin n) O) * ZL with hNdef
  set K := (GlobalTheory.DblVac.antiCols (F := F) (E := E) n)ᵀ * M * GlobalTheory.DblVac.antiCols n +
        (GlobalTheory.DblVac.antiCols (F := F) (E := E) n)ᵀ * M * (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E)) * (P * ZL.map ι * Q) with hK
  have hNab : (Matrix.fromRows (1 : Matrix (Fin n) (Fin n) O) (-1 : Matrix (Fin n) (Fin n) O)).map ι = Matrix.fromRows (ι 1 • (1 : Matrix (Fin n) (Fin n) (AE F E))) (-(ι 1 • 1)) := by
    rw [Matrix.fromRows_map, map_one_eq, map_neg_one_eq]
  have hDel : (Matrix.fromRows (1 : Matrix (Fin n) (Fin n) O) (1 : Matrix (Fin n) (Fin n) O)).map ι = Matrix.fromRows (ι 1 • (1 : Matrix (Fin n) (Fin n) (AE F E))) (ι 1 • 1) := by
    rw [Matrix.fromRows_map, map_one_eq]
  have hanti : GlobalTheory.DblVac.antiCols (F := F) (E := E) n * P = Matrix.fromBlocks P 0 0 P * (Matrix.fromRows (1 : Matrix (Fin n) (Fin n) O) (-1 : Matrix (Fin n) (Fin n) O)).map ι := by
    rw [hNab, GlobalTheory.DblVac.antiCols, Matrix.fromRows_mul, Matrix.fromBlocks_mul_fromRows]
    simp [Matrix.mul_smul, heP]
  have hdiag : ∀ Y : Matrix (Fin n) (Fin n) (AE F E), (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E)) * (P * Y) = Matrix.fromBlocks P 0 0 P * ((Matrix.fromRows (1 : Matrix (Fin n) (Fin n) O) (1 : Matrix (Fin n) (Fin n) O)).map ι * Y) := by
    intro Y
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hDel, diagCols, Matrix.fromRows_mul, Matrix.fromBlocks_mul_fromRows]
    simp [Matrix.mul_smul, heP]
  have hantiT : ∀ {k : Type} [Fintype k] (Y : Matrix (Fin n ⊕ Fin n) k (AE F E)), (GlobalTheory.DblVac.antiCols (F := F) (E := E) n)ᵀ * (Matrix.fromBlocks P 0 0 P * Y) = P * (((Matrix.fromRows (1 : Matrix (Fin n) (Fin n) O) (-1 : Matrix (Fin n) (Fin n) O)).map ι)ᵀ * Y) := by
    intro k _ Y
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hNab, GlobalTheory.DblVac.antiCols, Matrix.transpose_fromRows, Matrix.transpose_fromRows,
      Matrix.fromCols_mul_fromBlocks, Matrix.mul_fromCols]
    simp [Matrix.mul_smul, heP]
  have hMG' : ∀ {k : Type} [Fintype k] (Y : Matrix (Fin n ⊕ Fin n) k (AE F E)), M * (Matrix.fromBlocks P 0 0 P * Y) = Matrix.fromBlocks P 0 0 P * (G.map ι * Y) := by
    intro k _ Y; rw [← Matrix.mul_assoc, hMG, Matrix.mul_assoc]
  have hQPι : ZL.map ι * (Q * P) = ZL.map ι := by rw [hQP, Matrix.mul_smul, Matrix.mul_one, hmapE]
  have hKP : K * P = P * N.map ι := by
    rw [hK, Matrix.add_mul]
    refine (congrArg₂ (· + ·) (assoc_a _ _ _ _) (assoc_b _ _ _ _ _ _ _)).trans ?_
    rw [hanti, hQPι, hdiag, hMG', hMG', hantiT, hantiT, hNdef]
    simp only [map_add_gen, map_mul_gen, Matrix.transpose_map, Matrix.mul_add, Matrix.mul_assoc]

  have hN1 : N * N⁻¹ = 1 := Matrix.mul_nonsing_inv N hN
  have h2inv : algebraMap F (AE F E) 2⁻¹ * 2 = 1 := by
    rw [← map_ofNat (algebraMap F (AE F E)) 2, ← map_mul, inv_mul_cancel₀ two_ne_zero, map_one]
  have hMe : ι 1 • (M - 1) = M - 1 := by
    ext i j
    rw [Matrix.smul_apply, smul_eq_mul]
    apply he
    intro u hu
    have := congrFun (congrFun (hM u hu) i) j
    simpa using this
  have hM1 : (1 - ι 1) • M = (1 - ι 1) • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) := by
    rw [sub_smul, one_smul, sub_smul, one_smul, ← sub_eq_zero,
      show M - ι 1 • M - (1 - ι 1 • 1) = (M - 1) - (ι 1 • M - ι 1 • 1) by abel, ← smul_sub, hMe, sub_self]
  have hZe : (1 - ι 1) • (P * ZL.map ι * Q) = 0 := by
    rw [sub_smul, one_smul, ← Matrix.smul_mul, ← Matrix.smul_mul, heP, sub_self]
  have hAA : (GlobalTheory.DblVac.antiCols (F := F) (E := E) n)ᵀ * GlobalTheory.DblVac.antiCols n = (2 : AE F E) • (1 : Matrix (Fin n) (Fin n) (AE F E)) := by
    rw [GlobalTheory.DblVac.antiCols, Matrix.transpose_fromRows]
    refine (Matrix.fromCols_mul_fromRows _ _ _ _).trans ?_
    simp [two_smul]
  have hKe : (1 - ι 1) • K = (1 - ι 1) • ((2 : AE F E) • (1 : Matrix (Fin n) (Fin n) (AE F E))) := by
    rw [hK, smul_add]
    refine (congrArg₂ (· + ·) (smul_mid_of _ _ _ _ hM1) (smul_last_of _ _ _ _ _ hZe)).trans ?_
    rw [add_zero]
    exact congrArg _ hAA
  set R := (algebraMap F (AE F E) 2⁻¹ * (1 - ι 1)) • (1 : Matrix (Fin n) (Fin n) (AE F E)) + P * N⁻¹.map ι * Q with hR
  have hKR : K * R = 1 := by
    have hsec : K * (P * N⁻¹.map ι * Q) = ι 1 • (1 : Matrix (Fin n) (Fin n) (AE F E)) := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hKP, Matrix.mul_assoc P, ← map_mul_gen, hN1, map_one_eq,
        Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hPQ, smul_smul, hee]
    rw [hR, Matrix.mul_add, hsec, Matrix.mul_smul, Matrix.mul_one, mul_smul, hKe, smul_smul, smul_smul, ← add_smul,
      show algebraMap F (AE F E) 2⁻¹ * (1 - ι 1) * 2 + ι 1 = (1 - ι 1) * (algebraMap F (AE F E) 2⁻¹ * 2) + ι 1 by ring,
      h2inv, mul_one, sub_add_cancel, one_smul]
  have hPz : ∀ w : Fin n → AE F E, (1 - ι 1) • (P *ᵥ w) = 0 := by
    intro w; rw [← Matrix.smul_mulVec, sub_smul, one_smul, heP, sub_self, Matrix.zero_mulVec]
  refine ⟨P * ZL.map ι * Q, hAtZ, hlatZ, hJZ, Matrix.isUnit_det_of_right_inverse hKR, ?_⟩
  intro z hz
  obtain ⟨a, rfl⟩ := (hlat z).1 hz
  rw [Matrix.inv_eq_right_inv hKR]
  refine (hlat _).2 ⟨N⁻¹ *ᵥ a, ?_⟩
  rw [hR, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, mul_smul, hPz, smul_zero, zero_add,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hvec, map_mulVec_gen]

end GlobalTheory.TransportBack
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineRingHomPairOfSpecializes
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

theorem asIdeal_spMap_field {B k : Type} [CommRing B] [Field k] (φ : B →+* k) (u : Sp k) :
    ((spMap φ).base u).asIdeal = RingHom.ker φ := by
  have hu : u.asIdeal = ⊥ := @Ideal.eq_bot_of_prime _ _ _ u.isPrime
  rw [RingHom.ker_eq_comap_bot, ← hu]
  rw [spMap, Spec.map_base]
  rfl

theorem exists_ringHom_pair_of_specializes {X : Scheme.{0}} {k k' : Type} [Field k] [Field k'] (x : Sp k ⟶ X)
    (x' : Sp k' ⟶ X) (u : Sp k) (u' : Sp k') (h : x'.base u' ⤳ x.base u) :
    ∃ (B : Type) (_ : CommRing B) (g : B →+* k) (g' : B →+* k') (ρ : Sp B ⟶ X),
      RingHom.ker g' ≤ RingHom.ker g ∧ spMap g ≫ ρ = x ∧ spMap g' ≫ ρ = x' := by
  obtain ⟨V, hV, hxV, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens)
    (show x.base u ∈ (⊤ : X.Opens) from trivial)
  have hV' : IsAffineOpen V := hV
  have hx'V : x'.base u' ∈ V := h.mem_open V.isOpen hxV
  have hsub : Set.range x.base ⊆ Set.range hV'.fromSpec := by
    rw [hV'.range_fromSpec]
    rintro _ ⟨v, rfl⟩
    rwa [Subsingleton.elim v u]
  have hsub' : Set.range x'.base ⊆ Set.range hV'.fromSpec := by
    rw [hV'.range_fromSpec]
    rintro _ ⟨v, rfl⟩
    rwa [Subsingleton.elim v u']
  let xV := IsOpenImmersion.lift hV'.fromSpec x hsub
  let x'V := IsOpenImmersion.lift hV'.fromSpec x' hsub'
  have hfx : xV ≫ hV'.fromSpec = x := IsOpenImmersion.lift_fac _ _ _
  have hfx' : x'V ≫ hV'.fromSpec = x' := IsOpenImmersion.lift_fac _ _ _
  have e1 : spMap (Spec.preimage xV).hom = xV := Spec.map_preimage xV
  have e2 : spMap (Spec.preimage x'V).hom = x'V := Spec.map_preimage x'V
  refine ⟨Γ(X, V), inferInstance, (Spec.preimage xV).hom, (Spec.preimage x'V).hom, hV'.fromSpec, ?_, ?_, ?_⟩
  · rw [← asIdeal_spMap_field _ u, ← asIdeal_spMap_field _ u']
    refine (PrimeSpectrum.le_iff_specializes ((spMap (Spec.preimage x'V).hom).base u')
      ((spMap (Spec.preimage xV).hom).base u)).mpr ?_
    rw [e1, e2]
    have h2 : hV'.fromSpec (x'V u') ⤳ hV'.fromSpec (xV u) := by
      rw [← hfx, ← hfx'] at h
      simpa only [Scheme.Hom.comp_apply] using h
    exact (hV'.fromSpec.isOpenEmbedding.isInducing.specializes_iff).mp h2
  · rw [e1]; exact hfx
  · rw [e2]; exact hfx'

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAppellHumbertUnimodularRiemannForm
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZM GlobalTheory.KeyFam

namespace GlobalTheory.PolUnif

theorem hermForm_self_im {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian) (x : Fin g → ℂ) :
    (hermForm Hm x x).im = 0 := by
  have h := hH.im_star_dotProduct_mulVec_self (star x)
  rw [star_star] at h
  exact h

theorem exists_unif_riemannForm : ∀ (h : ℕ) (P : Out.PolAV (Sp ℂ)), P.g = h → ∃ (u : HolUnif P.A P.L h) (Hm : Matrix (Fin h) (Fin h) ℂ) (χ : u.Λ → ℂ) (Ef : LinearMap.BilinForm ℤ u.Λ), u.IsAH Hm χ ∧ (∀ x y : u.Λ, (Ef x y : ℝ) = (hermForm Hm x y).im) ∧ Function.Bijective Ef ∧ (∀ x, Ef x x = 0) ∧ Module.Free ℤ u.Λ ∧ Module.Finite ℤ u.Λ ∧ Module.finrank ℤ u.Λ = 2 * h ∧ ∀ (n : ℕ) (x y : u.Λ) (e : ℂˣ), 0 < n → (e : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (Ef x y : ℂ) / n) → Out.WeilIs P.A P.L n (u.ex ((n : ℂ)⁻¹ • (x : Fin h → ℂ))) (u.ex ((n : ℂ)⁻¹ • (y : Fin h → ℂ))) (unitOn e) := by
  intro h P hg
  subst hg
  obtain ⟨rig, hrig⟩ := P.rigid
  obtain ⟨u, Hm, χ, Ef, hAH, -, -, -, -, -, hE, hbij, hW⟩ := GlobalTheory.thetaUnifAV_all P rig hrig
  haveI : DiscreteTopology u.Λ := u.discrete
  haveI : IsZLattice ℝ u.Λ := ⟨u.full⟩
  refine ⟨u, Hm, χ, Ef, hAH, hE, hbij, fun x => ?_, ZLattice.module_free ℝ u.Λ, ZLattice.module_finite ℝ u.Λ, ?_, hW⟩
  · have h1 := hE x x
    rw [hermForm_self_im hAH.1] at h1
    exact_mod_cast h1
  · rw [ZLattice.rank ℝ u.Λ, Module.finrank_pi_fintype]
    simp [mul_comm]

end GlobalTheory.PolUnif
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasisChoiceDetNeZero
section
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

namespace GlobalTheory

theorem exists_basis_choice_det_ne_zero : ∀ (F E A A' : Type) [Field F] [Field E] [Algebra F E] [AddCommGroup A] [Module F A] [AddCommGroup A'] [Module E A'] (ι : A →ₛₗ[algebraMap F E] A') (V : Submodule F A) (r δ : ℕ) (bb : Module.Basis (Fin r) F V) (res : A' →ₗ[E] (Fin δ → E)), (Submodule.span E (ι '' (V : Set A))).map res = ⊤ → ∃ σ : Fin δ → Fin r, (Matrix.of fun p' p => res (ι (bb (σ p))) p').det ≠ 0 := by
  intro F E A A' _ _ _ _ _ _ _ ι V r δ bb res h
  have hsub : ι '' (V : Set A) ⊆ Submodule.span E (Set.range fun i => ι (bb i)) := by
    rintro _ ⟨x, hx, rfl⟩
    have hx' : x = ∑ i, bb.repr ⟨x, hx⟩ i • ((bb i : V) : A) := by
      have := congrArg Subtype.val (bb.sum_repr ⟨x, hx⟩)
      simp only [Submodule.coe_sum, Submodule.coe_smul] at this
      exact this.symm
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hx', map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [LinearMap.map_smulₛₗ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hspan : Submodule.span E (Set.range fun i => res (ι (bb i))) = ⊤ := by
    have h1 := Submodule.map_mono (f := res) (Submodule.span_le.mpr hsub)
    rw [h, Submodule.map_span, ← Set.range_comp] at h1
    exact eq_top_iff.mpr h1
  obtain ⟨b, hb, hbspan, hli⟩ := exists_linearIndependent E (Set.range fun i => res (ι (bb i)))
  let bs := Module.Basis.mk hli (by rw [Subtype.range_coe, hbspan, hspan])
  let e := bs.indexEquiv (Pi.basisFun E (Fin δ))
  have hmem : ∀ p, ((e.symm p : b) : Fin δ → E) ∈ Set.range fun i => res (ι (bb i)) :=
    fun p => hb (e.symm p).2
  choose σ hσ using hmem
  refine ⟨σ, ?_⟩
  have hli2 : LinearIndependent E (fun p => res (ι (bb (σ p)))) := by
    have : (fun p => res (ι (bb (σ p)))) = ((↑) : b → Fin δ → E) ∘ e.symm := funext fun p => hσ p
    rw [this]
    exact hli.comp _ e.symm.injective
  have hunit : IsUnit (Matrix.of fun p' p => res (ι (bb (σ p))) p') := by
    rw [← Matrix.linearIndependent_cols_iff_isUnit]
    exact hli2
  exact ((Matrix.isUnit_iff_isUnit_det _).mp hunit).ne_zero

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBlockWordOfTypeProd
section
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

namespace GlobalTheory.HSShort

theorem words_of_type (D t : ℕ) (α : Fin D →₀ ℕ) (hα : α.degree ≤ t) :
    ∃ β : Fin t → Fin (D + 1), (∀ i : Fin D, (Finset.univ.filter fun q => β q = i.castSucc).card = α i) ∧
      (α.degree = t → ∀ q, β q ≠ Fin.last D) ∧
      ∀ (M : Type) [Monoid M] (f : Fin (D + 1) → M),
        (List.ofFn fun q => f (β q)).prod =
          (List.ofFn fun i : Fin D => f i.castSucc ^ α i).prod * f (Fin.last D) ^ (t - α.degree) := by
  classical
  have hdeg : α.degree = ∑ i, α i := Finsupp.degree_eq_sum α
  set L : List (Fin (D + 1)) :=
    (List.ofFn fun i : Fin D => List.replicate (α i) i.castSucc).flatten ++
      List.replicate (t - α.degree) (Fin.last D) with hL
  have hlen : L.length = t := by
    simp only [hL, List.length_append, List.length_flatten, List.map_ofFn, List.length_replicate,
      List.sum_ofFn, Function.comp_def]
    omega
  refine ⟨fun q => L.get (Fin.cast hlen.symm q), ?_⟩
  set β : Fin t → Fin (D + 1) := fun q => L.get (Fin.cast hlen.symm q) with hβ
  have hofFn : List.ofFn β = L := by
    apply List.ext_get
    · simp [hlen]
    · intro n h1 h2
      simp [hβ]
  have hcount : ∀ x, (Finset.univ.filter fun q => β q = x).card = L.count x := by
    intro x
    rw [← hofFn, ← Multiset.coe_count, ← Fin.univ_val_map, Multiset.count_map, Finset.card_def,
      Finset.filter_val]
    congr 1
    apply Multiset.filter_congr
    intro a _
    exact eq_comm
  refine ⟨?_, ?_, ?_⟩
  · intro i
    rw [hcount]
    simp [hL, List.count_flatten, List.count_replicate, Function.comp_def, Fin.castSucc_inj, List.sum_ofFn,
      (Fin.castSucc_ne_last i).symm]
  · intro ht q
    have hmem : β q ∈ L := List.get_mem _ _
    have h0 : t - α.degree = 0 := by omega
    simp only [hL, h0, List.replicate_zero, List.append_nil, List.mem_flatten, List.mem_ofFn] at hmem
    obtain ⟨l, ⟨j, rfl⟩, hl⟩ := hmem
    rw [List.mem_replicate] at hl
    rw [hl.2]
    exact Fin.castSucc_ne_last j
  · intro M _ f
    have : (List.ofFn fun q => f (β q)) = (List.ofFn β).map f := by
      rw [List.map_ofFn]; rfl
    rw [this, hofFn, hL]
    simp [List.prod_append, List.map_flatten, List.prod_flatten, List.map_ofFn, Function.comp_def,
      List.prod_replicate]

end GlobalTheory.HSShort
end

