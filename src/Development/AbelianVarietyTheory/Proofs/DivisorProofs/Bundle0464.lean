module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0012
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0362
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FiniteFaithfullyFlatKer
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0410
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0427
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0454
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0450
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0145
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0141
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsFinSetSplitPlacesCoprimeConductor
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0459
public import Formalism.PairingDivisors.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0440
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0448

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAinfSandwichDatumBlockSum
section
noncomputable section

open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.BlockSum

def blk {R : Type} [Zero R] {m n : ℕ} (A : Matrix (Fin m) (Fin m) R) (B : Matrix (Fin n) (Fin n) R) :
    Matrix (Fin (m + n)) (Fin (m + n)) R :=
  (fromBlocks A 0 0 B).submatrix finSumFinEquiv.symm finSumFinEquiv.symm

theorem blk_mulVec {R : Type} [CommRing R] {m n : ℕ} (A : Matrix (Fin m) (Fin m) R)
    (B : Matrix (Fin n) (Fin n) R) (x : Fin m → R) (y : Fin n → R) :
    blk A B *ᵥ Fin.append x y = Fin.append (A *ᵥ x) (B *ᵥ y) := by
  unfold blk
  rw [submatrix_mulVec_equiv, fromBlocks_mulVec]
  ext j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · have : Fin.append x y ∘ finSumFinEquiv = Sum.elim x y := by
      ext (a | b) <;> simp
    simp [this]
  · have : Fin.append x y ∘ finSumFinEquiv = Sum.elim x y := by
      ext (a | b) <;> simp
    simp [this]

theorem blk_mul {R : Type} [CommRing R] {m n : ℕ} (A A' : Matrix (Fin m) (Fin m) R)
    (B B' : Matrix (Fin n) (Fin n) R) : blk A B * blk A' B' = blk (A * A') (B * B') := by
  unfold blk
  rw [submatrix_mul_equiv, fromBlocks_multiply]
  simp

theorem blk_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {m n : ℕ}
    (A : Matrix (Fin m) (Fin m) R) (B : Matrix (Fin n) (Fin n) R) :
    (blk A B).map f = blk (A.map f) (B.map f) := by
  unfold blk
  rw [← submatrix_map, fromBlocks_map]
  simp

theorem blk_smul_one {R : Type} [CommRing R] {m n : ℕ} (c : R) :
    blk (c • (1 : Matrix (Fin m) (Fin m) R)) (c • (1 : Matrix (Fin n) (Fin n) R)) =
      c • (1 : Matrix (Fin (m + n)) (Fin (m + n)) R) := by
  unfold blk
  have : fromBlocks (c • (1 : Matrix (Fin m) (Fin m) R)) 0 0 (c • (1 : Matrix (Fin n) (Fin n) R))
      = c • (1 : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) R) := by
    rw [← fromBlocks_one, fromBlocks_smul, smul_zero, smul_zero]
  rw [this, ← submatrix_one_equiv finSumFinEquiv.symm]
  rfl

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (Ideal.span {(p : O)}) O]

def sum {ε : PreTilt O p} {h₁ h₂ : ℕ} (D₁ : Datum ε h₁ ℤ_[p]) (D₂ : Datum ε h₂ ℤ_[p]) :
    Datum ε (h₁ + h₂) ℤ_[p] where
  F := blk D₁.F D₂.F
  G := blk D₁.G D₂.G
  Ψ := blk D₁.Ψ D₂.Ψ
  Ψ' := blk D₁.Ψ' D₂.Ψ'
  ρT := Algebra.ofId _ _
  ρM := (RingHom.mapMatrix (ofPadic p O)).comp (algebraMap _ _)
  G_mul_F := by rw [blk_mul, D₁.G_mul_F, D₂.G_mul_F, blk_smul_one]
  F_eq := by rw [blk_map, blk_mul, ← D₁.F_eq, ← D₂.F_eq]
  Ψ_mul := by rw [blk_mul, D₁.Ψ_mul, D₂.Ψ_mul, blk_smul_one]
  F_act := by
    intro a
    have : ((algebraMap ℤ_[p] (Matrix (Fin (h₁ + h₂)) (Fin (h₁ + h₂)) ℤ_[p]) a).map (ofPadic p O))
        = ofPadic p O a • (1 : Matrix (Fin (h₁ + h₂)) (Fin (h₁ + h₂)) (Ainf p O)) := by
      ext1 i j
      by_cases h : i = j <;> simp [Matrix.algebraMap_matrix_apply, h]
    simp only [Algebra.ofId_apply, RingHom.comp_apply, RingHom.mapMatrix_apply, this,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]

theorem sum_al {ε : PreTilt O p} {h₁ h₂ : ℕ} (D₁ : Datum ε h₁ ℤ_[p]) (D₂ : Datum ε h₂ ℤ_[p])
    (x : Fin h₁ → O) (y : Fin h₂ → O) :
    (sum D₁ D₂).al (Fin.append x y) = Fin.append (D₁.al x) (D₂.al y) := by
  change Matrix.toLin' ((blk D₁.F D₂.F).map _) _ = _
  rw [blk_map, toLin'_apply, blk_mulVec]
  rfl

theorem sum_bb {ε : PreTilt O p} {h₁ h₂ : ℕ} (D₁ : Datum ε h₁ ℤ_[p]) (D₂ : Datum ε h₂ ℤ_[p])
    (x : Fin h₁ → O) (y : Fin h₂ → O) :
    (sum D₁ D₂).bb (Fin.append x y) = Fin.append (D₁.bb x) (D₂.bb y) := by
  change Matrix.toLin' ((blk D₁.G D₂.G).map _) _ = _
  rw [blk_map, toLin'_apply, blk_mulVec]
  rfl

theorem exists_sum_datum : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ (h₁ h₂ : ℕ) (D₁ : Datum ε h₁ ℤ_[p]) (D₂ : Datum ε h₂ ℤ_[p]), ∃ D : Datum ε (h₁ + h₂) ℤ_[p], (∀ x y, D.al (Fin.append x y) = Fin.append (D₁.al x) (D₂.al y)) ∧ ∀ x y, D.bb (Fin.append x y) = Fin.append (D₁.bb x) (D₂.bb y) := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ ε hε h₁ h₂ D₁ D₂
  exact ⟨sum D₁ D₂, sum_al D₁ D₂, sum_bb D₁ D₂⟩

end GlobalTheory.BlockSum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoactionEqAddOfPrimitive
section
open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory.HopfQuot

section
variable {R Λ B : Type} [CommRing R] [CommRing Λ] [HopfAlgebra R Λ] [CommRing B] [Algebra R B]

theorem ev_mulRight_comul_of_primitive (l : Λ →ₗ[R] R)
    (hl : ∀ x, ev Λ l (Coalgebra.comul x) = algebraMap R Λ (l x)) (b : Λ)
    (hb : Coalgebra.comul (R := R) b = b ⊗ₜ[R] 1 + 1 ⊗ₜ[R] b) (u : Λ) :
    ev Λ (l ∘ₗ LinearMap.mulRight R b) (Coalgebra.comul u) =
      l (u * b) • (1 : Λ) - l u • b := by
  have h1 : ∀ w : Λ ⊗[R] Λ, ev Λ l (w * (b ⊗ₜ[R] 1 + 1 ⊗ₜ[R] b)) =
      ev Λ l w * b + ev Λ (l ∘ₗ LinearMap.mulRight R b) w := by
    intro w
    induction w with
    | add u v hu hv =>
      simp only [add_mul, map_add (f := _), hu, hv]
      ring
    | tmul u v => simp [mul_add]
  have h2 := hl (u * b)
  rw [Bialgebra.comul_mul, hb, h1, hl, ← Algebra.smul_def, Algebra.algebraMap_eq_smul_one] at h2
  rw [← h2]
  ring

theorem coact_ev_mulRight_of_primitive (ρ : B →ₐ[R] B ⊗[R] Λ)
    (hassoc : ∀ a, TensorProduct.assoc R B Λ Λ (ρ.toLinearMap.rTensor Λ (ρ a)) =
      (Coalgebra.comul (R := R) (A := Λ)).lTensor B (ρ a))
    (l : Λ →ₗ[R] R) (hl : ∀ x, ev Λ l (Coalgebra.comul x) = algebraMap R Λ (l x)) (b : Λ)
    (hb : Coalgebra.comul (R := R) b = b ⊗ₜ[R] 1 + 1 ⊗ₜ[R] b) (f : B) :
    ρ (ev B (l ∘ₗ LinearMap.mulRight R b) (ρ f)) =
      ev B (l ∘ₗ LinearMap.mulRight R b) (ρ f) ⊗ₜ[R] 1 - ev B l (ρ f) ⊗ₜ[R] b := by
  set l' := l ∘ₗ LinearMap.mulRight R b with hl'
  let F : B ⊗[R] (Λ ⊗[R] Λ) →ₗ[R] B ⊗[R] Λ := ((ev Λ l').restrictScalars R).lTensor B
  have h1 : ∀ w : B ⊗[R] Λ, ρ (ev B l' w) =
      F (TensorProduct.assoc R B Λ Λ (ρ.toLinearMap.rTensor Λ w)) := by
    intro w
    induction w with
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | tmul a b =>
      rw [ev_tmul, map_smul, LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply]
      generalize ρ a = w
      induction w with
      | add u v hu hv => simp only [map_add (f := _), smul_add, add_tmul, hu, hv]
      | tmul u v => simp [F]
  have h2 : ∀ w : B ⊗[R] Λ, F ((Coalgebra.comul (R := R)).lTensor B w) =
      ev B l' w ⊗ₜ 1 - ev B l w ⊗ₜ b := by
    intro w
    induction w with
    | add a c ha hc =>
      simp only [map_add (f := _), add_tmul, ha, hc]
      abel
    | tmul a c =>
      have := ev_mulRight_comul_of_primitive l hl b hb c
      rw [← hl'] at this
      simp only [F, LinearMap.lTensor_tmul, LinearMap.restrictScalars_apply, this, ev_tmul,
        tmul_sub, smul_tmul]
      rfl
  rw [h1, hassoc, h2]

end

theorem exists_coact_eq_add_of_primitive : ∀ {R Λ B : Type} [CommRing R] [CommRing Λ] [HopfAlgebra R Λ] [Module.Finite R Λ] [Module.Projective R Λ] [CommRing B] [Algebra R B] (ρ : B →ₐ[R] B ⊗[R] Λ), (∀ a, TensorProduct.assoc R B Λ Λ (ρ.toLinearMap.rTensor Λ (ρ a)) = (Coalgebra.comul (R := R) (A := Λ)).lTensor B (ρ a)) → (∀ a, TensorProduct.rid R B ((Coalgebra.counit (R := R) (A := Λ)).lTensor B (ρ a)) = a) → Function.Surjective (Algebra.TensorProduct.productMap (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] Λ) ρ) → ∀ b : Λ, cobOne R Λ b = 0 → ∃ x : B, ρ x = x ⊗ₜ[R] 1 + 1 ⊗ₜ[R] b := by
  intro R Λ B _ _ _ _ _ _ _ ρ hassoc hcounit hsurj b hb0
  have hb : Coalgebra.comul (R := R) b = b ⊗ₜ[R] 1 + 1 ⊗ₜ[R] b := by
    rw [cobOne_apply, sub_sub, sub_eq_zero] at hb0
    exact hb0
  obtain ⟨-, -, hff, -⟩ := finite_faithfullyFlat_ker ρ hassoc hcounit hsurj
  set B₀ := AlgHom.equalizer ρ (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] Λ) with hB₀
  let I : Ideal B₀ :=
    { carrier := {y | ∃ x : B, ρ x = x ⊗ₜ[R] 1 + (y : B) ⊗ₜ[R] b}
      add_mem' := by
        rintro y z ⟨x, hx⟩ ⟨x', hx'⟩
        refine ⟨x + x', ?_⟩
        rw [map_add (f := _), hx, hx', Subalgebra.coe_add, add_tmul, add_tmul]
        abel
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := by
        rintro t y ⟨x, hx⟩
        have ht : ρ t = (t : B) ⊗ₜ 1 := t.2
        refine ⟨t * x, ?_⟩
        rw [map_mul, ht, hx]
        simp [mul_add] }
  obtain ⟨n, l, T, hl, hT⟩ := exists_integrals R Λ
  have hmem : ∀ k f, ev B (l k) (ρ f) ∈ I.map (algebraMap B₀ B) := by
    intro k f
    refine Ideal.mem_map_of_mem (algebraMap B₀ B)
      (x := ⟨ev B (l k) (ρ f), ev_mem_equalizer ρ hassoc _ (hl k) f⟩) ?_
    refine ⟨-ev B (l k ∘ₗ LinearMap.mulRight R b) (ρ f), ?_⟩
    rw [map_neg, coact_ev_mulRight_of_primitive ρ hassoc _ (hl k) b hb, neg_tmul]
    abel
  have hall : ∀ k z, ev B (l k) z ∈ I.map (algebraMap B₀ B) := by
    intro k z
    obtain ⟨w, rfl⟩ := hsurj z
    induction w with
    | add u v hu hv =>
      rw [map_add (f := _), map_add (f := _)]
      exact add_mem hu hv
    | tmul u v =>
      have : (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] Λ) u * ρ v = u • ρ v := by
        rw [Algebra.smul_def]
        rfl
      rw [Algebra.TensorProduct.productMap_apply_tmul, this, map_smul]
      exact Ideal.mul_mem_left _ _ (hmem k v)
  have h1 : (1 : B) ∈ I.map (algebraMap B₀ B) := by
    have : (1 : B) = ∑ k, ev B (l k) (1 ⊗ₜ T k) := by
      have h := hT 1
      simp only [mul_one, Bialgebra.counit_one] at h
      simp [← Finset.sum_smul, h]
    rw [this]
    exact Ideal.sum_mem _ fun k _ => hall k _
  have h2 : (1 : B₀) ∈ I := by
    rw [← Ideal.comap_map_eq_self_of_faithfullyFlat (B := B) I, Ideal.mem_comap, map_one]
    exact h1
  exact h2

end GlobalTheory.HopfQuot
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdealGeometricRankIffOfLieCondition
section
noncomputable section

namespace GlobalTheory.UPel.HT.LieLin.RankIdeal

open Matrix
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.LieLin

theorem exists_ideal_rank_iff : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (B : Type) [CommRing B]
  (βB : R →+* B) (n : ℕ) (M : 𝓞 D.F →+* Matrix (Fin n) (Fin n) B),
    ∃ K₂ : Ideal B, ∀ (T : Type) [CommRing T] (f : B →+* T), lieIdeal b βB M ≤ RingHom.ker f →
      ((∀ (k : Type) [Field k] [IsAlgClosed k] (h : T →+* k) (i : Fin D.a),
          Module.finrank k (eigSub (matAct M (h.comp f)) ((h.comp (f.comp βB)).comp (b.t i))) = D.m) ↔
        K₂ ≤ RingHom.ker f) := by
  intro p _ D R _ b B _ βB n M
  set J := lieIdeal b βB M with hJdef
  let P : Fin D.a → Matrix (Fin n) (Fin n) (B ⧸ J) := fun i => (projMat b βB M i).map (Ideal.Quotient.mk J)
  have hJmk : J ≤ RingHom.ker (Ideal.Quotient.mk J) := fun a ha => by
    rw [RingHom.mem_ker]; exact Ideal.Quotient.eq_zero_iff_mem.2 ha

  have hrange : ∀ (K : Type) [CommRing K] (g : B →+* K), J ≤ RingHom.ker g → ∀ i : Fin D.a,
      (eigSub (matAct M g) ((g.comp βB).comp (b.t i)) : Set (Fin n → K)) =
        LinearMap.range ((projMat b βB M i).map g).mulVecLin := by
    intro K _ g hg i
    ext v
    simp only [SetLike.mem_coe, mem_eigSub, matAct_apply, LinearMap.mem_range, Matrix.mulVecLin_apply,
      RingHom.coe_comp, Function.comp_apply]
    constructor
    · intro hv
      exact ⟨v, GlobalTheory.T.eigenPartProjectionMatrix_map_mulVec_of_eigenvector p D R b B βB n M K g i v hv⟩
    · rintro ⟨w, rfl⟩ c
      rw [Matrix.mulVec_mulVec, GlobalTheory.T.map_mul_eigenPartProjectionMatrix_eq_scalar p D R b B βB n M K g hg i c, Matrix.smul_mulVec]
  have hidem : ∀ i, P i * P i = P i := by
    intro i
    apply (Matrix.toLin' (R := B ⧸ J) (m := Fin n) (n := Fin n)).injective
    apply LinearMap.ext
    intro v
    simp only [Matrix.toLin'_apply]
    rw [← Matrix.mulVec_mulVec]
    apply GlobalTheory.T.eigenPartProjectionMatrix_map_mulVec_of_eigenvector p D R b B βB n M _ (Ideal.Quotient.mk J) i
    intro c
    rw [Matrix.mulVec_mulVec, GlobalTheory.T.map_mul_eigenPartProjectionMatrix_eq_scalar p D R b B βB n M _ _ hJmk i c, Matrix.smul_mulVec]
  obtain ⟨x, hx⟩ := GlobalTheory.T.exists_rank_ideal_of_idempotent' (B ⧸ J) (Fin D.a) n P hidem D.m
  obtain ⟨x', rfl⟩ := Ideal.Quotient.mk_surjective x
  refine ⟨Ideal.span {x'}, fun T _ f hf => ?_⟩
  have hfa : ∀ a ∈ J, f a = 0 := fun a ha => RingHom.mem_ker.1 (hf ha)
  let fb : B ⧸ J →+* T := Ideal.Quotient.lift J f hfa
  have hfb : fb.comp (Ideal.Quotient.mk J) = f := Ideal.Quotient.lift_comp_mk _ _ _
  rw [Ideal.span_singleton_le_iff_mem, RingHom.mem_ker]
  have hx' := hx T fb
  rw [show fb (Ideal.Quotient.mk J x') = f x' from Ideal.Quotient.lift_mk _ _ _] at hx'
  rw [← hx']
  refine forall_congr' fun k => forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun h => forall_congr' fun i => ?_
  have e1 : eigSub (matAct M (h.comp f)) ((h.comp (f.comp βB)).comp (b.t i)) =
      LinearMap.range ((P i).map (h.comp fb)).mulVecLin := by
    apply SetLike.coe_injective
    show (eigSub (matAct M (h.comp f)) (((h.comp f).comp βB).comp (b.t i)) : Set (Fin n → k)) = _
    rw [hrange k (h.comp f) (fun a ha => by simp [hfa a ha]) i]
    congr 3
  rw [e1, GlobalTheory.T.finrank_range_map_idempotent_eq_rankAtStalk (B ⧸ J) n (P i) (hidem i) k (h.comp fb)]

end GlobalTheory.UPel.HT.LieLin.RankIdeal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdealSectionIntegralFiniteIdeleUpToUnits
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.CMVal.Euler
open scoped nonZeroDivisors

namespace GlobalTheory.CMVal.IdeleIdeal

variable {E : Type} [Field E] [NumberField E]

def ordAt (y : (Af E)ˣ) (w : HeightOneSpectrum (𝓞 E)) : ℕ := (-WithZero.log (Valued.v ((y : Af E) w))).toNat

def idealOf (y : (Af E)ˣ) : Ideal (𝓞 E) := ∏ᶠ w : HeightOneSpectrum (𝓞 E), w.asIdeal ^ ordAt y w

theorem ordAt_eventually (y : (Af E)ˣ) : ∀ᶠ w in Filter.cofinite, ordAt y w = 0 := by
  filter_upwards [(FiniteAdeleRing.isUnit_iff.1 y.isUnit).2] with w hw
  simp [ordAt, hw]

theorem finite_pow (y : (Af E)ˣ) :
    (Function.mulSupport fun w : HeightOneSpectrum (𝓞 E) => w.asIdeal ^ ordAt y w).Finite := by
  have := ordAt_eventually y
  rw [Filter.eventually_cofinite] at this
  refine this.subset fun v hv h1 => hv ?_
  simp [h1]

theorem ordAt_cast {y : (Af E)ˣ} {w : HeightOneSpectrum (𝓞 E)} (h : Valued.v ((y : Af E) w) ≤ 1) :
    (ordAt y w : ℤ) = -WithZero.log (Valued.v ((y : Af E) w)) := by
  have h0 := IdeleModule.coord_ne y w
  have : WithZero.log (Valued.v ((y : Af E) w)) ≤ 0 := by
    rw [← WithZero.exp_le_exp, WithZero.exp_log h0, WithZero.exp_zero]; exact h
  unfold ordAt
  omega

theorem modF_eq {y : (Af E)ˣ} (h : ∀ w, Valued.v ((y : Af E) w) ≤ 1) :
    modF y = ((Ideal.absNorm (idealOf y) : ℕ) : ℝ)⁻¹ := by
  unfold idealOf modF
  rw [map_finprod Ideal.absNorm (finite_pow y)]
  have hf : (Function.mulSupport fun w : HeightOneSpectrum (𝓞 E) => Ideal.absNorm (w.asIdeal ^ ordAt y w)).Finite :=
    (finite_pow y).subset fun w hw h1 => hw (by simp only [h1, map_one])
  have := map_finprod (Nat.castRingHom ℝ) hf
  simp only [eq_natCast] at this
  rw [this, ← finprod_inv_distrib]
  refine finprod_congr fun w => ?_
  rw [map_pow, Nat.cast_pow, ← zpow_natCast, ordAt_cast (h w), zpow_neg, inv_inv]

theorem count_idealOf (y : (Af E)ˣ) (w : HeightOneSpectrum (𝓞 E)) :
    FractionalIdeal.count E w (idealOf y : FractionalIdeal (𝓞 E)⁰ E) = ordAt y w := by
  have h1 : (idealOf y : FractionalIdeal (𝓞 E)⁰ E) =
      ∏ᶠ v : HeightOneSpectrum (𝓞 E), (v.asIdeal : FractionalIdeal (𝓞 E)⁰ E) ^ (ordAt y v : ℤ) := by
    have := map_finprod (FractionalIdeal.coeIdealHom (𝓞 E)⁰ E) (finite_pow y)
    simp only [map_pow, FractionalIdeal.coeIdealHom_apply] at this
    simp only [zpow_natCast]
    exact this
  rw [h1, FractionalIdeal.count_finprod]
  filter_upwards [ordAt_eventually y] with v hv
  simp [hv]

theorem val_eq_of_idealOf_eq {y y' : (Af E)ˣ} (h : ∀ w, Valued.v ((y : Af E) w) ≤ 1)
    (h' : ∀ w, Valued.v ((y' : Af E) w) ≤ 1) (e : idealOf y = idealOf y') (w : HeightOneSpectrum (𝓞 E)) :
    Valued.v ((y : Af E) w) = Valued.v ((y' : Af E) w) := by
  have h1 := count_idealOf y w
  rw [e, count_idealOf, ordAt_cast (h w), ordAt_cast (h' w), neg_inj] at h1
  rw [← WithZero.exp_log (IdeleModule.coord_ne y w), ← h1, WithZero.exp_log (IdeleModule.coord_ne y' w)]

end GlobalTheory.CMVal.IdeleIdeal


open GlobalTheory.CMVal.IdeleIdeal in
theorem GlobalTheory.CMVal.exists_idele_section_of_ideal : ∀ (E : Type) [Field E] [NumberField E] , ∃ g : Ideal (𝓞 E) → (Af E)ˣ, ∀ y : (Af E)ˣ, (∀ w, Valued.v ((y : Af E) w) ≤ 1) → ∃ J : Ideal (𝓞 E), modF y = ((Ideal.absNorm J : ℕ) : ℝ)⁻¹ ∧ ∀ w, Valued.v ((((g J)⁻¹ * y : (Af E)ˣ) : Af E) w) = 1 := by
  intro E _ _
  classical
  refine ⟨fun J => if h : ∃ y : (Af E)ˣ, (∀ w, Valued.v ((y : Af E) w) ≤ 1) ∧ idealOf y = J then h.choose else 1,
    fun y hy => ⟨idealOf y, modF_eq hy, fun w => ?_⟩⟩
  have h : ∃ y' : (Af E)ˣ, (∀ w, Valued.v ((y' : Af E) w) ≤ 1) ∧ idealOf y' = idealOf y := ⟨y, hy, rfl⟩
  simp only [dif_pos h]
  rw [Units.val_mul, mul_coord, inv_coord, map_mul, map_inv₀,
    val_eq_of_idealOf_eq h.choose_spec.1 hy h.choose_spec.2 w, inv_mul_cancel₀ (IdeleModule.coord_ne y w)]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLatticePointsIntegralIdelesEquiv
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal

namespace GlobalTheory.CMVal.LatBij

variable {E : Type} [Field E] [NumberField E]

def diag : Eˣ →* (Af E)ˣ := Units.map (algebraMap E (Af E)).toMonoidHom

theorem coe_diag (a : Eˣ) : (diag a : Af E) = algebraMap E (Af E) a := rfl

theorem diag_mem_princ (a : Eˣ) : diag a ∈ (princ : Subgroup (Af E)ˣ) := ⟨a, rfl⟩

theorem diag_unit_mem (c : Ideal (OF E)) (u : (OF E)ˣ) :
    diag (Units.map (algebraMap (OF E) E).toMonoidHom u) ∈ hatOUnits c := by
  rw [mem_hatOUnits, ← map_inv, ← map_inv]
  exact ⟨algebraMap_mem_hatO (algebraMap_mem_orderC c _), algebraMap_mem_hatO (algebraMap_mem_orderC c _)⟩

def rep {c : Ideal (OF E)} {y : (Af E)ˣ} (a : modUnits (lattice c y)) : Eˣ := Units.mk0 a.1.out (out_mem_lattice a).2

def toIdele (c : Ideal (OF E)) (p : Σ q : PicO c, modUnits (lattice c q.out)) :
    {z : (Af E)ˣ ⧸ hatOUnits c // ∃ y : (Af E)ˣ, (QuotientGroup.mk y : (Af E)ˣ ⧸ hatOUnits c) = z ∧ (y : Af E) ∈ hatO c} :=
  ⟨QuotientGroup.mk (diag (rep p.2) * p.1.out⁻¹), _, rfl, (out_mem_lattice p.2).1⟩

theorem toIdele_surjective (c : Ideal (OF E)) : Function.Surjective (toIdele c) := by
  rintro ⟨_, y, rfl, hy⟩
  let q : PicO c := QuotientGroup.mk y⁻¹
  have hq : (q.out)⁻¹ * y⁻¹ ∈ princ ⊔ hatOUnits c := QuotientGroup.eq.1 (Quotient.out_eq q)
  obtain ⟨_, ⟨α, rfl⟩, u, hu, h⟩ := Subgroup.mem_sup.1 hq
  change diag α * u = _ at h
  have h1 : diag α⁻¹ * q.out⁻¹ = y * u := by
    rw [map_inv, eq_mul_inv_iff_mul_eq.1 h |>.symm, mul_assoc, inv_mul_cancel_left, mul_comm]
  have hx : ((α⁻¹ : Eˣ) : E) ∈ lattice c q.out := by
    rw [mem_lattice, ← coe_diag, ← Units.val_mul, h1, Units.val_mul]
    exact mul_mem hy hu.1
  let a : modUnits (lattice c q.out) := ⟨Quotient.mk _ ((α⁻¹ : Eˣ) : E), _, hx, Units.ne_zero _, rfl⟩
  obtain ⟨w, hw⟩ : (unitRel (E := E)).r ((α⁻¹ : Eˣ) : E) a.1.out := Quotient.exact (Quotient.out_eq a.1).symm
  have hr : rep a = Units.map (algebraMap (OF E) E).toMonoidHom w * α⁻¹ := Units.ext hw
  refine ⟨⟨q, a⟩, Subtype.ext ?_⟩
  refine (QuotientGroup.eq.2 ?_ : (QuotientGroup.mk y : (Af E)ˣ ⧸ hatOUnits c) = _).symm
  change y⁻¹ * (diag (rep a) * q.out⁻¹) ∈ _
  rw [hr, map_mul, mul_assoc, h1, mul_left_comm, inv_mul_cancel_left]
  exact mul_mem (diag_unit_mem c w) hu

theorem toIdele_injective (c : Ideal (OF E)) (hcap : lattice c 1 = (orderC c : Set E))
    (hun : ∀ x : E, x ≠ 0 → x ∈ orderC c → x⁻¹ ∈ orderC c → ∃ u : (OF E)ˣ, x = algebraMap (OF E) E u) :
    Function.Injective (toIdele c) := by
  rintro ⟨q, a⟩ ⟨q', a'⟩ h
  have h1 : (diag (rep a) * q.out⁻¹)⁻¹ * (diag (rep a') * q'.out⁻¹) ∈ hatOUnits c :=
    QuotientGroup.eq.1 (congrArg Subtype.val h)
  have hq : q = q' := by
    rw [← Quotient.out_eq q, ← Quotient.out_eq q']
    refine QuotientGroup.eq.2 ?_
    have : q.out⁻¹ * q'.out = diag ((rep a)⁻¹ * rep a') *
        ((diag (rep a) * q.out⁻¹)⁻¹ * (diag (rep a') * q'.out⁻¹))⁻¹ := by
      rw [map_mul, map_inv]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel
    rw [this]
    exact mul_mem (Subgroup.mem_sup_left (diag_mem_princ _)) (Subgroup.mem_sup_right (inv_mem h1))
  subst hq
  have h2 : diag ((rep a)⁻¹ * rep a') ∈ hatOUnits c := by
    convert h1 using 1
    rw [map_mul, map_inv, mul_inv, inv_inv, mul_mul_mul_comm, mul_inv_cancel, mul_one]
  have key : ∀ b : Eˣ, diag b ∈ hatOUnits c → (b : E) ∈ orderC c := fun b hb => by
    have : (b : E) ∈ lattice c 1 := by
      rw [mem_lattice, inv_one, Units.val_one, mul_one]
      exact hb.1
    rwa [hcap] at this
  obtain ⟨u, hu⟩ := hun _ (Units.ne_zero _) (key _ h2) (by
    rw [← Units.val_inv_eq_inv_val]
    exact key _ (by rw [map_inv]; exact inv_mem h2))
  have h3 : a = a' := by
    apply Subtype.ext
    rw [← Quotient.out_eq a.1, ← Quotient.out_eq a'.1]
    refine Quotient.sound ⟨u, ?_⟩
    rw [← hu]
    change ((rep a' : Eˣ) : E) = _ * ((rep a : Eˣ) : E)
    rw [← Units.val_mul, mul_comm, mul_inv_cancel_left]
  rw [h3]

theorem exists_equiv : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (𝔣 c : Ideal (OF E)), IsBaseCond 𝔣 → 𝔣 ∣ c → c ≠ ⊥ →
    ∃ e : (Σ q : PicO c, modUnits (lattice c q.out)) ≃
      {z : (Af E)ˣ ⧸ hatOUnits c // ∃ y : (Af E)ˣ, (QuotientGroup.mk y : (Af E)ˣ ⧸ hatOUnits c) = z ∧ (y : Af E) ∈ hatO c},
      ∀ p, ∀ y : (Af E)ˣ, (y : Af E) = algebraMap E (Af E) (p.2.1.out) * (((Quotient.out p.1 : (Af E)ˣ)⁻¹ : (Af E)ˣ) : Af E) →
        (e p).1 = QuotientGroup.mk y := by
  intro E _ _ _ 𝔣 c h𝔣 hc hc0
  refine ⟨Equiv.ofBijective (toIdele c) ⟨toIdele_injective c (_root_.GlobalTheory.CMVal.HatCap.lattice_one E c hc0) (GlobalTheory.T.cmRingClassOrder_units_eq_maxRealSubfield_units E 𝔣 c h𝔣 hc),
    toIdele_surjective c⟩, fun p y hy => ?_⟩
  have : y = diag (rep p.2) * p.1.out⁻¹ := Units.ext hy
  rw [this]
  rfl

end GlobalTheory.CMVal.LatBij
end
end

