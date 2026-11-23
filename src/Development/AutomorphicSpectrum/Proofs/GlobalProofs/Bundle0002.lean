module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0005
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.InstBorelGL
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0039

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.AdaptedFrameOrthogonalSubspaceStatement
section
open Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.block_basis_change_entries : ∀ (n n' a : ℕ) (hdim : a + n' + a = n) (P : Matrix (Fin n) (Fin n) ℂ), IsUnit P.det →
    ∀ (J : Matrix (Fin n) (Fin n') ℂ) (Jp : Matrix (Fin n') (Fin n) ℂ) (B Bi : Matrix (Fin n') (Fin n') ℂ), Jp * J = 1 → B * Bi = 1 →
    (∀ (i : Fin n) (j : Fin n'), J i j = ∑ r : Fin n', P i (⟨a + r.val, by omega⟩ : Fin n) * B r j) →
    (∀ b : Fin n, (b.val < a ∨ n ≤ b.val + a) → Jp *ᵥ (fun k => P k b) = 0) →
    ∀ p q : Fin n', J * Matrix.single p q (1 : ℂ) * Jp = ∑ r : Fin n', ∑ u : Fin n', (B r p * Bi q u) •
      (P * Matrix.single (⟨a + r.val, by omega⟩ : Fin n) (⟨a + u.val, by omega⟩ : Fin n) (1 : ℂ) * P⁻¹) := by
  first | exact @GlobalTheory.CompanionTheory.MidConj.conj_units_of_mid | exact GlobalTheory.CompanionTheory.MidConj.conj_units_of_mid | (intros; apply GlobalTheory.CompanionTheory.MidConj.conj_units_of_mid <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.BlockBasisChangeEntries
section
open Matrix

namespace GlobalTheory.CompanionTheory.IsometricMatrix

theorem exp_mulVec_of_mulVec_eq_zero {m : ℕ} (N : Matrix (Fin m) (Fin m) ℂ) (x : Fin m → ℂ)
    (hx : N *ᵥ x = 0) : NormedSpace.exp N *ᵥ x = x := by
  have hC : N * Matrix.replicateCol (Fin 1) x = Matrix.replicateCol (Fin 1) x * (0 : Matrix (Fin 1) (Fin 1) ℂ) := by
    ext i j
    have hi := congrFun hx i
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at hi
    simpa [Matrix.mul_apply, Matrix.replicateCol] using hi
  have hE := matrix_exp_mul_eq_mul_exp_of_intertwine N _ 0 hC
  simp only [NormedSpace.exp_zero, Matrix.mul_one] at hE
  ext i
  have hi := congrFun (congrFun hE i) 0
  simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.replicateCol] using hi

theorem main {n n' : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (H' : Matrix (Fin n') (Fin n') ℂ)
    (J : Matrix (Fin n) (Fin n') ℂ)
    (hH : Hᴴ = H) (hH' : H'ᴴ = H') (hd : IsUnit H.det) (hd' : IsUnit H'.det)
    (hJ : Jᴴ * H * J = H') :
    ((H'⁻¹ * Jᴴ * H) * J = 1 ∧
      (∀ Z : Matrix (Fin n') (Fin n') ℂ, -(H⁻¹ * (J * Z * (H'⁻¹ * Jᴴ * H))ᴴ * H) = J * (-(H'⁻¹ * Zᴴ * H')) * (H'⁻¹ * Jᴴ * H)) ∧
      (∀ A : Matrix (Fin n') (Fin n') ℂ, Aᴴ * H' + H' * A = 0 →
        (J * A * (H'⁻¹ * Jᴴ * H))ᴴ * H + H * (J * A * (H'⁻¹ * Jᴴ * H)) = 0) ∧
      (∀ (A : Matrix (Fin n') (Fin n') ℂ) (t : ℝ), NormedSpace.exp (t • (J * A * (H'⁻¹ * Jᴴ * H))) * J = J * NormedSpace.exp (t • A)) ∧
      (∀ (A : Matrix (Fin n') (Fin n') ℂ) (t : ℝ) (x : Fin n → ℂ), (Jᴴ * H) *ᵥ x = 0 →
        NormedSpace.exp (t • (J * A * (H'⁻¹ * Jᴴ * H))) *ᵥ x = x)) := by
  have hJ' : Jᴴ * (H * J) = H' := by rw [← Matrix.mul_assoc]; exact hJ
  have hPJ : H'⁻¹ * Jᴴ * H * J = 1 := by
    simp only [Matrix.mul_assoc]
    rw [hJ', Matrix.nonsing_inv_mul _ hd']
  have hPs : (H'⁻¹ * Jᴴ * H)ᴴ = H * J * H'⁻¹ := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.conjTranspose_nonsing_inv, hH, hH', Matrix.mul_assoc]
  refine ⟨hPJ, fun Z => ?_, fun A hA => ?_, fun A t => ?_, fun A t x hx => ?_⟩
  · rw [Matrix.conjTranspose_mul (J * Z) (H'⁻¹ * Jᴴ * H), hPs, Matrix.conjTranspose_mul J Z]
    simp only [Matrix.mul_assoc, Matrix.neg_mul, Matrix.mul_neg,
      Matrix.nonsing_inv_mul_cancel_left _ _ hd, Matrix.mul_nonsing_inv_cancel_left _ _ hd']
  · have key : H * J * H'⁻¹ * (Aᴴ * H' + H' * A) * (H'⁻¹ * Jᴴ * H) =
        (J * A * (H'⁻¹ * Jᴴ * H))ᴴ * H + H * (J * A * (H'⁻¹ * Jᴴ * H)) := by
      rw [Matrix.conjTranspose_mul (J * A) (H'⁻¹ * Jᴴ * H), hPs, Matrix.conjTranspose_mul J A,
        Matrix.mul_add, Matrix.add_mul]
      simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hd',
        Matrix.mul_nonsing_inv_cancel_left _ _ hd']
    rw [← key, hA, Matrix.mul_zero, Matrix.zero_mul]
  · have hBJ : J * A * (H'⁻¹ * Jᴴ * H) * J = J * A := by
      rw [Matrix.mul_assoc, hPJ, Matrix.mul_one]
    exact matrix_exp_smul_mul_eq_mul_exp_smul_of_intertwine n n' _ J A hBJ t
  · have hB : (J * A * (H'⁻¹ * Jᴴ * H)) *ᵥ x = 0 := by
      have hfac : J * A * (H'⁻¹ * Jᴴ * H) = (J * A * H'⁻¹) * (Jᴴ * H) := by
        simp only [Matrix.mul_assoc]
      rw [hfac, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero]
    apply exp_mulVec_of_mulVec_eq_zero
    rw [Matrix.smul_mulVec, hB, smul_zero]

end GlobalTheory.CompanionTheory.IsometricMatrix
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.GeneralLinearIntegralCompactOpen
section
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.QLTop

open ValuativeRel

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem nonarchimedeanLocalField_secondCountable_t2Space (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] : SecondCountableTopology k ∧ T2Space k := by
  let := IsTopologicalAddGroup.rightUniformSpace k
  have := isUniformAddGroup_of_addCommGroup (G := k)
  let : (Valued.v (R := k)).RankOne :=
  { hom' := IsRankLeOne.nonempty.some.emb (R := k).comp MonoidWithZeroHom.ValueGroup₀.embedding
    strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  open scoped Valued in
  have : ProperSpace k := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace k
  exact ⟨secondCountable_of_proper, inferInstance⟩

theorem isOpen_isCompact_integers : IsOpen ((𝒪[F] : Subring F) : Set F) ∧ IsCompact ((𝒪[F] : Subring F) : Set F) := by
  refine ⟨?_, ?_⟩
  · exact Valuation.isOpen_valuationSubring (valuation F)
  · exact isCompact_iff_compactSpace.2 (inferInstance : CompactSpace 𝒪[F])

def intSet (O : Subring F) (n : ℕ) : Set (Matrix (Fin n) (Fin n) F) := {M | IsInt O M}

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] in
theorem isOpen_intSet {O : Subring F} (hO : IsOpen (O : Set F)) (n : ℕ) : IsOpen (intSet O n) := by
  have : intSet O n = ⋂ i, ⋂ j, (fun M : Matrix (Fin n) (Fin n) F => M i j) ⁻¹' (O : Set F) := by
    ext M; simp [intSet, IsInt]
  rw [this]
  exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
    hO.preimage ((continuous_apply j).comp (continuous_apply i))

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] in
theorem isCompact_intSet {O : Subring F} (hO : IsCompact (O : Set F)) (n : ℕ) : IsCompact (intSet O n) := by
  have : intSet O n = Set.pi Set.univ fun _ : Fin n => Set.pi Set.univ fun _ : Fin n => (O : Set F) := by
    ext M
    exact ⟨fun h i _ j _ => h i j, fun h i j => h i (Set.mem_univ _) j (Set.mem_univ _)⟩
  rw [this]
  exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hO

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem GLint_eq_preimage (O : Subring F) (n : ℕ) :
    (GLint O n : Set (GL (Fin n) F)) =
      Units.embedProduct (Matrix (Fin n) (Fin n) F) ⁻¹' (intSet O n ×ˢ (MulOpposite.op '' intSet O n)) := by
  ext g
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, ⟨_, h2, rfl⟩⟩
  · rintro ⟨h1, ⟨y, hy, he⟩⟩
    have hy' : y = ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := MulOpposite.op_injective he
    exact ⟨h1, hy' ▸ hy⟩

theorem gl_topology : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}, LF O ϖ nrm q → ∀ n : ℕ,
    IsOpen (GLint O n : Set (GL (Fin n) F)) ∧ IsCompact (GLint O n : Set (GL (Fin n) F)) ∧
    LocallyCompactSpace (GL (Fin n) F) ∧ SecondCountableTopology (GL (Fin n) F) ∧ T2Space (GL (Fin n) F) ∧
    IsOpen (Mint O n) ∧ IsClosed (Mint O n) := by
  intro F _ _ _ _ O ϖ nrm q h n
  obtain ⟨hsc, ht2⟩ := nonarchimedeanLocalField_secondCountable_t2Space F
  obtain ⟨hOo, hOc⟩ : IsOpen (O : Set F) ∧ IsCompact (O : Set F) := by
    rw [h.O_eq]; exact isOpen_isCompact_integers
  have : T2Space (Matrix (Fin n) (Fin n) F) := inferInstanceAs (T2Space (Fin n → Fin n → F))
  have : SecondCountableTopology (Matrix (Fin n) (Fin n) F) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → F))
  have : LocallyCompactSpace (Matrix (Fin n) (Fin n) F) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → F))
  have : SecondCountableTopology (Matrix (Fin n) (Fin n) F)ᵐᵒᵖ :=
    (MulOpposite.opHomeomorph (M := Matrix (Fin n) (Fin n) F)).symm.isEmbedding.secondCountableTopology
  have hSo := isOpen_intSet hOo n
  have hSc := isCompact_intSet hOc n
  have hemb := Units.isClosedEmbedding_embedProduct (α := Matrix (Fin n) (Fin n) F)
  have hMint : Mint O n = Units.val ⁻¹' intSet O n := rfl
  refine ⟨?_, ?_, hemb.locallyCompactSpace, hemb.isEmbedding.secondCountableTopology, inferInstance, ?_, ?_⟩
  · rw [GLint_eq_preimage]
    exact (hSo.prod (MulOpposite.opHomeomorph.isOpenMap _ hSo)).preimage hemb.continuous
  · rw [GLint_eq_preimage]
    exact hemb.isCompact_preimage (hSc.prod (hSc.image MulOpposite.continuous_op))
  · rw [hMint]; exact hSo.preimage Units.continuous_val
  · rw [hMint]; exact hSc.isClosed.preimage Units.continuous_val

end GlobalTheory.CompanionTheory.QLTop
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.IwasawaDecompositionUpperTriangular
section
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel

namespace GlobalTheory.CompanionTheory.QL.Iwasawa

theorem map_mem_GLint {F : Type} [Field F] [ValuativeRel F] {n : ℕ}
    (k : GL (Fin n) (ValuativeRel.valuation F).valuationSubring) :
    GeneralLinearGroup.map (algebraMap (ValuativeRel.valuation F).valuationSubring F) k ∈
      GLint 𝒪[F] n := by
  have key : ∀ (u : GL (Fin n) (ValuativeRel.valuation F).valuationSubring),
      IsInt 𝒪[F] ((GeneralLinearGroup.map
        (algebraMap (ValuativeRel.valuation F).valuationSubring F) u : GL (Fin n) F) :
          Matrix (Fin n) (Fin n) F) := by
    intro u i j
    have h := (u.1 i j).2
    exact h
  refine ⟨key k, ?_⟩
  rw [← map_inv]
  exact key k⁻¹

theorem exists_upper_mul_int {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}
    (h : LF O ϖ nrm q) (n : ℕ) (g : GL (Fin n) F) :
    ∃ b : GL (Fin n) F, (b : Matrix (Fin n) (Fin n) F).BlockTriangular id ∧
      ∃ k ∈ GLint O n, g = b * k := by
  obtain rfl := h.O_eq
  obtain ⟨k, b, hb, hg⟩ :=
    GlobalTheory.ValIwasawa.iwasawa (ValuativeRel.valuation F).valuationSubring F n g⁻¹
  refine ⟨b⁻¹, ?_, _, (GLint _ n).inv_mem (map_mem_GLint k), ?_⟩
  · let _ : Invertible (b : Matrix (Fin n) (Fin n) F) := Units.invertible b
    rw [Matrix.coe_units_inv]
    exact Matrix.blockTriangular_inv_of_blockTriangular hb
  · rw [← _root_.mul_inv_rev, ← hg, inv_inv]

end GlobalTheory.CompanionTheory.QL.Iwasawa
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.LocalFieldUniformizerNormProperties
section
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel

namespace GlobalTheory.CompanionTheory.QL.NormalisedValue

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}

theorem val_pi_lt_one (h : LF O ϖ nrm q) : ValuativeRel.valuation F ϖ < 1 := by
  exact (h.lt_one ϖ).2 ⟨1, O.one_mem, (mul_one ϖ).symm⟩

theorem val_pi_pos (h : LF O ϖ nrm q) : 0 < ValuativeRel.valuation F ϖ := by
  first
    | exact (Valuation.pos_iff _).2 h.ne
    | exact zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 h.ne)

theorem mem_iff_val_le (h : LF O ϖ nrm q) (x : F) : x ∈ O ↔ ValuativeRel.valuation F x ≤ 1 := by
  rw [h.O_eq]
  exact Valuation.mem_integer_iff _ _

theorem one_lt_q (h : LF O ϖ nrm q) : 1 < q := by
  have hq0 : q ≠ 0 := by
    intro hq
    have hp := h.nrm_pi
    rw [hq, Nat.cast_zero, _root_.inv_zero] at hp
    exact h.ne ((AbsoluteValue.eq_zero nrm).1 hp)
  have hq1 : q ≠ 1 := by
    intro hq
    have hc := h.card
    rw [hq] at hc
    have hs := (Nat.card_eq_one_iff_unique.1 hc.symm).1
    exact not_subsingleton (IsLocalRing.ResidueField ↥(ValuativeRel.valuation F).integer) hs
  omega

private theorem isUnit_iff_valuation_eq_one' (y : 𝒪[F]) : IsUnit y ↔ ValuativeRel.valuation F (y : F) = 1 := by
  first
    | exact (Valuation.integer.integers _).isUnit_iff_valuation_eq_one
    | simpa using (Valuation.integer.integers (ValuativeRel.valuation F)).isUnit_iff_valuation_eq_one (x := y)

theorem irreducible_pi (h : LF O ϖ nrm q) :
    Irreducible (⟨ϖ, (Valuation.mem_integer_iff _ _).2 (val_pi_lt_one h).le⟩ : 𝒪[F]) := by
  refine ⟨?_, ?_⟩
  · rw [isUnit_iff_valuation_eq_one']
    exact (val_pi_lt_one h).ne
  · intro a b hab
    by_cases ha : ValuativeRel.valuation F (a : F) = 1
    · left
      exact (isUnit_iff_valuation_eq_one' a).2 ha
    · right
      have ha1 : ValuativeRel.valuation F (a : F) < 1 :=
        lt_of_le_of_ne ((Valuation.mem_integer_iff _ _).1 a.2) ha
      obtain ⟨o, hoO, hao⟩ := (h.lt_one a).1 ha1
      have hab' : (ϖ : F) = (a : F) * (b : F) := congrArg Subtype.val hab
      have hoI : o ∈ 𝒪[F] := by
        rw [← h.O_eq]
        exact hoO
      have hob : (⟨o, hoI⟩ : 𝒪[F]) * b = 1 := by
        apply Subtype.ext
        show o * (b : F) = 1
        have hh : ϖ * 1 = ϖ * (o * (b : F)) := by
          rw [mul_one, ← mul_assoc, ← hao, ← hab']
        exact (mul_left_cancel₀ h.ne hh).symm
      exact ⟨⟨b, ⟨o, hoI⟩, (mul_comm _ _).trans hob, hob⟩, rfl⟩

theorem val_eq_pow_of_int (h : LF O ϖ nrm q) {x : F} (hx : x ≠ 0)
    (hxO : ValuativeRel.valuation F x ≤ 1) :
    ∃ n : ℕ, ValuativeRel.valuation F x = ValuativeRel.valuation F ϖ ^ n := by
  have hxI : x ∈ 𝒪[F] := (Valuation.mem_integer_iff _ _).2 hxO
  have hx' : (⟨x, hxI⟩ : 𝒪[F]) ≠ 0 := by
    intro h0
    exact hx (congrArg Subtype.val h0)
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx' (irreducible_pi h)
  refine ⟨n, ?_⟩
  have hv := congrArg (fun y : 𝒪[F] => ValuativeRel.valuation F (y : F)) hu
  have hu1 : ValuativeRel.valuation F ((u : 𝒪[F]) : F) = 1 := (isUnit_iff_valuation_eq_one' _).1 u.isUnit
  simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow, map_mul, map_pow, hu1, one_mul] at hv
  exact hv

theorem val_eq_zpow (h : LF O ϖ nrm q) {x : F} (hx : x ≠ 0) :
    ∃ e : ℤ, ValuativeRel.valuation F x = ValuativeRel.valuation F ϖ ^ e := by
  by_cases hle : ValuativeRel.valuation F x ≤ 1
  · obtain ⟨n, hn⟩ := val_eq_pow_of_int h hx hle
    exact ⟨n, by rw [hn, _root_.zpow_natCast]⟩
  · have hlt : 1 < ValuativeRel.valuation F x := lt_of_not_ge hle
    have hinv : ValuativeRel.valuation F x⁻¹ ≤ 1 := ((Valuation.one_lt_val_iff _ hx).1 hlt).le
    obtain ⟨n, hn⟩ := val_eq_pow_of_int h (inv_ne_zero hx) hinv
    refine ⟨-(n : ℤ), ?_⟩
    rw [_root_.zpow_neg, _root_.zpow_natCast, ← hn, map_inv₀, _root_.inv_inv]

theorem val_mul_zpow (h : LF O ϖ nrm q) {x : F} {e : ℤ}
    (he : ValuativeRel.valuation F x = ValuativeRel.valuation F ϖ ^ e) :
    ValuativeRel.valuation F (x * ϖ ^ (-e)) = 1 := by
  rw [map_mul, map_zpow₀, he, ← zpow_add₀ (val_pi_pos h).ne']
  simp

theorem nrm_eq_zpow (h : LF O ϖ nrm q) {x : F} {e : ℤ}
    (he : ValuativeRel.valuation F x = ValuativeRel.valuation F ϖ ^ e) :
    nrm x = (q : ℝ) ^ (-e) := by
  have h1 : nrm (x * ϖ ^ (-e)) = 1 := h.nrm_unit _ (val_mul_zpow h he)
  have hdecomp : x = x * ϖ ^ (-e) * ϖ ^ e := by
    rw [mul_assoc, ← zpow_add₀ h.ne, neg_add_cancel, _root_.zpow_zero, mul_one]
  have hz : nrm (ϖ ^ e) = nrm ϖ ^ e := by
    first
      | exact map_zpow₀ nrm ϖ e
      | exact map_zpow₀ nrm.toMonoidWithZeroHom ϖ e
  conv_lhs => rw [hdecomp]
  rw [map_mul, h1, one_mul, hz, h.nrm_pi, _root_.inv_zpow']

private theorem nrm_le_one_of_valuation_le_one (h : LF O ϖ nrm q) (x : F) (hx : ValuativeRel.valuation F x ≤ 1) :
    nrm x ≤ 1 := by
  by_cases h0 : x = 0
  · simp [h0]
  · obtain ⟨n, hn⟩ := val_eq_pow_of_int h h0 hx
    rw [nrm_eq_zpow h (e := (n : ℤ)) (by rw [hn, _root_.zpow_natCast]), _root_.zpow_neg, _root_.zpow_natCast]
    have hq : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (one_lt_q h).le
    exact inv_le_one_of_one_le₀ (one_le_pow₀ hq)

private theorem nrm_le_inv_q_of_valuation_lt_one (h : LF O ϖ nrm q) (x : F) (hx : ValuativeRel.valuation F x < 1) :
    nrm x ≤ (q : ℝ)⁻¹ := by
  obtain ⟨o, hoO, rfl⟩ := (h.lt_one x).1 hx
  rw [map_mul, h.nrm_pi]
  have ho : nrm o ≤ 1 := nrm_le_one_of_valuation_le_one h o ((mem_iff_val_le h o).1 hoO)
  have hq : (0 : ℝ) ≤ (q : ℝ)⁻¹ := by positivity
  calc (q : ℝ)⁻¹ * nrm o ≤ (q : ℝ)⁻¹ * 1 := mul_le_mul_of_nonneg_left ho hq
    _ = (q : ℝ)⁻¹ := mul_one _

theorem nrm_le_one_iff (h : LF O ϖ nrm q) (x : F) :
    nrm x ≤ 1 ↔ ValuativeRel.valuation F x ≤ 1 := by
  constructor
  · intro hn
    by_contra hv
    have hlt : 1 < ValuativeRel.valuation F x := lt_of_not_ge hv
    have hx : x ≠ 0 := by
      rintro rfl
      simp at hlt
    have hi : ValuativeRel.valuation F x⁻¹ < 1 := (Valuation.one_lt_val_iff _ hx).1 hlt
    have h2 : nrm x⁻¹ ≤ (q : ℝ)⁻¹ := nrm_le_inv_q_of_valuation_lt_one h _ hi
    have hq : (q : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast one_lt_q h)
    rw [map_inv₀] at h2
    have hpos : 0 < nrm x := nrm.pos hx
    have h3 : (nrm x)⁻¹ < 1 := lt_of_le_of_lt h2 hq
    have h4 : 1 < nrm x := (inv_lt_one₀ hpos).1 h3
    linarith
  · exact nrm_le_one_of_valuation_le_one h x

theorem nrm_lt_one_iff (h : LF O ϖ nrm q) (x : F) :
    nrm x < 1 ↔ ValuativeRel.valuation F x < 1 := by
  constructor
  · intro hn
    by_contra hv
    have h1 : 1 ≤ ValuativeRel.valuation F x := not_lt.1 hv
    rcases h1.lt_or_eq with hlt | heq
    · exact absurd ((nrm_le_one_iff h x).1 hn.le) (not_le.2 hlt)
    · have hu := h.nrm_unit x heq.symm
      linarith
  · intro hv
    exact lt_of_le_of_lt (nrm_le_inv_q_of_valuation_lt_one h x hv) (inv_lt_one_of_one_lt₀ (by exact_mod_cast one_lt_q h))

theorem nrm_le_of_val_le (h : LF O ϖ nrm q) {x y : F}
    (hxy : ValuativeRel.valuation F x ≤ ValuativeRel.valuation F y) : nrm x ≤ nrm y := by
  by_cases hy : y = 0
  · have hv0 : ValuativeRel.valuation F x = 0 := by
      rw [hy, map_zero] at hxy
      exact le_antisymm hxy zero_le
    have hx : x = 0 := (Valuation.zero_iff _).1 hv0
    simp [hx]
  · have hyv : ValuativeRel.valuation F y ≠ 0 := (Valuation.ne_zero_iff _).2 hy
    have hq : ValuativeRel.valuation F (x * y⁻¹) ≤ 1 := by
      rw [map_mul, map_inv₀]
      calc ValuativeRel.valuation F x * (ValuativeRel.valuation F y)⁻¹
          ≤ ValuativeRel.valuation F y * (ValuativeRel.valuation F y)⁻¹ := by gcongr
        _ = 1 := _root_.mul_inv_cancel₀ hyv
    have h1 := (nrm_le_one_iff h _).2 hq
    rw [map_mul, map_inv₀] at h1
    have hpos : 0 < nrm y := nrm.pos hy
    calc nrm x = nrm x * (nrm y)⁻¹ * nrm y := (_root_.inv_mul_cancel_right₀ hpos.ne' _).symm
      _ ≤ 1 * nrm y := mul_le_mul_of_nonneg_right h1 hpos.le
      _ = nrm y := one_mul _

theorem main : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}, LF O ϖ nrm q → 1 < q ∧ ϖ ∈ O ∧ (∀ x : F, nrm x ≤ 1 ↔ x ∈ O) ∧ (∀ x : F, nrm x < 1 ↔ ∃ o ∈ O, x = ϖ * o) ∧ (∀ x : F, x ≠ 0 → ∃ e : ℤ, nrm x = (q : ℝ) ^ (-e) ∧ nrm (x * ϖ ^ (-e)) = 1) ∧ (∀ x y : F, nrm (x + y) ≤ max (nrm x) (nrm y)) ∧ (∀ x : F, nrm x = 1 ↔ ValuativeRel.valuation F x = 1) := by
  intro F _ _ _ _ O ϖ nrm q h
  refine ⟨one_lt_q h, (mem_iff_val_le h ϖ).2 (val_pi_lt_one h).le,
    fun x => (nrm_le_one_iff h x).trans (mem_iff_val_le h x).symm,
    fun x => (nrm_lt_one_iff h x).trans (h.lt_one x), ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨e, he⟩ := val_eq_zpow h hx
    exact ⟨e, nrm_eq_zpow h he, h.nrm_unit _ (val_mul_zpow h he)⟩
  · intro x y
    rcases le_total (ValuativeRel.valuation F x) (ValuativeRel.valuation F y) with hxy | hxy
    · have hs : ValuativeRel.valuation F (x + y) ≤ ValuativeRel.valuation F y :=
        le_trans (Valuation.map_add _ x y) (max_le hxy le_rfl)
      exact le_trans (nrm_le_of_val_le h hs) (le_max_right _ _)
    · have hs : ValuativeRel.valuation F (x + y) ≤ ValuativeRel.valuation F x :=
        le_trans (Valuation.map_add _ x y) (max_le le_rfl hxy)
      exact le_trans (nrm_le_of_val_le h hs) (le_max_left _ _)
  · intro x
    constructor
    · intro hn
      have h1 := (nrm_le_one_iff h x).1 hn.le
      have h2 : ¬ ValuativeRel.valuation F x < 1 := fun hlt => by
        have := (nrm_lt_one_iff h x).2 hlt
        linarith
      exact le_antisymm h1 (not_lt.1 h2)
    · exact h.nrm_unit x

end GlobalTheory.CompanionTheory.QL.NormalisedValue
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.RamifiedPrimeContainsDiscriminantStatement
section
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ramified_prime_contains_discriminant : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (S : Finset (HeightOneSpectrum (𝓞 F))), (∀ v ∉ S, Algebra.IsUnramifiedIn (𝓞 E) v.asIdeal) → ∀ (P : Ideal (𝓞 E)) [P.IsPrime], P ≠ ⊥ → P ∣ differentIdeal ℤ (𝓞 E) → (((discr F).natAbs * ∏ v ∈ S, v.asIdeal.absNorm : ℕ) : 𝓞 E) ∈ P := by
  first | exact @GlobalTheory.CompanionTheory.GlobalFiniteness.natAbs_discr_mul_prod_absNorm_mem_of_dvd_differentIdeal | exact GlobalTheory.CompanionTheory.GlobalFiniteness.natAbs_discr_mul_prod_absNorm_mem_of_dvd_differentIdeal | (intros; apply GlobalTheory.CompanionTheory.GlobalFiniteness.natAbs_discr_mul_prod_absNorm_mem_of_dvd_differentIdeal <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.SkewOperatorBoundedByPolynomialRootsStatement
section
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.skew_operator_bounded_by_polynomial_roots :
    ∀ (M H : Type) [AddCommGroup M] [Module ℂ M] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      (ι : M →ₗ[ℂ] H), Function.Injective ι → ∀ T : Module.End ℂ M,
      (∀ x y, ⟪ι (T x), ι y⟫_ℂ = -⟪ι x, ι (T y)⟫_ℂ) →
      ∀ m : Polynomial ℂ, m ≠ 0 → ∀ κ : ℝ, 0 ≤ κ → (∀ r ∈ m.roots, ‖r‖ ≤ κ) →
      ∀ x, Polynomial.aeval T m x = 0 → ‖ι (T x)‖ ≤ κ * ‖ι x‖ :=
  GlobalTheory.CompanionTheory.SkewSpec.norm_le_of_aeval_eq_zero
end

