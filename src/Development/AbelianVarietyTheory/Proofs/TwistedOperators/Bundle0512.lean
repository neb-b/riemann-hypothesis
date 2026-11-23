module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1243
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1665
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1531
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1281
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitEqNormCompletionTensorOfIsInertAt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftVAlgebraMapMul
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0370
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0393
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0337
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0497
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PureTensorOZeroEqJetP
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacuumFockOfThetaSquareIntegrable
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0499
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0476

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIntegralGeneratorSplitPlaceCmExtension
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

namespace GlobalTheory.SplitGen

open IsDedekindDomain.HeightOneSpectrum Polynomial

theorem exists_integral_gen_split : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ v : Pl (F := F), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v →
    ∃ (a : 𝓞 E) (b c : 𝓞 F), (a : E) ^ 2 + algebraMap F E (b : F) * a + algebraMap F E (c : F) = 0 ∧
      σ (a : E) = -algebraMap F E (b : F) - a ∧ c ∈ v.asIdeal ∧ b ∉ v.asIdeal := by
  intro F E _ _ _ _ _ σ B hB v hv
  obtain ⟨P, Q, hPQ, hPv, hQv⟩ := hv
  have hσ := hB.cm
  have h2 : Module.finrank F E = 2 := hσ.2.2.1
  haveI : IsGalois ℚ E := hB.galois
  haveI : IsGalois F E := IsGalois.tower_top_of_isGalois ℚ F E
  have hPo : P.asIdeal ∈ v.asIdeal.primesOver (𝓞 E) := ⟨P.isPrime, ⟨hPv.symm⟩⟩
  have hQo : Q.asIdeal ∈ v.asIdeal.primesOver (𝓞 E) := ⟨Q.isPrime, ⟨hQv.symm⟩⟩
  obtain ⟨g, hg⟩ := Ideal.exists_comap_galRestrict_eq (𝓞 F) F E (𝓞 E) hPo hQo
  have hgQ : ∀ x : 𝓞 E, x ∈ Q.asIdeal → galRestrict (𝓞 F) F E (𝓞 E) g x ∈ P.asIdeal := by
    intro x hx
    rw [← hg] at hx
    exact hx
  have hgE : ∀ x : 𝓞 E, ((galRestrict (𝓞 F) F E (𝓞 E) g x : 𝓞 E) : E) = g (x : E) :=
    fun x => algebraMap_galRestrict_apply (𝓞 F) g x

  have hne : P.asIdeal ≠ Q.asIdeal := fun h => hPQ (HeightOneSpectrum.ext h)
  have htop := Ideal.IsMaximal.coprime_of_ne P.isMaximal Q.isMaximal hne
  obtain ⟨a, haP, j, hjQ, haj⟩ := Submodule.mem_sup.1 (htop ▸ Submodule.mem_top : (1 : 𝓞 E) ∈ P.asIdeal ⊔ Q.asIdeal)
  have ha1Q : a - 1 ∈ Q.asIdeal := by
    have : a - 1 = -j := by rw [← haj]; ring
    rw [this]; exact neg_mem hjQ
  have hga1 : galRestrict (𝓞 F) F E (𝓞 E) g a - 1 ∈ P.asIdeal := by
    have := hgQ _ ha1Q
    rwa [map_sub, map_one] at this
  have h1P : (1 : 𝓞 E) ∉ P.asIdeal := fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h)
  have hga : g (a : E) ≠ a := by
    intro h
    apply h1P
    have e : galRestrict (𝓞 F) F E (𝓞 E) g a = a := by
      apply RingOfIntegers.ext
      rw [hgE]; exact h
    have := P.asIdeal.sub_mem haP hga1
    rw [e] at this
    simpa using this
  have hnot : (a : E) ∉ (algebraMap F E).range := by
    rintro ⟨x, hx⟩
    apply hga
    rw [← hx, AlgEquiv.commutes]
  have hi : IsIntegral (𝓞 F) a := Algebra.IsIntegral.isIntegral a
  have hmap : minpoly F (a : E) = (minpoly (𝓞 F) a).map (algebraMap (𝓞 F) F) :=
    minpoly.isIntegrallyClosed_eq_field_fractions F E hi
  have hdeg : (minpoly F (a : E)).natDegree = (minpoly (𝓞 F) a).natDegree := by
    rw [hmap, (minpoly.monic hi).natDegree_map]
  have hge : 2 ≤ (minpoly (𝓞 F) a).natDegree := by
    rw [← hdeg]
    exact (minpoly.two_le_natDegree_iff (Algebra.IsIntegral.isIntegral _)).2 hnot
  have hle : (minpoly F (a : E)).natDegree ≤ 2 := h2 ▸ minpoly.natDegree_le (a : E)
  obtain ⟨b, c, hbc⟩ := isMonicOfDegree_two_iff.1
    (⟨by omega, minpoly.monic hi⟩ : IsMonicOfDegree (minpoly (𝓞 F) a) 2)
  have hq0 : a ^ 2 + algebraMap _ _ b * a + algebraMap _ _ c = 0 := by
    have := minpoly.aeval (𝓞 F) a
    rw [hbc] at this
    simpa using this
  have hq : (a : E) ^ 2 + algebraMap F E (b : F) * a + algebraMap F E (c : F) = 0 := by
    have := congrArg (algebraMap (𝓞 E) E) hq0
    simp only [map_add (f := _), map_mul, map_pow, map_zero] at this
    exact this
  have hli : LinearIndependent F ![(1 : E), a] := by
    rw [LinearIndependent.pair_iff' one_ne_zero]
    intro x hx
    exact hnot ⟨x, by rw [Algebra.algebraMap_eq_smul_one, hx]⟩
  let Bs := basisOfLinearIndependentOfCardEqFinrank hli (by simp [h2])
  have hBs : ⇑Bs = ![(1 : E), a] := coe_basisOfLinearIndependentOfCardEqFinrank _ _
  have hσa : σ (a : E) ≠ a := by
    intro hfix
    obtain ⟨x, hx⟩ := GlobalTheory.InertUnitNorm.exists_ne_of_isCMExt σ hσ
    apply hx
    have : σ.toLinearMap = LinearMap.id := by
      refine Bs.ext fun i => ?_
      fin_cases i
      · simp [hBs]
      · simp [hBs, hfix]
    exact congrArg (fun f : E →ₗ[F] E => f x) this
  have hqσ : σ (a : E) ^ 2 + algebraMap F E (b : F) * σ a + algebraMap F E (c : F) = 0 := by
    have := congrArg σ hq
    simpa only [map_add (f := _), map_mul, map_pow, AlgHom.commutes, map_zero] using this
  have hconj : σ (a : E) = -algebraMap F E (b : F) - a := by
    have hm : (σ (a : E) - a) * (σ a + a + algebraMap F E (b : F)) = 0 := by
      linear_combination hqσ - hq
    rcases mul_eq_zero.1 hm with h | h
    · exact absurd (sub_eq_zero.1 h) hσa
    · linear_combination h
  have hqg : g (a : E) ^ 2 + algebraMap F E (b : F) * g a + algebraMap F E (c : F) = 0 := by
    have := congrArg g hq
    simpa only [map_add (f := _), map_mul, map_pow, AlgEquiv.commutes, map_zero] using this
  have hgconj : g (a : E) = -algebraMap F E (b : F) - a := by
    have hm : (g (a : E) - a) * (g a + a + algebraMap F E (b : F)) = 0 := by
      linear_combination hqg - hq
    rcases mul_eq_zero.1 hm with h | h
    · exact absurd (sub_eq_zero.1 h) hga
    · linear_combination h
  have hgO : galRestrict (𝓞 F) F E (𝓞 E) g a = -algebraMap (𝓞 F) (𝓞 E) b - a := by
    apply RingOfIntegers.ext
    rw [hgE, hgconj]
    simp only [map_sub, map_neg]
    rfl
  refine ⟨a, b, c, hq, hconj, ?_, ?_⟩
  ·
    rw [← hPv, Ideal.mem_comap]
    have e : algebraMap (𝓞 F) (𝓞 E) c = a * (-algebraMap (𝓞 F) (𝓞 E) b - a) := by
      linear_combination hq0
    rw [e]
    exact P.asIdeal.mul_mem_right _ haP
  · intro hb
    rw [← hPv, Ideal.mem_comap] at hb
    apply h1P
    rw [hgO] at hga1
    have e : (1 : 𝓞 E) = -(-algebraMap (𝓞 F) (𝓞 E) b - a - 1) - algebraMap (𝓞 F) (𝓞 E) b - a := by ring
    rw [e]
    exact P.asIdeal.sub_mem (P.asIdeal.sub_mem (neg_mem hga1) hb) haP

end GlobalTheory.SplitGen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIntegralSiegelParabolicOfConjugateIdempote
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.SplitConjPar

section FinTwoTypeFamily
variable {R : Type} [CommRing R] {d : ℕ}

def blk2 (d : ℕ) (a b : R) : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) R :=
  Matrix.fromBlocks (a • 1) (b • 1) (b • 1) (a • 1)

theorem symmetricScalarBlockMatrix_mul (a b a' b' : R) : blk2 d a b * blk2 d a' b' = blk2 d (a * a' + b * b') (a * b' + b * a') := by
  simp only [blk2, Matrix.fromBlocks_multiply, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul, ← add_smul]
  congr 2 <;> ring

theorem symmetricScalarBlockMatrix_one_zero : blk2 d (1 : R) 0 = 1 := by
  simp [blk2, Matrix.fromBlocks_one]

theorem symmetricScalarBlockMatrix_transpose (a b : R) : (blk2 d a b)ᵀ = blk2 d a b := by
  simp [blk2, Matrix.fromBlocks_transpose, Matrix.transpose_smul]

theorem symmetricScalarBlockMatrix_map (c : R → R) (h0 : c 0 = 0) (a b : R) : (blk2 d a b).map c = blk2 d (c a) (c b) := by
  ext (i | i) (j | j) <;> by_cases h : i = j <;> simp [blk2, Matrix.one_apply, h, h0]

theorem symmetricScalarBlockMatrix_mul_gram_mul (J : Matrix (Fin d) (Fin d) R) (a b a' b' : R) :
    blk2 d a b * Matrix.fromBlocks J 0 0 (-J) * blk2 d a' b' =
      Matrix.fromBlocks ((a * a' - b * b') • J) ((a * b' - b * a') • J) ((b * a' - a * b') • J) ((b * b' - a * a') • J) := by
  simp only [blk2, Matrix.fromBlocks_multiply, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one,
    Matrix.zero_mul, Matrix.mul_zero, smul_zero, zero_add, add_zero, smul_neg, Matrix.neg_mul, Matrix.mul_neg, smul_smul]
  congr 1 <;> module

theorem symmetricScalarBlockMatrix_mul_diagonalColumns (a b : R) :
    blk2 d a b * (Matrix.fromRows (1 : Matrix (Fin d) (Fin d) R) (1 : Matrix (Fin d) (Fin d) R) : Matrix (Fin d ⊕ Fin d) (Fin d) R) =
      (Matrix.fromRows (1 : Matrix (Fin d) (Fin d) R) (1 : Matrix (Fin d) (Fin d) R) : Matrix (Fin d ⊕ Fin d) (Fin d) R) * ((a + b) • (1 : Matrix (Fin d) (Fin d) R)) := by
  simp only [blk2, Matrix.fromBlocks_mul_fromRows, Matrix.fromRows_mul, Matrix.mul_one, Matrix.one_mul, add_comm b a, ← add_smul]

theorem symmetricScalarBlockMatrix_mul_antidiagonalColumns (a b : R) :
    blk2 d a b * (Matrix.fromRows (1 : Matrix (Fin d) (Fin d) R) (-(1 : Matrix (Fin d) (Fin d) R)) : Matrix (Fin d ⊕ Fin d) (Fin d) R) =
      (Matrix.fromRows (1 : Matrix (Fin d) (Fin d) R) (-(1 : Matrix (Fin d) (Fin d) R)) : Matrix (Fin d ⊕ Fin d) (Fin d) R) * ((a - b) • (1 : Matrix (Fin d) (Fin d) R)) := by
  simp only [blk2, Matrix.fromBlocks_mul_fromRows, Matrix.fromRows_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_neg,
    Matrix.neg_mul]
  congr 1 <;> module

theorem symmetricScalarBlockMatrix_sub_one (a b : R) : blk2 d a b - 1 = blk2 d (a - 1) b := by
  ext (i | i) (j | j) <;> by_cases h : i = j <;> simp [blk2, Matrix.one_apply, h]

theorem symmetricScalarBlockMatrix_mulVec_inl (a b : R) (z : Fin d ⊕ Fin d → R) (i : Fin d) :
    (blk2 d a b *ᵥ z) (Sum.inl i) = a * z (Sum.inl i) + b * z (Sum.inr i) := by
  simp [blk2, Matrix.fromBlocks_mulVec, Matrix.smul_mulVec]

theorem symmetricScalarBlockMatrix_mulVec_inr (a b : R) (z : Fin d ⊕ Fin d → R) (i : Fin d) :
    (blk2 d a b *ᵥ z) (Sum.inr i) = b * z (Sum.inl i) + a * z (Sum.inr i) := by
  simp [blk2, Matrix.fromBlocks_mulVec, Matrix.smul_mulVec]

end FinTwoTypeFamily

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem evFin_half_mem (v : Pl (F := F)) (h2 : (2 : 𝓞 F) ∉ v.asIdeal) :
    evFin F v (⅟2 : AF F) ∈ v.adicCompletionIntegers F := by
  have hv2 : Valued.v (2 : Fv F v) = 1 := by
    have e : ((algebraMap (𝓞 F) (v.adicCompletionIntegers F) 2 : v.adicCompletionIntegers F) : Fv F v) = 2 := by
      rw [map_ofNat]; rfl
    have hn := (GlobalTheory.InertUnitNorm.algebraMap_mem_maximalIdeal_iff v 2).not.2 h2
    rw [GlobalTheory.InertUnitNorm.mem_maximalIdeal_iff_valued_lt_one, e] at hn
    have hle : Valued.v (2 : Fv F v) ≤ 1 := by
      rw [← e]; exact (algebraMap (𝓞 F) (v.adicCompletionIntegers F) 2).2
    exact le_antisymm hle (not_lt.1 hn)
  have hx : (2 : Fv F v) * evFin F v (⅟2 : AF F) = 1 := by
    rw [← map_ofNat (evFin F v) 2, ← map_mul, mul_invOf_self, map_one]
  rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
  have := congrArg Valued.v hx
  rw [map_mul, hv2, one_mul, map_one] at this
  exact this.le

theorem symmetricScalarBlockMatrix_mulVec_mem_doubledLattice {d : ℕ} {W : Spc F E d} {v : Pl (F := F)} {a b : AE F E} (ha : GlobalTheory.SplitConj.Mult W v a)
    (hb : GlobalTheory.SplitConj.Mult W v b) (z : Fin d ⊕ Fin d → AE F E) (hz : z ∈ GlobalTheory.InertDbl.latAtD W v) :
    blk2 d a b *ᵥ z ∈ GlobalTheory.InertDbl.latAtD W v := by
  constructor
  · simp only [symmetricScalarBlockMatrix_mulVec_inl]
    exact add_mem (ha _ hz.1) (hb _ hz.2)
  · simp only [symmetricScalarBlockMatrix_mulVec_inr]
    exact add_mem (hb _ hz.1) (ha _ hz.2)

theorem mult_neg {d : ℕ} {W : Spc F E d} {v : Pl (F := F)} {a : AE F E} (ha : GlobalTheory.SplitConj.Mult W v a) :
    GlobalTheory.SplitConj.Mult W v (-a) := fun z hz => by
  have : (fun i => -a * z i) = -(fun i => a * z i) := by ext i; simp
  rw [this]; exact neg_mem (ha z hz)

theorem mult_sub {d : ℕ} {W : Spc F E d} {v : Pl (F := F)} {a b : AE F E} (ha : GlobalTheory.SplitConj.Mult W v a)
    (hb : GlobalTheory.SplitConj.Mult W v b) : GlobalTheory.SplitConj.Mult W v (a - b) := by
  rw [sub_eq_add_neg]; exact GlobalTheory.SplitConj.mult_add ha (mult_neg hb)

theorem mult_one {d : ℕ} (W : Spc F E d) (v : Pl (F := F)) : GlobalTheory.SplitConj.Mult W v 1 := fun z hz => by
  simpa using hz

theorem exists_par : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (d : ℕ) (W : Spc F E d) (v : Pl (F := F)), (2 : 𝓞 F) ∉ v.asIdeal →
    ∀ Eid : AE F E, Eid * Eid = Eid → Eid + cA σ Eid = algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1) →
    Eid * cA σ Eid = 0 →
    (∀ z ∈ GlobalTheory.InertSph.latAt W v, (fun i => Eid * z i) ∈ GlobalTheory.InertSph.latAt W v) →
    ∃ s ∈ GlobalTheory.InertDbl.ParD σ W v,
      GlobalTheory.InertDbl.matD s * diagCols (Fin d) =
        diagCols (Fin d) * ((1 - (⅟2 : AF F) • Eid) • (1 : Matrix (Fin d) (Fin d) (AE F E))) ∧
      GlobalTheory.InertDbl.matD s * GlobalTheory.InertDbl.antiCols d =
        GlobalTheory.InertDbl.antiCols d * ((1 + cA σ Eid) • (1 : Matrix (Fin d) (Fin d) (AE F E))) := by
  intro F E _ _ _ _ _ σ B _ d W v h2 A hA hAe hAB hL
  set h : AE F E := algebraMap (AF F) (AE F E) (⅟2) with hh
  set e : AE F E := algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1) with he
  set A' : AE F E := cA σ A with hA'
  have h2h : 2 * h = 1 := by
    rw [hh, ← map_ofNat (algebraMap (AF F) (AE F E)) 2, ← map_mul, mul_invOf_self, map_one]
  have hee : e * e = e := by rw [he, ← map_mul, ← GlobalTheory.SplitConj.liftV_mul, one_mul]
  have hAe' : A * e = A := by rw [← hAe, mul_add, hA, hAB, add_zero]
  have hA'e : A' = e - A := by rw [← hAe]; ring
  have hA'A' : A' * A' = A' := by rw [hA'e]; linear_combination hee - 2 * hAe' + hA
  have ch : cA σ h = h := (cA σ).commutes _
  have ce : cA σ e = e := (cA σ).commutes _
  have cA' : cA σ A' = A := by rw [hA'e, map_sub, ce, ← hA', hA'e]; ring
  have hx : (1 - h * A) * (1 + A) = 1 := by linear_combination (-h) * hA - A * h2h
  have hy : (1 + A') * (1 - h * A') = 1 := by linear_combination (-h) * hA'A' - A' * h2h
  have cx : cA σ (1 - h * A) = 1 - h * A' := by rw [map_sub, map_one, map_mul, ch]
  have cy : cA σ (1 + A') = 1 + A := by rw [map_add (f := _), map_one, cA']
  have Mh : GlobalTheory.SplitConj.Mult W v h := GlobalTheory.SplitConj.mult_algebraMap W v _ (evFin_half_mem v h2)
  have Me : GlobalTheory.SplitConj.Mult W v e := GlobalTheory.SplitConj.mult_algebraMap W v _ (by
    rw [GlobalTheory.LatVac.evFin_liftV]; exact one_mem _)
  have MA : GlobalTheory.SplitConj.Mult W v A := hL
  have MA' : GlobalTheory.SplitConj.Mult W v A' := hA'e ▸ mult_sub Me MA
  have Mx := mult_sub (mult_one W v) (GlobalTheory.SplitConj.mult_mul Mh MA)
  have Mx' := GlobalTheory.SplitConj.mult_add (mult_one W v) MA
  have My := GlobalTheory.SplitConj.mult_add (mult_one W v) MA'
  have My' := mult_sub (mult_one W v) (GlobalTheory.SplitConj.mult_mul Mh MA')
  have hu : ∀ u : AF F, evFin F v u = 0 →
      algebraMap (AF F) (AE F E) u * A = 0 ∧ algebraMap (AF F) (AE F E) u * A' = 0 := by
    intro u hu
    have h1 : algebraMap (AF F) (AE F E) u * e = 0 := by
      have := GlobalTheory.LatVac.at_liftV v 1 u hu
      rw [he, ← map_mul, ← smul_eq_mul, this, map_zero]
    have h3 : algebraMap (AF F) (AE F E) u * A = 0 := by
      rw [← hAe']; linear_combination A * h1
    exact ⟨h3, by rw [hA'e, mul_sub, h1, h3, sub_zero]⟩
  have hsm : (⅟2 : AF F) • A = h * A := Algebra.smul_def _ _
  rw [hsm]
  generalize hxe : 1 - h * A = x at *
  generalize hxe' : 1 + A = x' at *
  generalize hye : 1 + A' = y at *
  generalize hye' : 1 - h * A' = y' at *
  have i1 : h * (x + y) * (h * (x' + y')) + h * (x - y) * (h * (x' - y')) = 1 := by
    linear_combination 2 * h * h * hx + 2 * h * h * hy + (2 * h + 1) * h2h
  have i2 : h * (x + y) * (h * (x' - y')) + h * (x - y) * (h * (x' + y')) = 0 := by
    linear_combination 2 * h * h * hx - 2 * h * h * hy
  have i3 : h * (x' + y') * (h * (x + y)) + h * (x' - y') * (h * (x - y)) = 1 := by
    linear_combination i1
  have i4 : h * (x' + y') * (h * (x - y)) + h * (x' - y') * (h * (x + y)) = 0 := by
    linear_combination i2
  have ca : cA σ (h * (x + y)) = h * (x' + y') := by rw [map_mul, map_add (f := _), ch, cx, cy, add_comm]
  have cb : cA σ (h * (x - y)) = -(h * (x' - y')) := by rw [map_mul, map_sub, ch, cx, cy]; ring
  have hmem : (blk2 d (h * (x + y)) (h * (x - y)))ᵀ * dbl (incM F W.J) *
      (blk2 d (h * (x + y)) (h * (x - y))).map (cA σ) = dbl (incM F W.J) := by
    rw [symmetricScalarBlockMatrix_transpose, symmetricScalarBlockMatrix_map _ (map_zero _), ca, cb, dbl, symmetricScalarBlockMatrix_mul_gram_mul]
    have j1 : h * (x + y) * (h * (x' + y')) - h * (x - y) * -(h * (x' - y')) = 1 := by linear_combination i1
    have j2 : h * (x + y) * -(h * (x' - y')) - h * (x - y) * (h * (x' + y')) = 0 := by linear_combination -i2
    have j3 : h * (x - y) * (h * (x' + y')) - h * (x + y) * -(h * (x' - y')) = 0 := by linear_combination i2
    have j4 : h * (x - y) * -(h * (x' - y')) - h * (x + y) * (h * (x' + y')) = -1 := by linear_combination -i1
    rw [j1, j2, j3, j4, one_smul, zero_smul, neg_smul, one_smul]
  let s : GlobalTheory.InertDbl.UD σ W :=
    ⟨⟨blk2 d (h * (x + y)) (h * (x - y)), blk2 d (h * (x' + y')) (h * (x' - y')),
      by rw [symmetricScalarBlockMatrix_mul, i1, i2, symmetricScalarBlockMatrix_one_zero], by rw [symmetricScalarBlockMatrix_mul, i3, i4, symmetricScalarBlockMatrix_one_zero]⟩, hmem⟩
  have hs : GlobalTheory.InertDbl.matD s = blk2 d (h * (x + y)) (h * (x - y)) := rfl
  have hs' : GlobalTheory.InertDbl.matD s⁻¹ = blk2 d (h * (x' + y')) (h * (x' - y')) := rfl
  have hd : GlobalTheory.InertDbl.matD s * diagCols (Fin d) = diagCols (Fin d) * (x • (1 : Matrix (Fin d) (Fin d) (AE F E))) := by
    have : h * (x + y) + h * (x - y) = x := by linear_combination x * h2h
    have k := symmetricScalarBlockMatrix_mul_diagonalColumns (d := d) (h * (x + y)) (h * (x - y))
    rw [this] at k
    exact k
  refine ⟨s, ⟨⟨?_, ?_⟩, ⟨x • 1, x' • 1, ?_, ?_⟩, hd⟩, hd, ?_⟩
  · intro u hu0
    obtain ⟨u1, u2⟩ := hu u hu0
    have k1 : u • (h * (x + y) - 1) = 0 := by
      rw [Algebra.smul_def, ← hxe, ← hye]
      linear_combination (-h * h) * u1 + h * u2 + algebraMap (AF F) (AE F E) u * h2h
    have k2 : u • (h * (x - y)) = 0 := by
      rw [Algebra.smul_def, ← hxe, ← hye]
      linear_combination (-h * h) * u1 - h * u2
    rw [hs, symmetricScalarBlockMatrix_sub_one, blk2, Matrix.fromBlocks_smul, ← smul_assoc, ← smul_assoc, k1, k2, zero_smul,
      Matrix.fromBlocks_zero]
  · intro z hz
    rw [hs, hs']
    exact ⟨symmetricScalarBlockMatrix_mulVec_mem_doubledLattice (GlobalTheory.SplitConj.mult_mul Mh (GlobalTheory.SplitConj.mult_add Mx My))
        (GlobalTheory.SplitConj.mult_mul Mh (mult_sub Mx My)) z hz,
      symmetricScalarBlockMatrix_mulVec_mem_doubledLattice (GlobalTheory.SplitConj.mult_mul Mh (GlobalTheory.SplitConj.mult_add Mx' My'))
        (GlobalTheory.SplitConj.mult_mul Mh (mult_sub Mx' My')) z hz⟩
  · rw [Matrix.smul_mul, Matrix.one_mul, smul_smul, hx, one_smul]
  · rw [Matrix.smul_mul, Matrix.one_mul, smul_smul, mul_comm, hx, one_smul]
  · have : h * (x + y) - h * (x - y) = y := by linear_combination y * h2h
    have k := symmetricScalarBlockMatrix_mul_antidiagonalColumns (d := d) (h * (x + y)) (h * (x - y))
    rw [this] at k
    exact k

end GlobalTheory.SplitConjPar

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockGaussianJetsAtOriginEqFockVectors
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockTransl
open Formalism.L2.Ker (VCx DVar derivAt0)

noncomputable section

namespace GlobalTheory.FockTransl.Jet

open Complex

variable {D : D7}

theorem list_prod_toMultiset {ι : Type} (m : ι →₀ ℕ) (g : ι → ℂ) :
    ((Finsupp.toMultiset m).toList.map g).prod = m.prod fun l n => g l ^ n := by
  rw [Multiset.prod_map_toList]
  induction m using Finsupp.induction with
  | zero => simp
  | single_add a n g' ha hn ih =>
    rw [map_add (f := _), Multiset.map_add (f := _), Multiset.prod_add, ih, Finsupp.toMultiset_single, Finsupp.prod_add_index']
    · simp [Multiset.map_nsmul, Multiset.prod_nsmul]
    · simp
    · intro a b c; rw [pow_add]

theorem crOp_const_mul {S T : HSp D} (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (l : DVar D.what₂.Tau S.rank T.rank)
    (c : ℂ) (Φ : VCx D.what₂.Tau S.rank T.rank → ℂ) (z : VCx D.what₂.Tau S.rank T.rank) (hΦ : DifferentiableAt ℝ Φ z) :
    crOp A B l (fun z => c * Φ z) z = c * crOp A B l Φ z := by
  unfold crOp
  rw [fderiv_const_mul hΦ]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem jet_eq_fock : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (σ : (D.what₂.Tau → ℂ) →+ AE D), IsStdChar D ψ (-1) → GlobalTheory.FockCompare.Chart θ σ → ∀ (S T : HSp D) (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T), ∃ C : (FVar D T.rank S.rank →₀ ℕ) → ℂ, ∀ f : WO S T → ℂ, GlobalTheory.ChainFr.IsVacF ψ θ A B f → ∀ (x : WO S T) (m : FVar D T.rank S.rank →₀ ℕ), derivAt0 (rd ψ σ A B f x) m = C m * GlobalTheory.ChainFr.ptF ψ θ A B f (MvPolynomial.monomial m 1) x := by
  intro D ψ θ σ hψ hσ S T A B
  have L1 : ∀ (D : D7) (S T : HSp D) (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (l : DVar D.what₂.Tau S.rank T.rank), (∀ a b, GlobalTheory.FockTransl.Jet.lamF A B l (a + b) = GlobalTheory.FockTransl.Jet.lamF A B l a + GlobalTheory.FockTransl.Jet.lamF A B l b) ∧ ∀ (t : ℂ) a, GlobalTheory.FockTransl.Jet.lamF A B l (t • a) = conj t * GlobalTheory.FockTransl.Jet.lamF A B l a := _root_.GlobalTheory.FockTransl.Jet.lamF_antilinear
  have L2 : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (σ : (D.what₂.Tau → ℂ) →+ AE D), IsStdChar D ψ (-1) → GlobalTheory.FockCompare.Chart θ σ → ∀ (S T : HSp D) (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (h : WO S T → ℂ) (x : WO S T) (l : FVar D T.rank S.rank) (z : VCx D.what₂.Tau S.rank T.rank), DifferentiableAt ℝ (rd ψ σ A B h x) z → rd ψ σ A B (aPlusAll (heisO ψ S T) θ (fun τ => cplxO (A.cart τ) (B.cart τ)) A.onb B.onb l h) x z = (2 / (fockScale D l.1 : ℂ)) * GlobalTheory.FockTransl.Jet.crOp A B l (rd ψ σ A B h x) z := _root_.GlobalTheory.FockTransl.Jet.rd_aPlusAll
  refine ⟨fun m => m.prod fun l n => ((fockScale D l.1 : ℂ) / 2) ^ n, fun f hf x m => ?_⟩
  set Aop := aPlusAll (heisO ψ S T) θ (fun τ => cplxO (A.cart τ) (B.cart τ)) A.onb B.onb with hAop
  have hent : Differentiable ℂ (rd ψ σ A B f x) := _root_.GlobalTheory.FockEntire.rd_differentiable D ψ θ σ hψ hσ S T A B f hf x
  have hops := GlobalTheory.Ker.CreOp.foldr_creation_zero _ _ Formalism.L2.Ker.coordX (GlobalTheory.FockTransl.Jet.lamF A B) (rd ψ σ A B f x)
    (fun l => L1 D S T A B l) hent (GlobalTheory.FockTransl.Jet.crOp A B) (fun _ _ _ => rfl)
  have key : ∀ L : List (FVar D T.rank S.rank), rd ψ σ A B (L.foldr (fun i g => Aop i g) f) x =
      fun z => (L.map fun l => 2 / (fockScale D l.1 : ℂ)).prod * L.foldr (GlobalTheory.FockTransl.Jet.crOp A B) (rd ψ σ A B f x) z := by
    intro L
    induction L with
    | nil => funext z; simp
    | cons l L ih =>
      funext z
      have hd0 : Differentiable ℝ (L.foldr (GlobalTheory.FockTransl.Jet.crOp A B) (rd ψ σ A B f x)) :=
        (hops L).1.differentiable (by simp)
      have hd : DifferentiableAt ℝ (rd ψ σ A B (L.foldr (fun i g => Aop i g) f) x) z := by
        rw [ih]; exact ((hd0.const_mul _) z)
      rw [List.foldr_cons, L2 D ψ θ σ hψ hσ S T A B _ x l z hd, ih, GlobalTheory.FockTransl.Jet.crOp_const_mul A B l _ _ z (hd0 z),
        List.foldr_cons, List.map_cons, List.prod_cons]
      ring
  have h0 : ∀ h : WO S T → ℂ, rd ψ σ A B h x 0 = h x := by
    intro h
    have hz : fockPt σ A B (0 : VCx D.what₂.Tau S.rank T.rank) = 0 := by
      have e : (fun τ => fockMat A B τ ((0 : VCx D.what₂.Tau S.rank T.rank) τ)) = 0 := by
        funext τ; simp [fockMat]
      rw [fockPt, e]; exact (FockCompare.iotaW σ T S).map_zero
    simp [rd, gq, hz, GlobalTheory.OrientedHeis.heisO_zero]
  have hfs : ∀ l : FVar D T.rank S.rank, (fockScale D l.1 : ℂ) ≠ 0 := fun l => GlobalTheory.VacuumFockLaws.fockScale_ne l.1
  have hval : opPow Aop m f x = (m.prod fun l n => (2 / (fockScale D l.1 : ℂ)) ^ n) * derivAt0 (rd ψ σ A B f x) m := by
    rw [opPow, ← h0 (List.foldr _ f _), key]
    beta_reduce
    rw [(hops _).2, derivAt0, GlobalTheory.AdForm.JetRead.iter_cast _ _ _ (Multiset.length_toList _) Formalism.L2.Ker.coordX,
      list_prod_toMultiset]
  have hpt : GlobalTheory.ChainFr.ptF ψ θ A B f (MvPolynomial.monomial m 1) x = opPow Aop m f x := by
    have e : MvPolynomial.basisMonomials (FVar D T.rank S.rank) ℂ m = MvPolynomial.monomial m 1 := by
      rw [MvPolynomial.coe_basisMonomials]
    rw [GlobalTheory.ChainFr.ptF, pureTensorO, pureTensorL, ← e, Module.Basis.constr_basis]
  rw [hpt, hval, ← mul_assoc, ← Finsupp.prod_mul]
  have e1 : (m.prod fun l n => ((fockScale D l.1 : ℂ) / 2) ^ n * (2 / (fockScale D l.1 : ℂ)) ^ n) = 1 := by
    refine Finset.prod_eq_one fun l _ => ?_
    beta_reduce
    rw [← mul_pow, div_mul_div_comm, mul_comm (fockScale D l.1 : ℂ) 2, div_self (mul_ne_zero two_ne_zero (hfs l)), one_pow]
  rw [e1, one_mul]

end GlobalTheory.FockTransl.Jet

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsWeilDatumComplexConjugateOfNegHermitianSpaceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Chain.RealIt GlobalTheory.PairLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isWeilDatum_complexConjugate_of_negHermitianSpace : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (ω : GlobalTheory.Grid.WRep S T), GlobalTheory.Grid.IsWeil ψ true S T χS χT ω → IsWeilDatumO ψ S T χS⁻¹ χT⁻¹ (GlobalTheory.AdjTr.conjRep ω) := by
  first | exact @GlobalTheory.ConjWeilBack.weil_conjRep_of_neg | exact GlobalTheory.ConjWeilBack.weil_conjRep_of_neg | (intros; apply GlobalTheory.ConjWeilBack.weil_conjRep_of_neg <;> assumption)
end

