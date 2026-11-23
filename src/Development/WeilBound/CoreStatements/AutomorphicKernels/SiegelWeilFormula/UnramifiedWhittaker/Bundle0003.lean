module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.Bundle0002

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.LocCAsm
section
noncomputable section

namespace PositivityTheory.SiegelWeilFormula.Gunr

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory PositivityTheory.PfSWUS.Loc PositivityTheory.SiegelWeilFormula.Gen Filter Topology
open scoped TensorProduct

set_option linter.unusedSectionVars false

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {M n d : ℕ} {J : Matrix (Fin M) (Fin M) E} {T : Matrix (Fin n) (Fin n) E}
  {bs : Module.Basis (Fin d) F E} {v : HeightOneSpectrum (𝓞 F)} {ψv : Fv F v → ℂ} {S : Subring (Fv F v ⊗[F] E)}
  {σS : S →+* S} {ϖ : Fv F v} {ε : ℤ}

namespace GoodLoc

variable (hG : GoodLoc σ J T bs v ψv S σS ϖ ε)
include hG

theorem coe_pS : ((hG.pS : S) : Fv F v ⊗[F] E) = algebraMap (Fv F v) (Fv F v ⊗[F] E) ϖ := rfl

theorem cT_smul_pS (k : ℕ) (X : Matrix (Fin n) (Fin n) S) (hX : PositivityTheory.PfSWUS.Loc.cT σS X = X) :
    PositivityTheory.PfSWUS.Loc.cT σS (hG.pS • X) = hG.pS • X := by
  ext a b
  have h1 := congrFun (congrFun hX a) b
  simp only [PositivityTheory.PfSWUS.Loc.cT, Matrix.transpose_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul,
    map_mul] at h1 ⊢
  have h2 : σS hG.pS = hG.pS := hG.quad.fix_ϖ
  rw [h2, h1]

theorem hermLev_succ (k : ℕ) (X : Matrix (Fin n) (Fin n) S) (hX : PositivityTheory.PfSWUS.Loc.cT σS X = X) :
    hG.hermLev (k + 1) (hG.pS • X) (hG.cT_smul_pS k X hX) = hG.hermLev k X hX := by
  apply Subtype.ext
  funext a b
  show (ϖ ^ (k + 1))⁻¹ • (((hG.pS • X) a b : S) : Fv F v ⊗[F] E) = (ϖ ^ k)⁻¹ • ((X a b : S) : Fv F v ⊗[F] E)
  rw [Matrix.smul_apply, smul_eq_mul, Subring.coe_mul, coe_pS, ← Algebra.smul_def, smul_smul, pow_succ, mul_inv,
    mul_assoc, inv_mul_cancel₀ hG.unif_ne, mul_one]

def liftH {k : ℕ} (B : hermMod σS hG.pS n k) : Matrix (Fin n) (Fin n) S := Classical.choose B.2

theorem liftH_herm {k : ℕ} (B : hermMod σS hG.pS n k) : PositivityTheory.PfSWUS.Loc.cT σS (hG.liftH B) = hG.liftH B :=
  (Classical.choose_spec B.2).1

theorem red_liftH {k : ℕ} (B : hermMod σS hG.pS n k) : red hG.pS k (hG.liftH B) = B.1 :=
  (Classical.choose_spec B.2).2

def iota (k : ℕ) (B : hermMod σS hG.pS n k) : HermR (Fv F v) σ n ⧸ H0 S σ n :=
  QuotientAddGroup.mk (hG.hermLev k (hG.liftH B) (hG.liftH_herm B))

theorem iota_eq (hCL : ClassLev) (k : ℕ) (X : Matrix (Fin n) (Fin n) S) (hX : PositivityTheory.PfSWUS.Loc.cT σS X = X)
    (B : hermMod σS hG.pS n k) (hB : red hG.pS k X = B.1) :
    hG.iota k B = QuotientAddGroup.mk (hG.hermLev k X hX) := by
  unfold iota
  rw [QuotientAddGroup.eq, neg_add_eq_sub]
  exact (hCL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hG k X (hG.liftH B) hX (hG.liftH_herm B)).2 (by rw [hB, hG.red_liftH])

theorem iota_inj (hCL : ClassLev) (k : ℕ) : Function.Injective (hG.iota k) := by
  intro B B' h
  unfold iota at h
  rw [QuotientAddGroup.eq, neg_add_eq_sub] at h
  have := (hCL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hG k (hG.liftH B') (hG.liftH B) (hG.liftH_herm B') (hG.liftH_herm B)).1 h
  rw [hG.red_liftH, hG.red_liftH] at this
  exact Subtype.ext this.symm

theorem iota_succ (hCL : ClassLev) (k : ℕ) (B : hermMod σS hG.pS n k) :
    ∃ B' : hermMod σS hG.pS n (k + 1), hG.iota (k + 1) B' = hG.iota k B := by
  refine ⟨⟨red hG.pS (k + 1) (hG.pS • hG.liftH B), hG.pS • hG.liftH B, hG.cT_smul_pS k _ (hG.liftH_herm B), rfl⟩, ?_⟩
  rw [hG.iota_eq hCL (k + 1) (hG.pS • hG.liftH B) (hG.cT_smul_pS k _ (hG.liftH_herm B)) _ rfl, hG.hermLev_succ]
  rfl

theorem iota_surj (hCL : ClassLev) (hEx : Exhaust) (c : HermR (Fv F v) σ n ⧸ H0 S σ n) :
    ∃ k B, hG.iota k B = c := by
  induction c using QuotientAddGroup.induction_on with
  | H b =>
    obtain ⟨k, X, hX, rfl⟩ := hEx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hG b
    exact ⟨k, ⟨red hG.pS k X, X, hX, rfl⟩, hG.iota_eq hCL k X hX _ rfl⟩

theorem f_lev (hNP : NuPow) (hJ : JtLev) (hNL : NuLev) (hPL : PsiLev) (hT : ∀ a b, σ (T b a) = T a b)
    (μv : Measure (Fin n → Fin M → Fv F v ⊗[F] E)) (hμ : SdW F E σ M J (Fv F v) ψv n μv)
    (lam : Measure (Fin n → Fv F v ⊗[F] E)) (L : AddSubgroup (Fin n → Fv F v ⊗[F] E)) (hlam : lam.IsAddHaarMeasure)
    (hL : (L : Set (Fin n → Fv F v ⊗[F] E)) = latO bs v) (z : ℂ) (k : ℕ) (B : hermMod σS hG.pS n k) :
    whI (Fv F v) σ J ψv μv ((latV bs v).indicator 1) (nu2 lam L L) (hermOf (Fv F v) σ T hT).1 z
      (hG.hermLev k (hG.liftH B) (hG.liftH_herm B)) =
    ((ε : ℂ) ^ M * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(2 * z + n))) ^
        Nat.log (Ideal.absNorm v.asIdeal ^ 2) (nuAt hG.pS B.1) *
      hG.psiLev (c := -1) (neg_mem (one_mem _)) k (Matrix.trace (red hG.pS k (matS S T hG.T_int) * B.1)) := by
  have e1 := hNL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hG lam L hlam hL k (hG.liftH B) (hG.liftH_herm B)
  have e2 := hJ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hG μv hμ k (hG.liftH B) (hG.liftH_herm B)
  have e3 := hPL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hG hT k (hG.liftH B) (hG.liftH_herm B)
  rw [hG.red_liftH] at e1 e2 e3
  have e4 : nuAt hG.pS B.1 = (Ideal.absNorm v.asIdeal ^ 2) ^ Nat.log (Ideal.absNorm v.asIdeal ^ 2) (nuAt hG.pS B.1) :=
    hNP S σS hG.pS _ ε hG.quad n k B.1 B.2
  have hq0 : (Ideal.absNorm v.asIdeal : ℂ) ≠ 0 := by
    have := hG.quad.one_lt
    exact_mod_cast (by omega : Ideal.absNorm v.asIdeal ≠ 0)
  simp only [whI]
  rw [e1, e2, e3]
  congr 1
  set D := Nat.log (Ideal.absNorm v.asIdeal ^ 2) (nuAt hG.pS B.1)
  set q := Ideal.absNorm v.asIdeal
  rw [e4]
  have h5 : ((((q ^ 2) ^ D : ℕ) : ℝ) : ℂ) = ((q : ℂ) ^ (2 * D : ℕ)) := by push_cast; ring
  rw [h5, ← Complex.natCast_cpow_natCast_mul]
  have h6 : ((2 * D : ℕ) : ℂ) * -(z - ((M : ℂ) - n) / 2) = (D : ℂ) * (2 * -(z - ((M : ℂ) - n) / 2)) := by push_cast; ring
  rw [h6, Complex.cpow_nat_mul, ← mul_pow]
  congr 1
  rw [← Complex.cpow_intCast, mul_left_comm, ← Complex.cpow_add _ _ hq0]
  congr 2
  push_cast
  ring

end GoodLoc

end PositivityTheory.SiegelWeilFormula.Gunr

end
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.NormLeOneIffMem
section
noncomputable section

namespace PositivityTheory.SiegelWeilFormula.Gunr

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory PositivityTheory.PfSWUS.Loc PositivityTheory.SiegelWeilFormula.Gen Filter
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem norm_le_one_iff_mem' (v : HeightOneSpectrum (𝓞 F)) (y : Fv F v) :
    ‖y‖ ≤ 1 ↔ y ∈ v.adicCompletionIntegers F := by
  rw [Valued.toNormedField.norm_le_one_iff, HeightOneSpectrum.mem_adicCompletionIntegers]

omit [NumberField F] [NumberField E] in
theorem mem_basisSet_two (σ : E →ₐ[F] E) {d : ℕ} (bs : Module.Basis (Fin d) F E) : (2 : F)⁻¹ ∈ basisSet σ bs := by
  classical
  simp [basisSet]

omit [NumberField F] [NumberField E] in
theorem mem_basisSet_one (σ : E →ₐ[F] E) {d : ℕ} (bs : Module.Basis (Fin d) F E) (k : Fin d) :
    bs.repr 1 k ∈ basisSet σ bs := by
  unfold basisSet
  simp

theorem two_of {σ : E →ₐ[F] E} {d : ℕ} {bs : Module.Basis (Fin d) F E} {v : HeightOneSpectrum (𝓞 F)}
    (hB : IntAt v (basisSet σ bs)) : ‖(2 : Fv F v)‖ = 1 := by
  have h1 := hB _ (mem_basisSet_two σ bs)
  rw [map_inv₀, map_ofNat, ← norm_le_one_iff_mem', norm_inv] at h1
  have h2 : ‖(2 : Fv F v)‖ ≤ 1 := by
    rw [norm_le_one_iff_mem', show (2 : Fv F v) = 1 + 1 by norm_num]
    exact add_mem (one_mem _) (one_mem _)
  have h0 : (2 : Fv F v) ≠ 0 := by
    rw [← map_ofNat (algebraMap F (Fv F v)) 2]
    exact (map_ne_zero_iff _ (algebraMap F (Fv F v)).injective).mpr two_ne_zero
  have hpos : 0 < ‖(2 : Fv F v)‖ := norm_pos_iff.mpr h0
  have h3 := (inv_le_one₀ hpos).mp h1
  linarith

theorem unif_mem_Rv {σ : E →ₐ[F] E} {d : ℕ} {bs : Module.Basis (Fin d) F E} {v : HeightOneSpectrum (𝓞 F)}
    (hB : IntAt v (basisSet σ bs)) {ϖ : Fv F v} (hϖ : ϖ ∈ v.adicCompletionIntegers F) :
    algebraMap (Fv F v) (Fv F v ⊗[F] E) ϖ ∈ Rv bs v := by
  intro k
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
    Algebra.TensorProduct.basis_repr_tmul]
  simp only [Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul]
  exact mul_mem hϖ (hB _ (mem_basisSet_one σ bs k))

theorem locRingE_of (h1 : RvRing) (h2 : FixedK) (h3 : UnifEx) (h4 : QuadAt) (h6 : TraceDualAt) : LocRingE := by
  intro F E i1 i2 i3 i4 i5 σ hCM d bs v hB
  obtain ⟨S, σS, hS, hσS⟩ := h1 F E σ d bs v hB
  obtain ⟨ϖ, hϖ0, hϖ1, hϖd, hϖc⟩ := h3 F v
  obtain ⟨ε, hε⟩ : ∃ ε : ℤ, (ε : ℂ) = eSp E v := by
    unfold eSp
    split_ifs
    · exact ⟨-1, by simp⟩
    · exact ⟨1, by simp⟩
  have hϖS : algebraMap (Fv F v) (Fv F v ⊗[F] E) (ϖ : Fv F v) ∈ S := by
    have := unif_mem_Rv hB ϖ.2
    rw [← hS] at this
    exact this
  have htr := h6 F E σ hCM d bs v hB
  rw [← hS] at htr
  exact ⟨S, σS, ϖ, ε, hϖS, hε, hS, hσS, h2 F E σ hCM v, ϖ.2, hϖ0, hϖ1,
    h4 F E σ hCM d bs v hB S σS hS hσS ϖ hϖ0 hϖ1 hϖd hϖc hϖS ε hε, two_of hB, htr⟩

theorem almostGood_ofE (h1 : FinInt) (h2 : PsiBasic) (h3 : PsiCond) (h4 : LocRingE) (h5 : LocMat) : AlmostGood := by
  classical
  intro F E _ _ _ _ _ σ hσ M J hJ n T hT hdet d bs ψ hψ
  filter_upwards [h1 F (basisSet σ bs ∪ matSet bs J ∪ matSet bs T), h3 F ψ hψ] with v hv hc
  have hB : IntAt v (basisSet σ bs) := fun x hx => hv x (by simp [hx])
  have hMJ : IntAt v (matSet bs J) := fun x hx => hv x (by simp [hx])
  have hMT : IntAt v (matSet bs T) := fun x hx => hv x (by simp [hx])
  obtain ⟨S, σS, ϖ, ε, hϖ, hε, hcar, hsig, hfix, hϖO, hϖ0, hϖ1, hquad, htwo, htr⟩ := h4 F E σ hσ d bs v hB
  obtain ⟨hJi, hJu⟩ := h5 F E σ d bs v S σS hcar hsig M J hJ.1 hJ.2 hMJ
  obtain ⟨hTi, hTu⟩ := h5 F E σ d bs v S σS hcar hsig n T hT hdet hMT
  obtain ⟨pa, p0, pc⟩ := h2 F ψ hψ v
  exact ⟨S, σS, ϖ, ε, hε,
    { carrier := hcar, sig := hsig, fixed := hfix, unif_mem := hϖO, unif_ne := hϖ0, unif_lt := hϖ1, unif_S := hϖ,
      quad := hquad, two := htwo, trace_dual := htr, J_int := hJi, J_unimod := hJu, T_int := hTi, T_unimod := hTu,
      psi_add := pa, psi_zero := p0, psi_cont := pc, psi_cond := hc }⟩

end PositivityTheory.SiegelWeilFormula.Gunr

end
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.QuadAtOf
section
noncomputable section

namespace PositivityTheory.SiegelWeilFormula.Gunr

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory PositivityTheory.PfSWUS.Loc PositivityTheory.SiegelWeilFormula.Gen Filter
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def QuadHyp (σ : E →ₐ[F] E) {d : ℕ} (bs : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))
    (S : Subring (Fv F v ⊗[F] E)) (σS : S →+* S) (ϖ : v.adicCompletionIntegers F) : Prop :=
  IsCMExt F E σ ∧ IntAt v (basisSet σ bs) ∧ (S : Set (Fv F v ⊗[F] E)) = Rv bs v ∧
    (∀ x : S, ((σS x : S) : Fv F v ⊗[F] E) = sigR (Fv F v) σ x) ∧ (ϖ : Fv F v) ≠ 0 ∧ ‖(ϖ : Fv F v)‖ < 1 ∧
    (∀ x : v.adicCompletionIntegers F, ‖(x : Fv F v)‖ < 1 → ϖ ∣ x) ∧
    Nat.card (v.adicCompletionIntegers F ⧸ Ideal.span {ϖ}) = Ideal.absNorm v.asIdeal

def Q1 : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : ℕ)
    (bs : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (S : Subring (Fv F v ⊗[F] E)) (σS : S →+* S)
    (ϖ : v.adicCompletionIntegers F), QuadHyp σ bs v S σS ϖ →
  ∀ hϖ : algebraMap (Fv F v) (Fv F v ⊗[F] E) ϖ ∈ S,
    (∀ a, σS (σS a) = a) ∧ σS ⟨_, hϖ⟩ = ⟨_, hϖ⟩ ∧ IsSMulRegular S (⟨_, hϖ⟩ : S) ∧ ¬ IsUnit (⟨_, hϖ⟩ : S) ∧
    1 < Ideal.absNorm v.asIdeal

def Q2 : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : ℕ)
    (bs : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (S : Subring (Fv F v ⊗[F] E)) (σS : S →+* S)
    (ϖ : v.adicCompletionIntegers F), QuadHyp σ bs v S σS ϖ →
  ∀ hϖ : algebraMap (Fv F v) (Fv F v ⊗[F] E) ϖ ∈ S,
    (∀ a : S, (∀ k, a ∈ lev (⟨_, hϖ⟩ : S) k) → a = 0) ∧
    ∀ f : ℕ → S, (∀ k, f (k + 1) - f k ∈ lev (⟨_, hϖ⟩ : S) k) → ∃ a, ∀ k, a - f k ∈ lev (⟨_, hϖ⟩ : S) k

def Q3 : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : ℕ)
    (bs : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (S : Subring (Fv F v ⊗[F] E)) (σS : S →+* S)
    (ϖ : v.adicCompletionIntegers F), QuadHyp σ bs v S σS ϖ →
  ∀ hϖ : algebraMap (Fv F v) (Fv F v ⊗[F] E) ϖ ∈ S,
    Nat.card (S ⧸ lev (⟨_, hϖ⟩ : S) 1) = Ideal.absNorm v.asIdeal ^ 2

def Q4 : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : ℕ)
    (bs : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (S : Subring (Fv F v ⊗[F] E)) (σS : S →+* S)
    (ϖ : v.adicCompletionIntegers F), QuadHyp σ bs v S σS ϖ →
  ∀ hϖ : algebraMap (Fv F v) (Fv F v ⊗[F] E) ϖ ∈ S,
    (∀ a : S, σS a = a → a ∉ lev (⟨_, hϖ⟩ : S) 1 → IsUnit a) ∧
    ∃ u : S, IsUnit (u - σS u) ∧ ∀ a, ∃ x y, σS x = x ∧ σS y = y ∧ a = x + y * u

def Q5 : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : ℕ)
    (bs : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (S : Subring (Fv F v ⊗[F] E)) (σS : S →+* S)
    (ϖ : v.adicCompletionIntegers F), QuadHyp σ bs v S σS ϖ →
  ∀ hϖ : algebraMap (Fv F v) (Fv F v ⊗[F] E) ϖ ∈ S,
    (IsField (Fv F v ⊗[F] E) ↔ IsField (S ⧸ lev (⟨_, hϖ⟩ : S) 1))

theorem quadAt_of (h1 : Q1) (h2 : Q2) (h3 : Q3) (h4 : Q4) (h5 : Q5) : QuadAt := by
  intro F E _ _ _ _ _ σ hσ d bs v hB S σS hcar hsig ϖ hϖ0 hϖ1 hϖd hϖc hϖ ε hε
  have hH : QuadHyp σ bs v S σS ϖ := ⟨hσ, hB, hcar, hsig, hϖ0, hϖ1, hϖd, hϖc⟩
  obtain ⟨a1, a2, a3, a4, a5⟩ := h1 F E σ d bs v S σS ϖ hH hϖ
  obtain ⟨b1, b2⟩ := h2 F E σ d bs v S σS ϖ hH hϖ
  obtain ⟨c1, c2⟩ := h4 F E σ d bs v S σS ϖ hH hϖ
  have e5 := h5 F E σ d bs v S σS ϖ hH hϖ
  refine ⟨a1, a2, a3, a4, b1, b2, c1, c2, a5, h3 F E σ d bs v S σS ϖ hH hϖ, ?_⟩
  by_cases hf : IsField (Fv F v ⊗[F] E)
  · left
    refine ⟨?_, e5.1 hf⟩
    have : (ε : ℂ) = -1 := by rw [hε, eSp, if_pos hf]
    exact_mod_cast this
  · right
    refine ⟨?_, fun h => hf (e5.2 h)⟩
    have : (ε : ℂ) = 1 := by rw [hε, eSp, if_neg hf]
    exact_mod_cast this

end PositivityTheory.SiegelWeilFormula.Gunr

end
end

