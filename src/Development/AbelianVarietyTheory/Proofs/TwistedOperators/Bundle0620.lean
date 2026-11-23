module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0593
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0003
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0607
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1256
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0792
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0877
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0118
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0252
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0609

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealPointActsOnVacuumByAlgebraicScalar
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section

namespace GlobalTheory.RealScalarAlg

open Matrix
open scoped Kronecker ComplexOrder

open GlobalTheory.Grid (neg sgn ofSgn)

variable {D : D7}

def EIn {m n : Type} (M : Matrix m n ℂ) : Prop := ∀ i j, M i j ∈ algebraicClosure ℚ ℂ

section Entries

variable {ι κ ι' κ' : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem EIn.add {M N : Matrix ι κ ℂ} (hM : EIn M) (hN : EIn N) : EIn (M + N) := fun i j => add_mem (hM i j) (hN i j)

theorem EIn.sub {M N : Matrix ι κ ℂ} (hM : EIn M) (hN : EIn N) : EIn (M - N) := fun i j => sub_mem (hM i j) (hN i j)

theorem EIn.neg {M : Matrix ι κ ℂ} (hM : EIn M) : EIn (-M) := fun i j => neg_mem (hM i j)

theorem EIn.smul {c : ℂ} (hc : c ∈ algebraicClosure ℚ ℂ) {M : Matrix ι κ ℂ} (hM : EIn M) : EIn (c • M) :=
  fun i j => mul_mem hc (hM i j)

theorem EIn.one : EIn (1 : Matrix ι ι ℂ) := fun i j => by
  rw [Matrix.one_apply]; split_ifs
  · exact one_mem _
  · exact zero_mem _

theorem EIn.mul {M : Matrix ι κ ℂ} {N : Matrix κ ι' ℂ} (hM : EIn M) (hN : EIn N) : EIn (M * N) := fun i j => by
  rw [Matrix.mul_apply]; exact sum_mem fun k _ => mul_mem (hM i k) (hN k j)

theorem EIn.transpose {M : Matrix ι κ ℂ} (hM : EIn M) : EIn Mᵀ := fun i j => hM j i

theorem EIn.kron {M : Matrix ι κ ℂ} {N : Matrix ι' κ' ℂ} (hM : EIn M) (hN : EIn N) :
    EIn (Matrix.kroneckerMap (· * ·) M N) := fun i j => by
  rw [Matrix.kroneckerMap_apply]; exact mul_mem (hM _ _) (hN _ _)

theorem EIn.det {M : Matrix ι ι ℂ} (hM : EIn M) : M.det ∈ algebraicClosure ℚ ℂ := by
  let M' : Matrix ι ι (algebraicClosure ℚ ℂ) := fun i j => ⟨M i j, hM i j⟩
  have e : M = (algebraicClosure ℚ ℂ).val.toRingHom.mapMatrix M' := by ext i j; rfl
  rw [e, ← RingHom.map_det]
  exact (M'.det).2

end Entries

theorem half_mem : (1 / 2 : ℂ) ∈ algebraicClosure ℚ ℂ := div_mem (one_mem _) (ofNat_mem _ 2)

theorem detPlus_mem {m n : ℕ} {sS : Matrix (Fin n) (Fin n) ℂ} {sT : Matrix (Fin m) (Fin m) ℂ}
    {a' : Matrix (Fin n) (Fin n) ℂ} {b : Matrix (Fin m) (Fin m) ℂ} (hS : EIn sS) (hT : EIn sT) (ha : EIn a') (hb : EIn b) :
    GlobalTheory.WeilParts.detPlus sS sT a' b ∈ algebraicClosure ℚ ℂ := by
  unfold GlobalTheory.WeilParts.detPlus
  have k1 : EIn (sT ⊗ₖ sSᵀ) := hT.kron hS.transpose
  have k2 : EIn (b ⊗ₖ a'ᵀ) := hb.kron ha.transpose
  have k3 : EIn ((1 + sT ⊗ₖ sSᵀ) * (b ⊗ₖ a'ᵀ)) := (EIn.one.add k1).mul k2
  have k4 : EIn ((1 / 2 : ℂ) • ((1 + sT ⊗ₖ sSᵀ) * (b ⊗ₖ a'ᵀ))) := k3.smul half_mem
  have k5 : EIn ((1 / 2 : ℂ) • (1 - sT ⊗ₖ sSᵀ)) := (EIn.one.sub k1).smul half_mem
  exact (k4.add k5).det

theorem compAt_mt_mul (θ : InfFam D) (τ : D.what₂.Tau) (V : HSp D) (g h : GA D V) :
    compAt θ τ (Formalism.L2.Theta.mt V (g * h)) = compAt θ τ (Formalism.L2.Theta.mt V g) * compAt θ τ (Formalism.L2.Theta.mt V h) := by
  have e : Formalism.L2.Theta.mt V (g * h) = Formalism.L2.Theta.mt V g * Formalism.L2.Theta.mt V h := by
    unfold Formalism.L2.Theta.mt; rw [map_mul, Units.val_mul]
  rw [e]
  exact Matrix.map_mul (f := (θ τ).comp (infPart D))

theorem compAt_mt_fin (θ : InfFam D) (τ : D.what₂.Tau) (V : HSp D) (g : GA D V) (hg : g ∈ GfC V) :
    compAt θ τ (Formalism.L2.Theta.mt V g) = 1 := by
  have h1 : infHom V g = 1 := hg
  have e : compAt θ τ (Formalism.L2.Theta.mt V g) = (Units.val (infHom V g)).map (θ τ) := rfl
  rw [e, h1, Units.val_one]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem eIn_rat {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) (V : HSp D) (γ : GA D V) (hγ : γ ∈ GQ V) :
    EIn (compAt θ τ (Formalism.L2.Theta.mt V γ)) := by
  obtain ⟨x, -, e⟩ := hγ
  have hm : Formalism.L2.Theta.mt V γ = (x : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (incA D) := by
    exact (congrArg Units.val e).symm
  intro i j
  rw [hm]
  show θ τ (infPart D (incA D (x i j))) ∈ _
  have e2 : infPart D (incA D (x i j)) = (1 : Ainf D.host.F) ⊗ₜ[D.host.F] (x i j : D.host.E) := by
    simp [infPart, incA, inclR, Algebra.TensorProduct.map_tmul]
  rw [e2, (hθ τ).1, mem_algebraicClosure_iff]
  exact ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) (x i j : D.host.E))).algHom (tauE D τ).toRatAlgHom

theorem eIn_real {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) (V : HSp D) (γ : GA D V) (hγ : γ ∈ GQ V) (a : GA D V)
    (h : γ * a ∈ GfC V) : EIn (compAt θ τ (Formalism.L2.Theta.mt V a)) ∧ EIn (compAt θ τ (Formalism.L2.Theta.mt V a⁻¹)) := by
  constructor
  · have e : a = γ⁻¹ * (γ * a) := by group
    rw [e, compAt_mt_mul, compAt_mt_fin θ τ V _ h, Matrix.mul_one]
    exact eIn_rat hθ τ V _ (inv_mem hγ)
  · have e : a⁻¹ = (γ * a)⁻¹ * γ := by group
    rw [e, compAt_mt_mul, compAt_mt_fin θ τ V _ (inv_mem h), Matrix.one_mul]
    exact eIn_rat hθ τ V _ hγ

theorem exists_root_alg {θ : InfFam D} (hθ : IsInfFam θ) (V : HSp D) (hV : ∀ τ, (gramAt D V τ).det ≠ 0)
    (g : GA D V) (hg : g ∈ GinfC V) (hA : ∀ τ, (compAt θ τ (Formalism.L2.Theta.mt V g)).det ∈ algebraicClosure ℚ ℂ) :
    ∃ x, IsDetRoot V g x ∧ ∀ ν : (AE D)ˣ →* Circle, (∀ τ, ∃ a, HasInfExp D ν τ a) →
      ((ν x : Circle) : ℂ) ∈ algebraicClosure ℚ ℂ := by
  classical
  have hu : ∀ τ, ‖(compAt θ τ (Formalism.L2.Theta.mt V g)).det‖ = 1 := fun τ => by
    have h : (compAt θ τ (Formalism.L2.Theta.mt V g))ᴴ * gramAt D V τ * compAt θ τ (Formalism.L2.Theta.mt V g) = gramAt D V τ :=
      GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V g τ
    have h2 := congrArg (fun M => ‖Matrix.det M‖) h
    simp only [Matrix.det_mul, Matrix.det_conjTranspose, norm_mul, norm_star] at h2
    have h3 : ‖(gramAt D V τ).det‖ ≠ 0 := norm_ne_zero_iff.2 (hV τ)
    have h4 : ‖(compAt θ τ (Formalism.L2.Theta.mt V g)).det‖ ^ 2 = 1 := by
      apply mul_left_cancel₀ h3; linear_combination h2
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h4
  have hw : ∀ τ, ∃ w : ℂ, w ^ 2 = (compAt θ τ (Formalism.L2.Theta.mt V g)).det ∧ ‖w‖ = 1 := fun τ => by
    obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq (compAt θ τ (Formalism.L2.Theta.mt V g)).det two_pos
    refine ⟨w, hw, (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 ?_⟩
    rw [← norm_pow, hw, hu]
  choose w hw1 hw2 using hw
  have hw0 : ∀ τ, w τ ≠ 0 := fun τ h => by simpa [h] using hw2 τ
  have hwA : ∀ τ, w τ ∈ algebraicClosure ℚ ℂ := fun τ => by
    have := hA τ
    rw [← hw1, mem_algebraicClosure_iff] at this
    exact mem_algebraicClosure_iff.2 (IsAlgebraic.of_pow two_pos this)
  choose x hx1 hx2 using fun τ => GlobalTheory.VacuumCharacter.exists_idele_at hθ τ (w τ) (hw0 τ)
  have hf : finPart D ((∏ τ, x τ : (AE D)ˣ) : AE D) = 1 := by
    rw [Units.coe_prod, map_prod]; exact Finset.prod_eq_one fun τ _ => hx1 τ
  have hi : ∀ τ, θ τ (infPart D ((∏ τ, x τ : (AE D)ˣ) : AE D)) = w τ := fun τ => by
    rw [Units.coe_prod, map_prod, map_prod]
    simp [hx2]
  refine ⟨∏ τ, x τ, ?_, fun ν hc => ?_⟩
  · refine GlobalTheory.VacuumCharacter.adele_ext hθ ?_ fun τ => ?_
    · have hd : finPart D (Formalism.L2.Theta.mt V g).det = 1 := by
        have hg' : finHom V g = 1 := hg
        have : (Formalism.L2.Theta.mt V g).map (finPart D) = 1 := congrArg Units.val hg'
        rw [RingHom.map_det]
        exact (congrArg Matrix.det this).trans Matrix.det_one
      rw [map_mul, hf]
      exact ((congrArg₂ (· * ·) hd (GlobalTheory.VacuumCharacter.finPart_cA _ hf)).trans (one_mul 1)).symm
    · rw [map_mul, map_mul, hi]
      have e1 := GlobalTheory.FockCompare.comp_cA hθ τ ((∏ τ, x τ : (AE D)ˣ) : AE D)
      have e2 := GlobalTheory.VacuumCharacter.det_compAt θ τ (Formalism.L2.Theta.mt V g)
      rw [hi] at e1
      refine Eq.trans ?_ (congrArg₂ (· * ·) e2 e1.symm)
      have : w τ * starRingEnd ℂ (w τ) = 1 := by rw [Complex.mul_conj', hw2]; simp
      rw [← hw1]; linear_combination (-w τ) * this
  · rw [map_prod]
    rw [show ((∏ τ, ν (x τ) : Circle) : ℂ) = ∏ τ, (ν (x τ) : ℂ) from map_prod Circle.coeHom _ _]
    refine prod_mem fun τ _ => ?_
    obtain ⟨a, n, -, -, h⟩ := hc τ
    rw [h θ hθ (x τ) (hx1 τ) (fun τ' h' => by rw [hx2, if_neg h']), hx2, if_pos rfl, hw2]
    simp only [Complex.ofReal_one, div_one]
    exact zpow_mem (hwA τ) n

theorem realScalar : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW},
    IsBottomTri W i j X → ∀ (t : T), ∀ γ ∈ Formalism.L2.Theta.GQ A, ∀ a ∈ GinfC A, ∀ γ' ∈ Formalism.L2.Theta.GQ WW, ∀ a' ∈ GinfC WW,
      γ * a ∈ GfC A → γ' * a' ∈ GfC WW →
      ∃ C : ℂ, IsAlgebraic ℚ C ∧ X.ω t (a, a') X.vac = C • X.vac := by
  intro D T L sc G W i j A A' WW X hX t γ hγ a ha γ' hγ' a' ha' hγa hγa'
  classical
  have hI := hX.is
  have hθ : IsInfFam W.θ := hI.isVac.2.inf
  have hψ : IsStdChar D W.ψ (-1) := hI.isVac.1
  set om' := (X.ω t).toSgn true with hom'
  have hom := hI.weil t
  have hsA : ∀ τ, X.rA.s τ = 1 := fun τ => (hX.std.2.2 τ).1
  have hsW : ∀ τ, X.rW.s τ = 1 := fun τ => (hX.stdW.2.2 τ).1
  set g : GA D (neg A) := (ofSgn true A).symm a with hgdef
  have hga : ofSgn true A g = a := MulEquiv.apply_symm_apply _ _
  have hg : g ∈ GinfC (neg A) := (GlobalTheory.SgnIdent.mem_GinfC_sgn true A g).2 (by rw [hga]; exact ha)
  have cS : ∀ τ, IsCartanInv (gramAt D (neg A) τ) (-X.rA.s τ) := fun τ => GlobalTheory.Grid.isCartanInv_sgn true A τ (hI.rigA.2.2 τ).1
  have cT : ∀ τ, IsCartanInv (gramAt D WW τ) (X.rW.s τ) := fun τ => (hI.rigW.2.2 τ).1
  have hdet : ∀ τ, (gramAt D (neg A) τ).det ≠ 0 := fun τ h0 => by
    have := (cS τ).2.2.det_pos.ne'
    rw [Matrix.det_mul, h0, zero_mul] at this
    exact this rfl
  have hdetW : ∀ τ, (gramAt D WW τ).det ≠ 0 := fun τ h0 => by
    have := (cT τ).2.2.det_pos.ne'
    rw [Matrix.det_mul, h0, zero_mul] at this
    exact this rfl
  have mg : ∀ τ, compAt W.θ τ (Formalism.L2.Theta.mt (neg A) g) = compAt W.θ τ (Formalism.L2.Theta.mt A a) := fun τ => by
    have e := GlobalTheory.Grid.mt_ofSgn true A g
    rw [hga] at e
    rw [e]
  have mgi : ∀ τ, compAt W.θ τ (Formalism.L2.Theta.mt (neg A) g⁻¹) = compAt W.θ τ (Formalism.L2.Theta.mt A a⁻¹) := fun τ => by
    have e := GlobalTheory.Grid.mt_ofSgn true A g⁻¹
    rw [map_inv, hga] at e
    rw [e]
  have eA := fun τ => eIn_real hθ τ A γ hγ a hγa
  have eW := fun τ => eIn_real hθ τ WW γ' hγ' a' hγa'
  obtain ⟨x, hx, hxν⟩ := exists_root_alg hθ (neg A) hdet g hg fun τ => by rw [mg]; exact (eA τ).1.det
  obtain ⟨y, hy, hyν⟩ := exists_root_alg hθ WW hdetW a' ha' fun τ => (eW τ).1.det
  obtain ⟨η, hη⟩ := GlobalTheory.WeilParts.exists_isEtaTilde_unramified D
  have hC := GlobalTheory.WeilVacChar.vacuum_character D W.ψ hψ (neg A) WW W.θ hθ _ _ om' η hη hom (fun τ => -X.rA.s τ) X.rW.s cS cT
    g hg a' ha' (fun τ => by rw [hsA]; simp) (fun τ => by rw [hsW]; simp) x y hx hy X.vac hI.isVac.2.theta hI.isVac.2.fock
  have hexp : ∀ (χ : (AE D)ˣ →* Circle) (n : ℕ), IsHeckeChar D χ → ResEta D χ n → ∀ k : ℕ,
      ∀ τ, ∃ b, HasInfExp D (χ * (η ^ k)⁻¹) τ b := fun χ n h1 h2 k τ => by
    obtain ⟨b, hb⟩ := GlobalTheory.SplitCharExp.exists_hasInfExp D W.θ χ n τ hθ h1 h2
    exact ⟨_, GlobalTheory.VacuumCharacter.hasInfExp_twist hb (hη.2.2.2 τ) k⟩
  have key : X.ω t (a, a') X.vac = om' (g, a') X.vac := by
    show _ = X.ω t (ofSgn true A g, a') X.vac
    rw [hga]
  rw [key, hC]
  refine ⟨_, ?_, rfl⟩
  · rw [← mem_algebraicClosure_iff, Circle.coe_mul, Circle.coe_inv]
    refine mul_mem (mul_mem (inv_mem (hxν _ (hexp _ _ hom.hecT hom.resT _))) (hyν _ (hexp _ _ hom.hecS hom.resS _)))
      (prod_mem fun τ _ => ?_)
    rw [mgi]
    have hs1 : EIn (-X.rA.s τ) := by rw [hsA]; exact EIn.one.neg
    have hs2 : EIn (X.rW.s τ) := by rw [hsW]; exact EIn.one
    exact detPlus_mem hs1 hs2 (eA τ).2 (eW τ).1

end GlobalTheory.RealScalarAlg

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SumQuotientIntegerMatricesInvariantIntegralGLMul
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv

namespace GlobalTheory.ResSumInv

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mk_eq_iff {ϖ : kˣ} (hϖ : IsUnif ϖ) (e : ℕ) (a b : 𝒪[k]) :
    (Ideal.Quotient.mk (IsLocalRing.maximalIdeal 𝒪[k] ^ e) a = Ideal.Quotient.mk _ b) ↔
      (((ϖ ^ e)⁻¹ : kˣ) : k) * ((a : k) - b) ∈ 𝒪[k] := by
  rw [Ideal.Quotient.eq, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  have hne : ((ϖ : k)) ^ e ≠ 0 := pow_ne_zero _ ϖ.ne_zero
  constructor
  · rintro ⟨c, hc⟩
    have hc' : ((a : k) - b) = (ϖ : k) ^ e * c := by
      have := congrArg (fun x : 𝒪[k] => (x : k)) hc
      simpa using this
    rw [hc']
    have : (((ϖ ^ e)⁻¹ : kˣ) : k) * ((ϖ : k) ^ e * c) = c := by
      rw [Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]
    rw [this]; exact c.2
  · intro h
    refine ⟨⟨_, h⟩, Subtype.ext ?_⟩
    push_cast
    rw [← mul_assoc, mul_inv_cancel₀ hne, one_mul]

theorem mul_mem_int {A C B : Type} [Fintype C] {X : Matrix A C k} {Y : Matrix C B k}
    (hX : ∀ i j, X i j ∈ 𝒪[k]) (hY : ∀ i j, Y i j ∈ 𝒪[k]) (i : A) (j : B) : (X * Y) i j ∈ 𝒪[k] := by
  rw [Matrix.mul_apply]
  exact Subring.sum_mem _ fun l _ => Subring.mul_mem _ (hX i l) (hY l j)

theorem sum_res_mul_left {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (ϖ : kˣ) (e : ℕ) (hϖ : IsUnif ϖ) (f : Matrix A B k → ℂ)
    (hf : ∀ Z Z' : Matrix A B k, (∀ i j, Z' i j ∈ 𝒪[k]) → f (Z + Z') = f Z)
    (M : GL A k) (hM : M ∈ KO k A) :
    ∑ S : A → B → Res k e, f (M.val * ((ϖ ^ e)⁻¹ • liftRes S)) =
      ∑ S : A → B → Res k e, f ((ϖ ^ e)⁻¹ • liftRes S) := by
  obtain ⟨hM1, hM2⟩ := (mem_KO_iff M).1 hM
  set c : k := (((ϖ ^ e)⁻¹ : kˣ) : k) with hc
  have hint : ∀ (S : A → B → Res k e) i j, (M.val * liftRes S) i j ∈ 𝒪[k] :=
    fun S => mul_mem_int hM1 (liftRes_mem S)
  let φ : (A → B → Res k e) → (A → B → Res k e) := fun S i j =>
    Ideal.Quotient.mk _ (⟨(M.val * liftRes S) i j, hint S i j⟩ : 𝒪[k])
  have h1 : ∀ S i j, c * (liftRes (φ S) i j - (M.val * liftRes S) i j) ∈ 𝒪[k] := by
    intro S i j
    have := (mk_eq_iff hϖ e (Quotient.out (φ S i j)) ⟨(M.val * liftRes S) i j, hint S i j⟩).1
      (Ideal.Quotient.mk_out _)
    exact this
  have hinj : Function.Injective φ := by
    intro S S' h
    have hd : ∀ i j, c * ((M.val * liftRes S) i j - (M.val * liftRes S') i j) ∈ 𝒪[k] := fun i j =>
      (mk_eq_iff hϖ e ⟨_, hint S i j⟩ ⟨_, hint S' i j⟩).1 (congrFun (congrFun h i) j)
    have hD : ∀ i j, (c • (M.val * liftRes S - M.val * liftRes S')) i j ∈ 𝒪[k] := fun i j => by
      simpa [mul_sub] using hd i j
    have hL : c • (liftRes S - liftRes S') = (M⁻¹).val * (c • (M.val * liftRes S - M.val * liftRes S')) := by
      rw [Matrix.mul_smul, ← Matrix.mul_sub, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel,
        Units.val_one, Matrix.one_mul]
    funext i j
    have hij : c * (((Quotient.out (S i j) : 𝒪[k]) : k) - ((Quotient.out (S' i j) : 𝒪[k]) : k)) ∈ 𝒪[k] := by
      have := mul_mem_int hM2 hD i j
      rw [← hL] at this
      simpa [liftRes, mul_sub] using this
    have := (mk_eq_iff hϖ e (Quotient.out (S i j)) (Quotient.out (S' i j))).2 hij
    rwa [Ideal.Quotient.mk_out, Ideal.Quotient.mk_out] at this
  have hbij : Function.Bijective φ := Finite.injective_iff_bijective.1 hinj
  rw [← Fintype.sum_bijective φ hbij (fun S => f ((ϖ ^ e)⁻¹ • liftRes (φ S))) (fun S => f ((ϖ ^ e)⁻¹ • liftRes S)) (fun _ => rfl)]
  refine Finset.sum_congr rfl fun S _ => ?_
  have hsm : ∀ N : Matrix A B k, (ϖ ^ e)⁻¹ • N = c • N := fun N => rfl
  rw [hsm, hsm, Matrix.mul_smul]
  have : c • liftRes (φ S) = c • (M.val * liftRes S) + c • (liftRes (φ S) - M.val * liftRes S) := by
    rw [← smul_add, add_sub_cancel]
  rw [this, hf]
  intro i j
  simpa [mul_sub] using h1 S i j

end GlobalTheory.ResSumInv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldingColumnArgsMovedPointConjAtPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv
open GlobalTheory.StdFrames

namespace GlobalTheory.TopLevelInv

section ColCoord

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

variable {D : D7}

theorem map_mt_cpt_colCoord (w : Pl D.host.E) (V : HSp D) (g : GA D V) :
    Matrix.map (Formalism.L2.Theta.mt V g) ((cpt w).comp (toEAf D)) = (loc w (Lev.finE V g)).val := rfl

theorem frAt_actO_colCoord (w : Pl D.host.E) {S T : HSp D} (β' : GL (Fin T.rank) (Lev.EAf D))
    (β : GL (Fin S.rank) (Lev.EAf D)) (g : GA D S) (h : GA D T) (x : WO S T) :
    GlobalTheory.FunObj.frAt w β' β (actO S T g h x) =
      (loc w (β'⁻¹ * Lev.finE T h * β')).val * GlobalTheory.FunObj.frAt w β' β x *
        (loc w (β⁻¹ * Lev.finE S g * β))⁻¹.val := by
  have e0 : ∀ y : WO S T, GlobalTheory.FunObj.frAt w β' β y =
      (loc w β'⁻¹).val * Matrix.map y ((cpt w).comp (toEAf D)) * (loc w β).val := by
    intro y
    rw [GlobalTheory.FunObj.frAt, GlobalTheory.FunObj.Comparison₂.fr, Matrix.map_mul, Matrix.map_mul]
    rfl
  have e1 : Matrix.map (actO S T g h x) ((cpt w).comp (toEAf D)) =
      (loc w (Lev.finE T h)).val * Matrix.map x ((cpt w).comp (toEAf D)) * (loc w (Lev.finE S g))⁻¹.val := by
    rw [actO, Matrix.map_mul, Matrix.map_mul, map_mt_cpt_colCoord, map_mt_cpt_colCoord, map_inv, map_inv]
  rw [e0, e0, e1]
  simp only [map_mul, map_inv, _root_.mul_inv_rev, inv_inv, Units.val_mul, Matrix.mul_assoc]
  have hA : ∀ {c : Type} [Fintype c] (Y : Matrix (Fin T.rank) c (Kw w)), (loc w β').val * ((loc w β')⁻¹.val * Y) = Y := by
    intro c _ Y; rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
  have hB : (loc w β).val * ((loc w β)⁻¹.val * ((loc w (Lev.finE S g))⁻¹.val * (loc w β).val)) =
      (loc w (Lev.finE S g))⁻¹.val * (loc w β).val := by
    rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
  rw [hA, hB]

theorem loc_finE_u_colCoord {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
    (S : GridChoice W U) {t : T} (ht : t ∈ U) {X : Node} (hX : DefNode D.R.m X) {w : Pl D.host.E}
    (hw : w ∈ locPl G t) : loc w (Lev.finE (G.V X) (S.N.u X).1) = 1 := by
  classical
  obtain ⟨P', a, ⟨⟨es, hes, rfl⟩, -⟩, hsupp, hoff⟩ := S.N.u_supp X hX
  have hnot : ¬ Off S.N.S w := by
    intro h0
    have h3 := S.N.off w h0
    rcases Finset.mem_union.1 hw with h | h
    · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 h
      exact h3.1 ((G.pl.under_w hv).symm ▸ hv)
    · exact h3.2.1 t ht w h rfl
  obtain ⟨q, hq, hqw⟩ : ∃ q ∈ S.N.S, ((q : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal := by
    unfold Off at hnot; push_neg at hnot; exact hnot
  have hz : cpt w (toEAf D ((∑ PP ∈ P', es PP) + cA D (∑ PP ∈ P', es PP))) = 0 := by
    have hA : ∀ PP ∈ P', cpt w (toEAf D (es PP)) = 0 := fun PP hPP =>
      (cpt_of_isIdemAt (hes PP hPP)).2 _ fun e => hoff PP hPP q hq (e ▸ hqw)
    have hB : ∀ PP ∈ P', cpt w (sg D (toEAf D (es PP))) = 0 := by
      intro PP hPP
      refine cpt_sg_eq_zero ((cpt_of_isIdemAt (hes PP hPP)).2 _ fun e => hoff PP hPP q hq ?_)
      rw [← e]; exact (natCast_mem_cP w q).2 hqw
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_add (f := _), toEAf_cA, map_sum]
    rw [Finset.sum_eq_zero hA, Finset.sum_eq_zero hB, add_zero]
  apply Units.ext
  refine Matrix.ext fun i j => ?_
  have h1 := congrArg (fun z => cpt w (toEAf D z)) (hsupp i j)
  simp only [map_mul, hz, zero_mul] at h1
  have h2 : cpt w (toEAf D (Formalism.L2.Theta.mt (G.V X) (S.N.u X).1 i j)) = cpt w (toEAf D ((1 : Matrix (Fin (G.V X).rank) (Fin (G.V X).rank) (AE D)) i j)) := by
    have := h1.symm
    rw [Matrix.sub_apply, map_sub, map_sub, sub_eq_zero] at this
    exact this
  change cpt w (toEAf D (Formalism.L2.Theta.mt (G.V X) (S.N.u X).1 i j)) = (1 : Matrix (Fin (G.V X).rank) (Fin (G.V X).rank) (Kw w)) i j
  rw [h2, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem submatrix_cast_mul_colCoord {K : Type} [CommRing K] {r n n' p r' p' : ℕ} (M : Matrix (Fin r) (Fin n) K)
    (N : Matrix (Fin n) (Fin p) K) (f : Fin r' → Fin r) (h : n' = n) (g : Fin p' → Fin p) :
    M.submatrix f (Fin.cast h) * N.submatrix (Fin.cast h) g = (M * N).submatrix f g :=
  Matrix.submatrix_mul_equiv M N f (finCongr h) g

end ColCoord

end GlobalTheory.TopLevelInv

namespace GlobalTheory.TopLevelInv

theorem conj_inv_inv_colCoord {Γ : Type} [Group Γ] (b f : Γ) : (b⁻¹ * f⁻¹ * b)⁻¹ = b⁻¹ * f * b := by group

theorem conj_inv_colCoord {Γ : Type} [Group Γ] (b f : Γ) : b⁻¹ * f⁻¹ * b = (b⁻¹ * f * b)⁻¹ := by group


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in
theorem colAt_movedPt_conj : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T}, t ∈ U → ∀ (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.top (j + 1))), ∀ w ∈ locPl G t,
    ∀ x : ∀ j' : Fin D.R.m, WO (G.pS (.top t j' : Pair T)) (G.pT (.top t j' : Pair T)),
      S.colAt t w (movedPt t j hj ((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1))) x) = colMove j (kapAt S t j hj k w) (S.colAt t w x) := by
  intro D T L sc G W U S t ht j hj k w hw x
  have hu := loc_finE_u_colCoord S ht (X := .top (j + 1)) (show j + 1 ≤ D.R.m by omega) hw
  set k' : FinPt G (.top (j + 1)) := (S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) with hk'def
  have hk : ∀ β : GL (Fin (G.V (.top (j + 1))).rank) (Lev.EAf D),
      loc w (β⁻¹ * Lev.finE (G.V (.top (j + 1))) (k' : GA D (G.V (.top (j + 1)))) * β) =
      loc w (β⁻¹ * Lev.finE (G.V (.top (j + 1))) (k : GA D (G.V (.top (j + 1)))) * β) := by
    intro β
    simp only [hk'def, Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, hu, inv_one, one_mul, mul_one]
  have hκ : (kapAt S t j hj k w).val =
      (loc w ((S.βp (j + 1))⁻¹ * Lev.finE (G.V (.top (j + 1))) (k : GA D (G.V (.top (j + 1)))) * S.βp (j + 1))).val.submatrix
        (Fin.cast (topRank_eq G t w hj.le)) (Fin.cast (topRank_eq G t w hj.le)) := rfl
  have hκi : (kapAt S t j hj k w)⁻¹.val =
      (loc w ((S.βp (j + 1))⁻¹ * Lev.finE (G.V (.top (j + 1))) (k : GA D (G.V (.top (j + 1)))) * S.βp (j + 1)))⁻¹.val.submatrix
        (Fin.cast (topRank_eq G t w hj.le)) (Fin.cast (topRank_eq G t w hj.le)) := by
    have h0 : (kapAt S t j hj k w)⁻¹.val =
        (loc w ((S.βp (j + 1))⁻¹ * (Lev.finE (G.V (.top (j + 1))) (k : GA D (G.V (.top (j + 1)))))⁻¹ *
          S.βp (j + 1))).val.submatrix (Fin.cast (topRank_eq G t w hj.le)) (Fin.cast (topRank_eq G t w hj.le)) := by
      rw [kapAt, ← map_inv]; rfl
    rw [h0, conj_inv_colCoord, map_inv]
  funext i
  rcases eq_or_ne i (j + 1) with rfl | h1
  · rw [colAt_eq S t w _ hj]
    simp only [movedPt, Function.update_self]
    rw [frAt_actO_colCoord]
    simp only [colMove, Function.update_self]
    rw [colAt_eq S t w x hj, hκ, inv_one, map_one, mul_one, inv_mul_cancel, map_one, Units.val_one, Matrix.one_mul,
      map_inv (Lev.finE (G.V (.top (j + 1)))), ← map_inv (loc w), conj_inv_inv_colCoord, hk, submatrix_cast_mul_colCoord]
  rcases eq_or_ne i j with rfl | h2
  · rw [colAt_eq S t w _ (show i < D.R.m by omega)]
    rw [movedPt, Function.update_of_ne (show (⟨i, by omega⟩ : Fin D.R.m) ≠ ⟨i + 1, hj⟩ by simp [Fin.ext_iff]),
      Function.update_self]
    rw [frAt_actO_colCoord]
    simp only [colMove]
    rw [Function.update_of_ne h1, Function.update_self, colAt_eq S t w x (show i < D.R.m by omega), hκi, inv_one,
      map_one, mul_one, inv_mul_cancel, map_one, inv_one, Units.val_one, Matrix.mul_one,
      map_inv (Lev.finE (G.V (.top (i + 1)))), conj_inv_colCoord, map_inv (loc w), hk, submatrix_cast_mul_colCoord]
  by_cases hi : i < D.R.m
  · have hm : movedPt t j hj k' x ⟨i, hi⟩ = x ⟨i, hi⟩ := by
      rw [movedPt, Function.update_of_ne (show (⟨i, hi⟩ : Fin D.R.m) ≠ ⟨j + 1, hj⟩ by simp [Fin.ext_iff, h1]),
        Function.update_of_ne (show (⟨i, hi⟩ : Fin D.R.m) ≠ ⟨j, by omega⟩ by simp [Fin.ext_iff, h2])]
    simp only [colMove]
    rw [Function.update_of_ne h1, Function.update_of_ne h2, colAt_eq S t w _ hi, colAt_eq S t w x hi, hm]
  · simp only [colMove]
    rw [Function.update_of_ne h1, Function.update_of_ne h2]
    simp only [GridChoice.colAt, dif_neg hi]

end GlobalTheory.TopLevelInv
end

