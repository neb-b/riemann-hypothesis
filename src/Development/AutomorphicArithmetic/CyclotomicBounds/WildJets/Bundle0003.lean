module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ExistsSmallSpherical
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0329
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HighestWeightBelow
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1615
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0484
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0081
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0130
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0053
public import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.ThreeForms

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.ExpLoss
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem UpperTheory.WildA.expLoss :
    ∀ (D : D7) (S : Finset ℕ) (h : ℕ → ℝ) (B : ℝ), GlobalTheory.NormSum.Exponents S h B →
      Loss (fun w : PlL D => (vw w ((GlobalTheory.SumSize.TopInt.primeUnder w : ℕ) : D.what₂.LL) : ℝ) * h (GlobalTheory.SumSize.TopInt.primeUnder w)) B := by
  intro D S h B hE
  have e : (fun w : PlL D => (vw w ((GlobalTheory.SumSize.TopInt.primeUnder w : ℕ) : D.what₂.LL) : ℝ) *
      h (GlobalTheory.SumSize.TopInt.primeUnder w)) = Formalism.PairingDivisionLocalBalance.wt (K := D.what₂.LL) S h := by
    funext w
    rw [hE.wt_eq (TopInt.primeUnder_prime w) w (TopInt.primeUnder_mem w), mul_comm]
  rw [e]
  refine ⟨hE.wt_size.1, ?_, hE.wt_size.2⟩
  have hf : ∀ l : ℕ, {w : PlL D | vw w (l : D.what₂.LL) ≠ 0}.Finite := fun l => by
    have hf := FractionalIdeal.finite_factors (K := D.what₂.LL)
      (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.what₂.LL)) (l : D.what₂.LL))
    rw [Filter.eventually_cofinite] at hf
    exact hf
  refine (S.finite_toSet.biUnion fun l _ => hf l).subset fun w hw => ?_
  obtain ⟨l, hl, h0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hw
  refine Set.mem_biUnion (Finset.mem_coe.2 hl) fun h1 => h0 ?_
  rw [h1]; simp
end

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.HalfUnit
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem UpperTheory.WildA.halfUnit :
    ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GlobalTheory.ChiGrid.GridData L sc} (p : GlobalTheory.ChiGrid.Pair T) (P : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e P →
      ∀ c : ℕ, (∀ w ∈ P, ((c : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal) →
      ∀ u ∈ pairLat G p, IsHalf e u → ∃ u' ∈ pairLat G p, IsHalf e u' ∧ c • u' = u := by
  intro D T L sc G p P e he c hc u hu hhalf
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
  by_cases hc0 : c = 0
  · subst hc0
    have hS : ∑ PP ∈ P, es PP = 0 :=
      Finset.sum_eq_zero fun PP hPP => (hc PP hPP (by simp)).elim
    have hu0 : u = 0 := by
      ext i j
      have h := hhalf i j
      rw [hS, zero_mul] at h
      exact h.symm
    subst hu0
    exact ⟨0, (pairLat G p).zero_mem, fun i j => by simp, by simp⟩
  · have hx : ((c : 𝓞 D.host.E)) ≠ 0 := by exact_mod_cast hc0
    let w : AE D := (∑ PP ∈ P, es PP) * incA D (((c : 𝓞 D.host.E) : D.host.E))⁻¹
    have hw : finPart D w ∈ intAE D := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [w, Finset.sum_mul, map_sum]
      refine AddSubgroup.sum_mem _ ?_
      intro PP hPP
      by_contra hn
      exact hc PP hPP (((hes PP hPP).2 _ hx).mpr hn)
    have h1 : incA D (((c : 𝓞 D.host.E) : D.host.E))⁻¹ * (c : AE D) = 1 := by
      rw [← map_natCast (incA D) c, ← map_mul]
      have hce : (((c : 𝓞 D.host.E) : D.host.E)) = (c : D.host.E) := by simp
      rw [hce, inv_mul_cancel₀ (by exact_mod_cast hc0), map_one]
    have hcw : (c : AE D) * w = ∑ PP ∈ P, es PP := by
      calc (c : AE D) * w
          = (∑ PP ∈ P, es PP) * (incA D (((c : 𝓞 D.host.E) : D.host.E))⁻¹ * (c : AE D)) := by
            simp only [w]; ring
        _ = ∑ PP ∈ P, es PP := by rw [h1, mul_one]
    refine ⟨w • u, GlobalTheory.LatticeStable.smul_mem_latO _ _ _ _ _ _ w hw u hu, ?_, ?_⟩
    · intro i j
      simp only [Matrix.smul_apply, smul_eq_mul]
      rw [← mul_assoc, mul_comm _ w, mul_assoc, hhalf i j]
    · ext i j
      simp only [Matrix.smul_apply, smul_eq_mul, nsmul_eq_mul]
      rw [← mul_assoc, hcw, hhalf i j]
end

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.JetDeg
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

section SlopeTestRemainingChoices

open MvPolynomial Formalism.L2.Ker GlobalTheory.JetDeg

variable {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] {a b : ℕ}

private def frW (a b : ℕ) (τ : ι) : (ι × Fin b × Fin b) ⊕ DVar ι a b → ℕ :=
  Sum.elim (fun k => if k.1 = τ then 1 else 0) fun _ => 0

omit [Fintype ι] in
private theorem subD_hom_fr (τ : ι) {P : Pol K ι a} {d : ℕ} (hP : IsWeightedHomogeneous (posW a τ) P d) :
    IsWeightedHomogeneous (frW a b τ) (subD K ι a b P) d := by
  have key : ∀ v : ι × Fin a × Fin a,
      IsWeightedHomogeneous (frW a b τ) (subD K ι a b (X v)) (AddMonoidHom.id ℕ (posW a τ v)) := by
    intro v
    simp only [subD, MvPolynomial.aeval_X, AddMonoidHom.id_apply]
    split_ifs with h
    · apply IsWeightedHomogeneous.sum
      intro β _
      have hm := (isWeightedHomogeneous_X K (frW a b τ) (Sum.inl (v.1, β, ⟨v.2.2, h⟩))).mul
        (isWeightedHomogeneous_X K (frW a b τ) (Sum.inr (v.1, β, v.2.1)))
      convert hm using 1
      simp [frW, posW]
    · exact isWeightedHomogeneous_zero K _ _
  simpa using algHom_hom (posW a τ) (frW a b τ) (AddMonoidHom.id ℕ) (subD K ι a b) key hP

private theorem weight_fr (τ : ι) (μ : (ι × Fin b × Fin b) ⊕ DVar ι a b →₀ ℕ) :
    Finsupp.weight (posW b τ) (μ.comapDomain Sum.inl Sum.inl_injective.injOn) = Finsupp.weight (frW a b τ) μ := by
  rw [Finsupp.weight_apply, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finsupp.sum_fintype _ _ (by simp),
    Fintype.sum_sum_type]
  simp [frW, posW]

private theorem weight_der (τ : ι) (μ : (ι × Fin b × Fin b) ⊕ DVar ι a b →₀ ℕ) :
    ((μ.comapDomain Sum.inr Sum.inr_injective.injOn).sum fun v e => if v.1 = τ then e else 0) =
      Finsupp.weight (derW a b τ) μ := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finsupp.sum_fintype _ _ (by simp),
    Fintype.sum_sum_type]
  simp [derW]

omit [DecidableEq ι] in
private theorem jetLin_eq (J : (DVar ι a b →₀ ℕ) → K) (Q : MvPolynomial ((ι × Fin b × Fin b) ⊕ DVar ι a b) K) :
    jetLin J Q = ∑ μ ∈ Q.support, AddMonoidAlgebra.coeff Q μ • (monomial (μ.comapDomain Sum.inl Sum.inl_injective.injOn)
      (J (μ.comapDomain Sum.inr Sum.inr_injective.injOn)) : Pol K ι b) := by
  classical
  set_option synthInstance.maxHeartbeats 100000 in
    conv_lhs => rw [Q.as_sum, map_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  have e : (monomial μ (AddMonoidAlgebra.coeff Q μ) : MvPolynomial ((ι × Fin b × Fin b) ⊕ DVar ι a b) K) =
      AddMonoidAlgebra.coeff Q μ • (basisMonomials _ K) μ := by
    rw [MvPolynomial.coe_basisMonomials, smul_monomial, smul_eq_mul, mul_one]
  rw [e, map_smul]
  simp only [jetLin, Module.Basis.constr_basis]

private theorem jetMap_congr_deg (lam : ι → DomWeight a) (lam' : ι → DomWeight b) (n : ι → ℕ)
    (hV : JetInVV K lam lam' n) (J J' : (DVar ι a b →₀ ℕ) → K)
    (h : ∀ m : DVar ι a b →₀ ℕ, (∀ τ, (m.sum fun v e => if v.1 = τ then e else 0) = ∑ i, (lam' τ).natW i) → J m = J' m)
    (P : Pol K ι a) (hP : P ∈ Formalism.L2.DIV.VV K lam) : jetMap J n P = jetMap J' n P := by
  set Q := subD K ι a b (GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint.sharp n P) with hQ
  have hJ : ∀ J₀ : (DVar ι a b →₀ ℕ) → K, jetMap J₀ n P = jetLin J₀ Q := fun J₀ => rfl
  have hfr : ∀ τ, IsWeightedHomogeneous (frW a b τ) Q (∑ i, (lam τ).natW i + n τ * a) :=
    fun τ => subD_hom_fr τ (sharp_hom n τ (VV_hom lam τ hP))
  have hder : ∀ τ, IsWeightedHomogeneous (derW a b τ) Q (∑ i, (lam τ).natW i + n τ * a) :=
    fun τ => subD_hom τ (sharp_hom n τ (VV_hom lam τ hP))
  have hdeg : ∀ (J₀ : (DVar ι a b →₀ ℕ) → K) τ,
      IsWeightedHomogeneous (posW b τ) (jetLin J₀ Q) (∑ i, (lam τ).natW i + n τ * a) := by
    intro J₀ τ
    rw [jetLin_eq]
    apply IsWeightedHomogeneous.sum
    intro μ hμ
    rw [smul_monomial]
    apply isWeightedHomogeneous_monomial
    rw [weight_fr]
    exact hfr τ (mem_support_iff.mp hμ)
  by_cases hall : ∀ τ, ∑ i, (lam τ).natW i + n τ * a = ∑ i, (lam' τ).natW i
  · rw [hJ, hJ, jetLin_eq, jetLin_eq]
    refine Finset.sum_congr rfl fun μ hμ => ?_
    have hJJ : J (μ.comapDomain Sum.inr Sum.inr_injective.injOn) =
        J' (μ.comapDomain Sum.inr Sum.inr_injective.injOn) := by
      apply h
      intro τ
      rw [weight_der, ← hall τ]
      exact hder τ (mem_support_iff.mp hμ)
    rw [hJJ]
  · push_neg at hall
    obtain ⟨τ, hτ⟩ := hall
    have hz : ∀ J₀ : (DVar ι a b →₀ ℕ) → K, jetMap J₀ n P = 0 := by
      intro J₀
      by_contra hne
      have h1 := VV_hom lam' τ (hV J₀ P hP)
      have h2 := hdeg J₀ τ
      rw [← hJ] at h2
      exact hτ (IsWeightedHomogeneous.inj_right hne h2 h1)
    rw [hz J, hz J']

end SlopeTestRemainingChoices

theorem UpperTheory.WildA.jetDeg :
    ∀ {K : Type} [Field K] [CharZero K] {ι : Type} [Fintype ι] [DecidableEq ι] {a b : ℕ} (lam : ι → DomWeight a) (lam' : ι → DomWeight b) (n : ι → ℕ),
      Formalism.L2.Ker.JetInVV K lam lam' n → ∀ J J' : (Formalism.L2.Ker.DVar ι a b →₀ ℕ) → K,
      (∀ m : Formalism.L2.Ker.DVar ι a b →₀ ℕ, (∀ τ, (m.sum fun v e => if v.1 = τ then e else 0) = ∑ i, (lam' τ).natW i) → J m = J' m) →
      Formalism.L2.Ker.jetOp lam lam' J n = Formalism.L2.Ker.jetOp lam lam' J' n := by
  intro K _ _ ι _ _ a b lam lam' n hV J J' h
  refine LinearMap.ext fun P => ?_
  show Formalism.L2.Ker.retrVV K lam' (Formalism.L2.Ker.jetMap J n P.1) = Formalism.L2.Ker.retrVV K lam' (Formalism.L2.Ker.jetMap J' n P.1)
  rw [jetMap_congr_deg lam lam' n hV J J' h P.1 P.2]
end

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.LatCoordB
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

section SlopeTestRemainingChoices

variable {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] {ι : Type} [Fintype ι] {n : ℕ}

private theorem lcb_mem_colLat_one (x : Fin n → K) :
    x ∈ colLat (1 : GL (Fin n) K) ↔ ∀ a, x a ∈ (1 : Submodule (𝓞 K) K) := by
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨j, rfl⟩ := hz
      intro a
      simp only [Units.val_one, Matrix.one_apply]
      split_ifs
      · exact Submodule.mem_one.2 ⟨1, map_one _⟩
      · exact zero_mem _
    | zero => intro a; exact zero_mem _
    | add y z _ _ hy hz => intro a; exact add_mem (hy a) (hz a)
    | smul c y _ hy => intro a; exact Submodule.smul_mem _ c (hy a)
  · intro hx
    choose r hr using fun a => Submodule.mem_one.1 (hx a)
    have : x = ∑ j, r j • fun a => ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) a j := by
      funext a
      simp only [Finset.sum_apply, Pi.smul_apply, Units.val_one, Matrix.one_apply, Algebra.smul_def, mul_ite, mul_zero,
        mul_one, Finset.sum_ite_eq, Finset.mem_univ, if_true, hr]
    rw [this]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

private theorem lcb_emb_int (φ : E →+* K) {x : E} (hx : x ∈ (1 : Submodule (𝓞 E) E)) :
    φ x ∈ (1 : Submodule (𝓞 K) K) := by
  obtain ⟨y, rfl⟩ := Submodule.mem_one.1 hx
  have hint : IsIntegral ℤ (φ (algebraMap (𝓞 E) E y)) := (RingOfIntegers.isIntegral_coe y).map φ.toIntAlgHom
  exact Submodule.mem_one.2 ⟨⟨_, (mem_integralClosure_iff ℤ _).2 hint⟩, rfl⟩

private theorem lcb_dot {x y : Fin n → K} (hx : ∀ a, x a ∈ (1 : Submodule (𝓞 K) K))
    (hy : ∀ a, y a ∈ (1 : Submodule (𝓞 K) K)) : x ⬝ᵥ y ∈ (1 : Submodule (𝓞 K) K) := by
  refine Submodule.sum_mem _ fun a _ => ?_
  obtain ⟨r, hr⟩ := Submodule.mem_one.1 (hx a)
  obtain ⟨t, ht⟩ := Submodule.mem_one.1 (hy a)
  exact Submodule.mem_one.2 ⟨r * t, by rw [map_mul, hr, ht]⟩

omit [Fintype ι] in
private theorem lcb_basisAt (emb : ι → E →+* K) (τ : ι) (Λ : Submodule (𝓞 E) (Fin n → E)) (s : ℕ)
    (h1 : ∀ x ∈ Λ, ∀ a, (s • x) a ∈ (1 : Submodule (𝓞 E) E))
    (h2 : ∀ j, s • (Pi.single j 1 : Fin n → E) ∈ Λ) (w : HeightOneSpectrum (𝓞 K)) (hs : (s : 𝓞 K) ∉ w.asIdeal) :
    IsBasisAt w (dualFr (tauLat emb τ Λ)) 1 := by
  apply le_antisymm
  · refine GlobalTheory.TransLoc.localization_le_of_smul_mem w hs fun φ hφ => (lcb_mem_colLat_one _).2 fun j => ?_
    have := hφ _ (Submodule.subset_span ⟨_, h2 j, rfl⟩)
    convert this using 1
    have e : (fun a => emb τ ((s • (Pi.single j 1 : Fin n → E)) a)) = s • (Pi.single j 1 : Fin n → K) := by
      funext a
      by_cases h : a = j
      · subst h; simp
      · simp [h]
    change _ = φ ⬝ᵥ (fun a => emb τ ((s • (Pi.single j 1 : Fin n → E)) a))
    rw [e, dotProduct_smul, dotProduct_single, Nat.cast_smul_eq_nsmul]
    simp
  · refine GlobalTheory.TransLoc.localization_le_of_smul_mem w hs fun φ hφ x hx => ?_
    have hx' : s • x ∈ colLat (1 : GL (Fin n) K) := by
      induction hx using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨y, hy, rfl⟩ := hz
        refine (lcb_mem_colLat_one _).2 fun a => ?_
        have := lcb_emb_int (emb τ) (h1 y hy a)
        simpa using this
      | zero => simp
      | add y z _ _ hy hz => rw [smul_add]; exact Submodule.add_mem _ hy hz
      | smul c y _ hy => rw [smul_comm]; exact Submodule.smul_mem _ c hy
    have := lcb_dot ((lcb_mem_colLat_one _).1 hφ) ((lcb_mem_colLat_one _).1 hx')
    rw [dotProduct_smul] at this
    rw [smul_dotProduct, Nat.cast_smul_eq_nsmul]
    exact this

private theorem lcb_isLattice (Λ : Submodule (𝓞 E) (Fin n → E)) (s : ℕ) (hs : s ≠ 0)
    (h1 : ∀ x ∈ Λ, ∀ a, (s • x) a ∈ (1 : Submodule (𝓞 E) E))
    (h2 : ∀ j, s • (Pi.single j 1 : Fin n → E) ∈ Λ) : Submodule.IsFullLattice E Λ := by
  have hs' : (s : E) ≠ 0 := Nat.cast_ne_zero.2 hs
  have hlat : Submodule.IsLattice E Λ := by
    apply Submodule.IsLattice.of_fg
    let f : (Fin n → E) →ₗ[𝓞 E] (Fin n → E) := s • LinearMap.id
    have hf : Function.Injective f := by
      intro x y h
      have h' : (s : E) • x = (s : E) • y := by
        rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]; exact h
      exact smul_right_injective _ hs' h'
    refine Submodule.fg_of_fg_map_injective f hf ?_
    refine Submodule.FG.of_le (M := Fin n → E) (T := colLat (1 : GL (Fin n) E)) (Submodule.fg_span (Set.finite_range _)) ?_
    rintro _ ⟨x, hx, rfl⟩
    exact (lcb_mem_colLat_one _).2 (h1 x hx)
  refine { toIsLattice := hlat, span_eq_top := ?_ }
  apply top_unique
  intro x _
  have hsingle : ∀ j : Fin n, (Pi.single j 1 : Fin n → E) ∈ Submodule.span E (Λ : Set (Fin n → E)) := by
    intro j
    have h := Submodule.smul_mem (Submodule.span E (Λ : Set (Fin n → E))) (s : E)⁻¹
      (Submodule.subset_span (h2 j))
    simpa [← Nat.cast_smul_eq_nsmul E, smul_smul, hs'] using h
  have hx : x = ∑ j, x j • (Pi.single j 1 : Fin n → E) := by
    simpa [← Pi.single_smul] using (Finset.univ_sum_single x).symm
  rw [hx]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hsingle j)

private theorem lcb_desc (φ : K →+* ℂ) (lam : ι → DomWeight n) (i : VVIdx lam) :
    ∃ F : VV K lam, (F : Pol K ι n) ∈ nabStd K lam ∧ GlobalTheory.CoefModel.mapVV φ lam F = bVV ℂ lam i := by
  have key : ∀ τ, ∃ f ∈ nablaSq (𝓞 K) n (lam τ), toK K _ f ∈ nablaSq K n (lam τ) ∧
      MvPolynomial.map φ (toK K _ f) = ssB ℂ (lam τ).natW (i τ) := by
    intro τ
    obtain ⟨k, sz, hsz, I, hsh, -, h⟩ := ((Formalism.GradedWeylDivisibility.sSBasis ℂ n n (lam τ).natW).choose_spec.2 (i τ)).2.2
    have e : toK K _ (Formalism.GradedWeylDivisibility.bideterminant (𝓞 K) sz hsz I) = Formalism.GradedWeylDivisibility.bideterminant K sz hsz I :=
      fk_map_bidet (algebraMap (𝓞 K) K) sz hsz I
    refine ⟨Formalism.GradedWeylDivisibility.bideterminant (𝓞 K) sz hsz I, ?_, ?_, ?_⟩
    · unfold nablaSq
      rw [← hsh]
      exact Formalism.GradedWeylDivisibility.bidetMem (𝓞 K) n n k sz hsz I
    · rw [e]
      unfold nablaSq
      rw [← hsh]
      exact Formalism.GradedWeylDivisibility.bidetMem K n n k sz hsz I
    · rw [e, fk_map_bidet]
      exact h.symm
  choose f hf hf' hf'' using key
  refine ⟨⟨ten fun τ => toK K _ (f τ), Submodule.subset_span ⟨_, hf', rfl⟩⟩,
    Submodule.subset_span ⟨_, fun τ => ⟨f τ, hf τ, rfl⟩, rfl⟩, Subtype.ext ?_⟩
  rw [GlobalTheory.CoefModel.mapVV_coe, bVV_coe]
  change MvPolynomial.map φ (ten fun τ => toK K _ (f τ)) = _
  rw [GlobalTheory.Proof.TensorMapDescent.map_ten]
  exact congrArg ten (funext hf'')

private theorem lcb_loc (emb : ι → E →+* K) (lam : ι → DomWeight n) (Λ : Submodule (𝓞 E) (Fin n → E)) (s : ℕ)
    (h1 : ∀ x ∈ Λ, ∀ a, (s • x) a ∈ (1 : Submodule (𝓞 E) E))
    (h2 : ∀ j, s • (Pi.single j 1 : Fin n → E) ∈ Λ) (w : HeightOneSpectrum (𝓞 K)) (hs : (s : 𝓞 K) ∉ w.asIdeal)
    (F : VV K lam) (hF : (F : Pol K ι n) ∈ nabStd K lam) : F ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (nabAtr emb lam Λ) := by
  have hs0 : s ≠ 0 := by
    rintro rfl
    exact hs (by simp)
  have hL := lcb_isLattice Λ s hs0 h1 h2
  have h := (GlobalTheory.TransLoc.nabDelLoc_free_leVV.1 K ι n lam (fun τ => dualFr (tauLat emb τ Λ))
    (fun τ => GlobalTheory.DualLat.isLattice_dualFr _ (GlobalTheory.TauLat.tauLatLattice E K ι n emb τ Λ hL)) w 1
    (fun τ => lcb_basisAt emb τ Λ s h1 h2 w hs)).1
  change (F : Pol K ι n) ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (nabP lam fun τ => dualFr (tauLat emb τ Λ))
  rw [h]
  refine ⟨F, ⟨1, fun h1 => w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1), by simpa using hF⟩, ?_⟩
  simp [actP, detTwK_one, trAct_one]

private theorem lcb_exists_vw (w : HeightOneSpectrum (𝓞 K)) (m : ℤ) : ∃ s : K, s ≠ 0 ∧ vw w s = m := by
  obtain ⟨ϖ, -, h0, h1, -⟩ := Formalism.DivisionValues.idxChange_unif (K := K) w
  have h0' : algebraMap (𝓞 K) K ϖ ≠ 0 := by simpa using h0
  refine ⟨algebraMap (𝓞 K) K ϖ ^ m, zpow_ne_zero _ h0', ?_⟩
  unfold vw
  obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg m
  · rw [zpow_natCast, ← FractionalIdeal.spanSingleton_pow, FractionalIdeal.count_pow, h1, mul_one]
  · rw [_root_.zpow_neg, zpow_natCast, ← FractionalIdeal.spanSingleton_inv, FractionalIdeal.count_inv,
      ← FractionalIdeal.spanSingleton_pow, FractionalIdeal.count_pow, h1, mul_one]

private theorem lcb_smul_loc {Z : Type} [AddCommGroup Z] [Module K Z] [Module (𝓞 K) Z] [IsScalarTower (𝓞 K) K Z]
    (w : HeightOneSpectrum (𝓞 K)) (M : Submodule (𝓞 K) Z) {a : K} (ha : a = 0 ∨ 0 ≤ vw w a) {x : Z}
    (hx : x ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal M) : a • x ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal M := by
  letI : StarRing K := starRingOfComm
  by_cases h0 : a = 0
  · rw [h0, zero_smul]; exact zero_mem _
  have h := Formalism.EigenvalueLevelCeiling.ThreeFormsAlt.mem_OO_of_vw_nonneg w h0 (ha.resolve_left h0)
  rw [Formalism.EigenvalueLevelCeiling.ThreeFormsAlt.mem_localization_iff_mem_span] at hx ⊢
  exact Submodule.smul_mem _ (⟨a, h⟩ : Formalism.EigenvalueLevelCeiling.ThreeFormsAlt.OO w) hx

end SlopeTestRemainingChoices

theorem UpperTheory.WildA.latCoordB :
    ∀ (D : D7) {n : ℕ} (lam : D.what₂.Tau → DomWeight n) (w : PlL D) (l : ℕ), l.Prime → (l : 𝓞 D.what₂.LL) ∈ w.asIdeal →
      ∀ Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E), Formalism.MainNotions.TaylorLogMetric.EqAt D l Λ (Formalism.MainNotions.StandardLatticesGL3.stdL D n) → ∀ (a : ℝ) (v : VV ℂ lam),
      (∀ i, LossLe w ((bVV ℂ lam).repr v i) a) → InLat lam w a Λ v := by
  intro D n lam w l _ hw Λ hΛ a v hv
  obtain ⟨s, hsl, h1, h2⟩ := hΛ
  have hs := GlobalTheory.GO.natCast_notMem_of_coprime hsl w hw
  have h1' : ∀ x ∈ Λ, ∀ b, (s • x) b ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) := by
    intro x hx b
    have := Submodule.mem_pi.1 (h1 x hx) b (Set.mem_univ _)
    rwa [Nat.cast_smul_eq_nsmul] at this
  have h2' : ∀ j, s • (Pi.single j 1 : Fin n → D.host.E) ∈ Λ := by
    intro j
    rw [← Nat.cast_smul_eq_nsmul D.host.E]
    refine h2 _ (Submodule.mem_pi.2 fun b _ => ?_)
    rw [Pi.single_apply]
    split_ifs
    · exact Submodule.mem_one.2 ⟨1, map_one _⟩
    · exact zero_mem _
  choose y hy hy' using hv
  choose F hF hF' using lcb_desc D.what₂.embLL lam
  obtain ⟨s₀, hs₀, hv₀⟩ := lcb_exists_vw w ⌊a⌋
  have hmem : s₀ • ∑ i, y i • F i ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (nabAtr (labLL D) lam Λ) := by
    rw [Finset.smul_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [smul_smul]
    refine lcb_smul_loc w _ ?_ (lcb_loc (labLL D) lam Λ s h1' h2' w hs (F i) (hF i))
    by_cases h0 : y i = 0
    · left; rw [h0, mul_zero]
    · right
      have h := (hy' i).resolve_left h0
      have h' : -vw w (y i) ≤ ⌊a⌋ := Int.le_floor.2 (by push_cast; linarith)
      have e : vw w (s₀ * y i) = vw w s₀ + vw w (y i) := Formalism.DivisionValues.idxChange_cnt_mul w hs₀ h0
      rw [e, hv₀]
      linarith
  obtain ⟨c, hc, hcx⟩ := (Formalism.L2.Col.mem_locP w _ _).1 hmem
  have hc0 : algebraMap _ D.what₂.LL c ≠ 0 := by
    intro h
    have : c = 0 := by simpa using h
    exact hc (this ▸ w.asIdeal.zero_mem)
  refine ⟨∑ i, y i • F i, algebraMap _ D.what₂.LL c * s₀, ?_, mul_ne_zero hc0 hs₀, ?_, ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
  · rw [map_sum]
    simp only [LinearMap.map_smulₛₗ, hy, hF']
    exact (bVV ℂ lam).sum_repr v
  · have e : vw w (algebraMap _ D.what₂.LL c * s₀) = vw w (algebraMap _ D.what₂.LL c) + vw w s₀ :=
      Formalism.DivisionValues.idxChange_cnt_mul w hc0 hs₀
    have e0 : vw w (algebraMap _ D.what₂.LL c) = 0 := Formalism.DivisionValues.idxChange_cnt_unit w hc
    rw [e, e0, hv₀, zero_add]
    exact Int.floor_le a
  · rw [mul_smul, algebraMap_smul]
    exact hcx
end

