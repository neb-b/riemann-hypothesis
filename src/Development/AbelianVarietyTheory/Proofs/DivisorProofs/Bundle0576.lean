module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0092
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0122
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0522
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0557
public import ReciprocityTheory.DualLattices.Bundle0017
public import ReciprocityTheory.DualLattices.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AinfFrobeniusSemilinearEquationExistsUnique
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.WSolve

theorem nilp_mod_p : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)], v.Integers O → ∀ x : O, ¬IsUnit x → IsNilpotent (Ideal.Quotient.mk (Ideal.span {(p : O)}) x) := by
  intro p _ C _ _ v O _ _ hp hv x hx
  have hx1 : v (algebraMap O C x) < 1 :=
    lt_of_le_of_ne (hv.map_le_one x) (fun h => hx (hv.isUnit_iff_valuation_eq_one.2 h))
  have hp0 : 0 < v (algebraMap O C (p : O)) := by
    rw [map_natCast]
    exact (Valuation.pos_iff v).2 (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hp0 hx1
  refine ⟨k, ?_⟩
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  rw [hv.dvd_iff_le, map_pow, map_pow]
  exact hk.le

theorem semilin_nil : ∀ (p : ℕ) [Fact p.Prime] (S : Type) [CommRing S] [CharP S p] (ι : Type) [Fintype ι] [DecidableEq ι] (Q : Matrix ι ι S) (N : ℕ), (∀ j i, IsNilpotent ((fun w : ι → S => Q.mulVec fun k => frobenius S p (w k))^[N] (Pi.single j 1) i)) → ∃ K : ℕ, ∀ z : ι → S, (fun w : ι → S => Q.mulVec fun k => frobenius S p (w k))^[K] z = 0 := _root_.GlobalTheory.frobSemilinear_iterate_eq_zero

theorem perf_solve : ∀ (p : ℕ) [Fact p.Prime] (S : Type) [CommRing S] [CharP S p] (ι : Type) [Fintype ι] (Q : Matrix ι ι (Perfection S p)), (∀ n : ℕ, ∃ K : ℕ, ∀ z : ι → S, (fun w : ι → S => (Q.map (Perfection.coeff S p n)).mulVec fun k => frobenius S p (w k))^[K] z = 0) → ∀ c : ι → Perfection S p, ∃! x : ι → Perfection S p, x - Q.mulVec (fun k => frobenius (Perfection S p) p (x k)) = c := _root_.GlobalTheory.perfection_frobenius_solve

theorem witt_solve : ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] [CharP R p] [PerfectRing R p] (ι : Type) [Fintype ι] (M : Matrix ι ι (WittVector p R)), (∀ c : ι → R, ∃! x : ι → R, x - (M.map WittVector.constantCoeff).mulVec (fun k => frobenius R p (x k)) = c) → ∀ c : ι → WittVector p R, ∃! v : ι → WittVector p R, v - M.mulVec (fun k => WittVector.frobenius (v k)) = c := _root_.GlobalTheory.wittSolve_unique

theorem iter_map {T T' : Type} [CommRing T] [CommRing T'] {ι : Type} [Fintype ι] (f : T →+* T')
    (σ : T →+* T) (σ' : T' →+* T') (hf : ∀ x, f (σ x) = σ' (f x)) (M : Matrix ι ι T) (k : ℕ)
    (w : ι → T) :
    (fun u : ι → T' => (M.map f).mulVec fun j => σ' (u j))^[k] (fun j => f (w j)) =
      fun i => f ((fun u : ι → T => M.mulVec fun j => σ (u j))^[k] w i) := by
  induction k generalizing w with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ← ih]
    congr 1
    funext i
    simpa only [← hf, Function.comp_def] using (RingHom.map_mulVec f M (fun j => σ (w j)) i).symm

theorem coeff_nil {S : Type} [CommRing S] {p : ℕ} [Fact p.Prime] [CharP S p] (y : Perfection S p)
    (h : IsNilpotent (Perfection.coeff S p 0 y)) (n : ℕ) : IsNilpotent (Perfection.coeff S p n y) := by
  have e : ∀ n, Perfection.coeff S p n y ^ (p ^ n) = Perfection.coeff S p 0 y := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ', pow_mul, Perfection.coeff_pow_p', ih]
  exact IsNilpotent.of_pow (m := p ^ n) (by rw [e]; exact h)

theorem key (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] (ι : Type) [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι (Ainf p O)) (N : ℕ)
    (hN : ∀ j i, IsNilpotent (Ideal.Quotient.mk (Ideal.span {(p : O)}) (WittVector.fontaineTheta O p
      ((fun w : ι → Ainf p O => M.mulVec fun k => WittVector.frobenius (w k))^[N] (Pi.single j 1) i)))) :
    ∀ c : ι → Ainf p O, ∃! v : ι → Ainf p O, v - M.mulVec (fun k => WittVector.frobenius (v k)) = c := by
  apply witt_solve p (PreTilt O p) ι M
  apply perf_solve p (ModP O p) ι (M.map WittVector.constantCoeff)
  intro n
  apply semilin_nil p (ModP O p) ι _ N
  intro j i
  have e1 : (Pi.single j 1 : ι → ModP O p) =
      fun k => Perfection.coeff (ModP O p) p n ((Pi.single j 1 : ι → PreTilt O p) k) := by
    funext k; by_cases h : k = j
    · subst h; simp only [Pi.single_eq_same]; exact (map_one _).symm
    · simp only [Pi.single_eq_of_ne h]; exact (map_zero _).symm
  have e2 : (Pi.single j 1 : ι → PreTilt O p) =
      fun k => WittVector.constantCoeff ((Pi.single j 1 : ι → Ainf p O) k) := by
    funext k; by_cases h : k = j
    · subst h; simp
    · simp [h]
  have h1 := congrFun (iter_map (T := PreTilt O p) (Perfection.coeff (ModP O p) p n)
    (frobenius (PreTilt O p) p) (frobenius (ModP O p) p) (fun x => by rw [frobenius_def, frobenius_def]; exact map_pow (Perfection.coeff (ModP O p) p n) x p)
    (M.map WittVector.constantCoeff) N (Pi.single j 1)) i
  have h2 := iter_map WittVector.constantCoeff WittVector.frobenius
    (frobenius (PreTilt O p) p) (fun x => by simp [frobenius_def, WittVector.constantCoeff_apply, WittVector.coeff_frobenius_charP]) M N (Pi.single j 1)
  rw [e1]
  erw [h1]
  rw [e2, h2]
  apply coeff_nil
  have := hN j i
  rw [WittVector.mk_fontaineTheta] at this
  exact this

theorem frobenius_mu_eq (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)]
    (ε : PreTilt O p) :
    WittVector.frobenius (Sandwich.mu ε) =
      (∑ i ∈ Finset.range p, (WittVector.teichmuller p ε) ^ i) * Sandwich.mu ε := by
  have h : WittVector.frobenius (WittVector.teichmuller p ε) = (WittVector.teichmuller p ε) ^ p := by
    rw [WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller, frobenius_def, map_pow]
  rw [Sandwich.mu, map_sub, map_one, h, geom_sum_mul]

theorem main : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (_hε : IsPrimitiveSystem ε), ∀ (ι : Type) [Fintype ι] (M : Matrix ι ι (Ainf p O)), IsNil (WittVector.fontaineTheta O p) (WittVector.frobenius : Ainf p O →+* Ainf p O) M → (∀ c : ι → Ainf p O, ∃ v : ι → Ainf p O, ∀ i, v i - M.mulVec (fun j => WittVector.frobenius (v j)) i = c i) ∧ ∀ v : ι → Ainf p O, (∀ i, Sandwich.mu ε ∣ v i - M.mulVec (fun j => WittVector.frobenius (v j)) i) → ∀ i, Sandwich.mu ε ∣ v i := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε ι _ M hM
  classical
  obtain ⟨N, hN⟩ := hM
  have hK := key p O ι M N (fun j i => nilp_mod_p p C v O hv _ (hN _ i))
  refine ⟨fun c => ?_, ?_⟩
  · obtain ⟨x, hx, -⟩ := hK c
    exact ⟨x, fun i => congrFun hx i⟩
  intro w hw
  choose u hu using hw
  have hφμ := frobenius_mu_eq p O ε
  set s : Ainf p O := ∑ i ∈ Finset.range p, (WittVector.teichmuller p ε) ^ i with hs
  have h1 : ε.untilt = 1 := by simpa [zeta] using hε.zeta_zero
  have hθs : WittVector.fontaineTheta O p s = p := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp [hs, map_sum, map_pow, WittVector.fontaineTheta_teichmuller, h1]
  have hK' := key p O ι (s • M) 1 (fun j i => by
    have e : (fun k => WittVector.frobenius ((Pi.single j 1 : ι → Ainf p O) k)) = Pi.single j 1 := by
      funext k; by_cases h : k = j
      · subst h; simp
      · simp [h]
    simp only [Function.iterate_one, e, Matrix.mulVec_single_one, Matrix.col_apply,
      Matrix.smul_apply, smul_eq_mul, map_mul, hθs]
    rw [← map_mul,
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))]
    exact IsNilpotent.zero)
  obtain ⟨w', hw', -⟩ := hK' u
  have hz : (w - Sandwich.mu ε • w') - M.mulVec (fun k => WittVector.frobenius ((w - Sandwich.mu ε • w') k)) = 0 := by
    funext i
    have a := hu i
    have b := congrFun hw' i
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Matrix.smul_apply,
      map_sub, map_mul, hφμ, Pi.zero_apply] at a b ⊢
    have hsum : ∑ x, M i x * (WittVector.frobenius (w x) - s * Sandwich.mu ε * WittVector.frobenius (w' x)) =
        ∑ x, M i x * WittVector.frobenius (w x) - Sandwich.mu ε * ∑ x, s * M i x * WittVector.frobenius (w' x) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun x _ => by ring)
    rw [hsum]
    linear_combination a - Sandwich.mu ε * b
  have h0 : (0 : ι → Ainf p O) - M.mulVec (fun k => WittVector.frobenius ((0 : ι → Ainf p O) k)) = 0 := by
    funext i; simp [Matrix.mulVec, dotProduct]
  have := (hK 0).unique hz h0
  intro i
  refine ⟨w' i, ?_⟩
  have := congrFun this i
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, sub_eq_zero] at this
  exact this

end GlobalTheory.WSolve
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BigMatConjTransposeMul
section
open Classical

noncomputable section

open MvPolynomial Matrix

namespace GlobalTheory.MinorFrame.FockRowSub

variable {ι : Type} [Fintype ι] {a d : ℕ}

def rowEquiv (ι : Type) [Fintype ι] (d : ℕ) : Fin d × ι ≃ Fin (Fintype.card (Fin d × ι)) :=
  Fintype.equivFin _

def varFlat (ι : Type) [Fintype ι] (d a : ℕ) : Var ι d a → Fin (Fintype.card (Fin d × ι)) × Fin a :=
  fun y => (rowEquiv ι d (y.2.1, y.1), y.2.2)

theorem varFlat_injective : Function.Injective (varFlat ι d a) := by
  intro y z h
  simp only [varFlat, Prod.mk.injEq] at h
  have h1 := (rowEquiv ι d).injective h.1
  simp only [Prod.mk.injEq] at h1
  exact Prod.ext h1.2 (Prod.ext h1.1 h.2)

def bigMat (κ : ι → Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin (Fintype.card (Fin d × ι))) (Fin (Fintype.card (Fin d × ι))) ℂ :=
  (blockDiagonal κ).submatrix (rowEquiv ι d).symm (rowEquiv ι d).symm

theorem rename_rowSub (κ : ι → Matrix (Fin d) (Fin d) ℂ) (P : Pol ι d a) :
    rename (varFlat ι d a) (rowSub κ P) = ReciprocityTheory.PGsh.rowSubst (bigMat κ) (rename (varFlat ι d a) P) := by
  have key : (rename (varFlat ι d a)).comp (rowSub κ) =
      (ReciprocityTheory.PGsh.rowSubst (bigMat κ)).comp (rename (varFlat ι d a)) := by
    refine MvPolynomial.algHom_ext fun y => ?_
    rw [AlgHom.comp_apply, AlgHom.comp_apply, rowSub, aeval_X, rename_X, ReciprocityTheory.PGsh.rowSubst_X,
      ← (rowEquiv ι d).sum_comp, Fintype.sum_prod_type, Finset.sum_comm, Finset.sum_eq_single y.1]
    set_option synthInstance.maxHeartbeats 100000 in
      · simp only [map_sum, map_mul, rename_C, rename_X, bigMat, submatrix_apply, varFlat, Equiv.symm_apply_apply]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [blockDiagonal_apply_eq]
    · intro τ _ hτ
      refine Finset.sum_eq_zero fun i _ => ?_
      simp [bigMat, varFlat, blockDiagonal_apply_ne _ _ _ hτ]
    · simp
  exact congrArg (fun f => f P) key

theorem bigMat_conjTranspose_mul (κ : ι → Matrix.unitaryGroup (Fin d) ℂ) :
    (bigMat fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ))ᴴ * bigMat (fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ)) = 1 := by
  rw [bigMat, conjTranspose_submatrix, submatrix_mul_equiv, blockDiagonal_conjTranspose, ← blockDiagonal_mul]
  have h : ∀ τ, (κ τ : Matrix (Fin d) (Fin d) ℂ)ᴴ * (κ τ : Matrix (Fin d) (Fin d) ℂ) = 1 := fun τ => by
    have := (κ τ).2
    rw [Matrix.mem_unitaryGroup_iff'] at this
    simpa [Matrix.star_eq_conjTranspose] using this
  simp only [h]
  rw [show (fun _ => (1 : Matrix (Fin d) (Fin d) ℂ)) = (1 : ι → Matrix (Fin d) (Fin d) ℂ) from rfl,
    blockDiagonal_one, submatrix_one_equiv]

theorem fockS_eq_fischer {ν : ℕ} {κ : Type} (f g : MvPolynomial (Fin ν × κ) ℂ) :
    Formalism.L2.DIV.fockS f g = ReciprocityTheory.PGsh.fischer g f := by
  rw [Formalism.L2.DIV.fockS_eq_sum f g (g.support ∪ f.support) Finset.subset_union_right, ReciprocityTheory.PGsh.fischer]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [Formalism.L2.DIV.mfact, Finsupp.prod, RCLike.star_def]
  ring

end GlobalTheory.MinorFrame.FockRowSub

namespace GlobalTheory.MinorFrame

open FockRowSub

theorem fockS_rowSub_unitary {ι : Type} [Fintype ι] (a d : ℕ) (κ : ι → Matrix.unitaryGroup (Fin d) ℂ)
    (P Q : Pol ι d a) :
    Formalism.L2.DIV.fockS (rowSub (fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ)) P)
      (rowSub (fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ)) Q) = Formalism.L2.DIV.fockS P Q := by
  rw [← GlobalTheory.Proof.ColumnInclusionRenaming.fockS_rename varFlat_injective, rename_rowSub, rename_rowSub, fockS_eq_fischer,
    ReciprocityTheory.PGsh.fischer_rowSubst, ReciprocityTheory.PGsh.rowSubst_mul, bigMat_conjTranspose_mul, ReciprocityTheory.PGsh.rowSubst_one,
    ← fockS_eq_fischer, GlobalTheory.Proof.ColumnInclusionRenaming.fockS_rename varFlat_injective]

end GlobalTheory.MinorFrame
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoboundaryEqAdditiveLeadingTerms
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

set_option autoImplicit false

namespace GlobalTheory.CobLead

open CategoryTheory TensorProduct MvPowerSeries in
set_option autoImplicit false in
private lemma subst_constantCoeff_zero_and_linear_coeff_eq {R : Type} [CommRing R] {d : ℕ} {τ : Type}
    (w : Fin d ⊕ Fin d → MvPowerSeries τ R) (hw : ∀ s, constantCoeff (w s) = 0)
    (F G : MvPowerSeries (Fin d ⊕ Fin d) R)
    (hFG : ∀ α : Fin d ⊕ Fin d →₀ ℕ, α.degree ≤ 1 → coeff α F = coeff α G)
    (hG : constantCoeff G = 0) :
    constantCoeff (subst w F) = 0 ∧ constantCoeff (subst w G) = 0 ∧
      ∀ γ : τ →₀ ℕ, γ.degree = 1 → coeff γ (subst w F) = coeff γ (subst w G) := by
  have hlow : ∀ H : MvPowerSeries (Fin d ⊕ Fin d) R, (∀ α : Fin d ⊕ Fin d →₀ ℕ, α.degree < 1 → coeff α H = 0) →
      constantCoeff (subst w H) = 0 := by
    intro H hH
    have h := (_root_.GlobalTheory.coeff_subst_leading R _ τ w w 1 H hw hw (fun _ _ _ => rfl) hH 0).1
      (by simp)
    rwa [coeff_zero_eq_constantCoeff_apply] at h
  have hG0 : ∀ α : Fin d ⊕ Fin d →₀ ℕ, α.degree < 1 → coeff α G = 0 := by
    intro α hα
    have : α = 0 := (Finsupp.degree_eq_zero_iff α).mp (by omega)
    rw [this, coeff_zero_eq_constantCoeff_apply, hG]
  refine ⟨hlow F (fun α hα => by rw [hFG α hα.le]; exact hG0 α hα), hlow G hG0, ?_⟩
  intro γ hγ
  have hdiff := (_root_.GlobalTheory.coeff_subst_leading R _ τ w w 2 (F - G) hw hw (fun _ _ _ => rfl)
    (fun α hα => by rw [map_sub, hFG α (by omega), sub_self]) γ).1 (by omega)
  rw [subst_sub (hasSubst_of_constantCoeff_zero hw), map_sub, sub_eq_zero] at hdiff
  exact hdiff

open CategoryTheory TensorProduct MvPowerSeries in
set_option autoImplicit false in
theorem _root_.GlobalTheory.CobLead.cob_eq_additive_lead : ∀ (R : Type) [CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (N : ℕ), (∀ i (α : Fin d ⊕ Fin d →₀ ℕ), α.degree ≤ 1 → coeff α (μ i) = coeff α (_root_.GlobalTheory.Katz.addLaw R d i)) → (∀ f : MvPowerSeries (Fin d) R, (∀ α : Fin d →₀ ℕ, α.degree < N → coeff α f = 0) → ∀ γ : Fin d ⊕ Fin d →₀ ℕ, (γ.degree < N → coeff γ (_root_.GlobalTheory.Katz.cob1 μ f) = 0) ∧ (γ.degree ≤ N → coeff γ (_root_.GlobalTheory.Katz.cob1 μ f) = coeff γ (_root_.GlobalTheory.Katz.cob1 (_root_.GlobalTheory.Katz.addLaw R d) f))) ∧ ∀ c : MvPowerSeries (Fin d ⊕ Fin d) R, (∀ α : Fin d ⊕ Fin d →₀ ℕ, α.degree < N → coeff α c = 0) → ∀ γ : Fin d ⊕ (Fin d ⊕ Fin d) →₀ ℕ, γ.degree ≤ N → coeff γ (_root_.GlobalTheory.Katz.cob2 μ c) = coeff γ (_root_.GlobalTheory.Katz.cob2 (_root_.GlobalTheory.Katz.addLaw R d) c) := by
  intro R _ d μ N hμ
  have hadd0 : ∀ i, constantCoeff (_root_.GlobalTheory.Katz.addLaw R d i) = 0 := by
    intro i
    simp [_root_.GlobalTheory.Katz.addLaw]
  have hμ0 : ∀ i, constantCoeff (μ i) = 0 := by
    intro i
    rw [← coeff_zero_eq_constantCoeff_apply, hμ i 0 (by simp), coeff_zero_eq_constantCoeff_apply, hadd0]
  have hX : ∀ {ι κ : Type} (e : ι → κ) (s : ι), constantCoeff (X (e s) : MvPowerSeries κ R) = 0 :=
    fun _ _ => by simp
  refine ⟨fun f hf γ => ⟨fun hγ => ?_, fun hγ => ?_⟩, fun c hc γ hγ => ?_⟩
  · unfold _root_.GlobalTheory.Katz.cob1 _root_.GlobalTheory.Katz.inL _root_.GlobalTheory.Katz.inR
    rw [map_sub, map_sub,
      (_root_.GlobalTheory.coeff_subst_leading R _ _ μ μ N f hμ0 hμ0 (fun _ _ _ => rfl) hf γ).1 hγ,
      (_root_.GlobalTheory.coeff_subst_leading R _ _ _ _ N f (hX Sum.inl) (hX Sum.inl)
        (fun _ _ _ => rfl) hf γ).1 hγ,
      (_root_.GlobalTheory.coeff_subst_leading R _ _ _ _ N f (hX Sum.inr) (hX Sum.inr)
        (fun _ _ _ => rfl) hf γ).1 hγ]
    simp
  · unfold _root_.GlobalTheory.Katz.cob1
    rw [map_sub, map_sub, map_sub, map_sub,
      (_root_.GlobalTheory.coeff_subst_leading R _ _ μ (_root_.GlobalTheory.Katz.addLaw R d) N f hμ0 hadd0
        (fun i γ' hγ' => hμ i γ' hγ'.le) hf γ).2 hγ]
  · have hpts : ∀ {τ : Type} (a b : Fin d → MvPowerSeries τ R), (∀ s, constantCoeff (a s) = 0) →
        (∀ s, constantCoeff (b s) = 0) → ∀ i,
          constantCoeff (_root_.GlobalTheory.Katz.op μ a b i) = 0 ∧
          constantCoeff (_root_.GlobalTheory.Katz.op (_root_.GlobalTheory.Katz.addLaw R d) a b i) = 0 ∧
          ∀ γ' : τ →₀ ℕ, γ'.degree = 1 → coeff γ' (_root_.GlobalTheory.Katz.op μ a b i) =
            coeff γ' (_root_.GlobalTheory.Katz.op (_root_.GlobalTheory.Katz.addLaw R d) a b i) := by
      intro τ a b ha hb i
      exact subst_constantCoeff_zero_and_linear_coeff_eq (Sum.elim a b) (fun s => by cases s <;> simp [ha, hb])
        (μ i) (_root_.GlobalTheory.Katz.addLaw R d i) (hμ i) (hadd0 i)
    have hs1 : ∀ s, constantCoeff (_root_.GlobalTheory.Katz.x1 (R := R) (d := d) s) = 0 := fun s => by
      simp [_root_.GlobalTheory.Katz.x1]
    have hs2 : ∀ s, constantCoeff (_root_.GlobalTheory.Katz.x2 (R := R) (d := d) s) = 0 := fun s => by
      simp [_root_.GlobalTheory.Katz.x2]
    have hs3 : ∀ s, constantCoeff (_root_.GlobalTheory.Katz.x3 (R := R) (d := d) s) = 0 := fun s => by
      simp [_root_.GlobalTheory.Katz.x3]
    have h12 := hpts _ _ hs1 hs2
    have h23 := hpts _ _ hs2 hs3
    unfold _root_.GlobalTheory.Katz.cob2 _root_.GlobalTheory.Katz.at2
    rw [map_sub, map_add (f := _), map_sub, map_sub, map_add (f := _), map_sub,
      (_root_.GlobalTheory.coeff_subst_leading R _ _
        (Sum.elim (_root_.GlobalTheory.Katz.op μ _root_.GlobalTheory.Katz.x1 _root_.GlobalTheory.Katz.x2)
          _root_.GlobalTheory.Katz.x3)
        (Sum.elim (_root_.GlobalTheory.Katz.op (_root_.GlobalTheory.Katz.addLaw R d) _root_.GlobalTheory.Katz.x1
          _root_.GlobalTheory.Katz.x2) _root_.GlobalTheory.Katz.x3) N c
        (fun s => by rcases s with s | s; exacts [(h12 s).1, hs3 s])
        (fun s => by rcases s with s | s; exacts [(h12 s).2.1, hs3 s])
        (fun s γ' hγ' => by rcases s with s | s; exacts [(h12 s).2.2 γ' hγ', rfl]) hc γ).2 hγ,
      (_root_.GlobalTheory.coeff_subst_leading R _ _
        (Sum.elim _root_.GlobalTheory.Katz.x1
          (_root_.GlobalTheory.Katz.op μ _root_.GlobalTheory.Katz.x2 _root_.GlobalTheory.Katz.x3))
        (Sum.elim _root_.GlobalTheory.Katz.x1 (_root_.GlobalTheory.Katz.op (_root_.GlobalTheory.Katz.addLaw R d)
          _root_.GlobalTheory.Katz.x2 _root_.GlobalTheory.Katz.x3)) N c
        (fun s => by rcases s with s | s; exacts [hs1 s, (h23 s).1])
        (fun s => by rcases s with s | s; exacts [hs1 s, (h23 s).2.1])
        (fun s γ' hγ' => by rcases s with s | s; exacts [rfl, (h23 s).2.2 γ' hγ']) hc γ).2 hγ]

end GlobalTheory.CobLead
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffEvalTwoGroupsThreeGroupsEqZeroOfNeZero
section
set_option autoImplicit false

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog

namespace GlobalTheory

theorem coeff_at2_x1_x2_eq_zero_of_third_ne_zero {R : Type} [CommRing R] {d : ℕ}
    (c : MvPowerSeries (Fin d ⊕ Fin d) R) (a b e : Fin d →₀ ℕ) (he : e ≠ 0) :
    coeff (Finsupp.sumElim a (Finsupp.sumElim b e)) (at2 c x1 x2) = 0 := by
  classical
  let g : Fin d ⊕ Fin d → Fin d ⊕ (Fin d ⊕ Fin d) := Sum.elim Sum.inl (Sum.inr ∘ Sum.inl)
  have hg : (Sum.elim x1 x2 : Fin d ⊕ Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) = X ∘ g := by
    funext s; rcases s with s | s <;> rfl
  have h1 : at2 c x1 x2 = rename g c := by
    rw [rename_eq_subst, ← hg]; rfl
  rw [h1]
  apply coeff_rename_eq_zero
  rintro ⟨v, hv⟩
  obtain ⟨i, hi⟩ : ∃ i, e i ≠ 0 := by
    by_contra h; push_neg at h; exact he (Finsupp.ext h)
  apply hi
  have h2 := congrArg (fun w : Fin d ⊕ (Fin d ⊕ Fin d) →₀ ℕ => w (Sum.inr (Sum.inr i))) hv
  rw [Finsupp.mapDomain_notin_range] at h2
  · simpa using h2.symm
  · rintro ⟨s, hs⟩; rcases s with s | s <;> simp [g] at hs

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffFinsuppProdConstFreeEqZeroOfDegreeLt
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.DivMono

theorem coeff_finsuppProd_eq_zero_of_degree_lt :
    ∀ (R : Type) [CommRing R] (σ τ : Type) (u : τ → MvPowerSeries σ R), (∀ j, constantCoeff (u j) = 0) →
      ∀ (α : τ →₀ ℕ) (β : σ →₀ ℕ), β.degree < α.degree → coeff β (α.prod fun j e => u j ^ e) = 0 := by
  intro R _ σ τ u hu α β hβ
  apply coeff_of_lt_order
  have hle : ((α.degree : ℕ) : ℕ∞) ≤ (α.prod fun j e => u j ^ e).order := by
    unfold Finsupp.prod
    refine le_trans ?_ (le_order_prod (fun j => u j ^ α j) α.support)
    rw [Finsupp.degree_apply, Nat.cast_sum]
    exact Finset.sum_le_sum fun j _ => le_order_pow_of_constantCoeff_eq_zero (α j) (hu j)
  exact lt_of_lt_of_le (by exact_mod_cast hβ) hle

end GlobalTheory.DivMono
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffPowerSeriesEvalTwoGroupsMemIdeal
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory.IdealAt2

theorem coeff_powerSeriesEvalTwoGroups_mem_ideal : ∀ (R : Type) [CommRing R] (d : ℕ) (τ : Type) (I : Ideal R)
    (t : MvPowerSeries (Fin d ⊕ Fin d) R) (u v : Fin d → MvPowerSeries τ R),
    (∀ i, constantCoeff (u i) = 0) → (∀ i, constantCoeff (v i) = 0) →
    (∀ α, coeff α t ∈ I) → ∀ α, coeff α (at2 t u v) ∈ I := by
  intro R _ d τ I t u v hu hv ht α
  have hs : HasSubst (Sum.elim u v) :=
    hasSubst_of_constantCoeff_zero fun s => by cases s <;> simp [hu, hv]
  rw [at2, coeff_subst hs]
  refine finsum_induction (fun x => x ∈ I) I.zero_mem (fun x y hx hy => I.add_mem hx hy) ?_
  intro e
  rw [smul_eq_mul]
  exact I.mul_mem_right _ (ht e)

end GlobalTheory.IdealAt2
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffPowerSeriesEvalTwoGroupsSecondThirdEqZero
section
open MvPowerSeries

set_option autoImplicit false

namespace GlobalTheory.Katz

theorem coeff_at2_x2_x3_eq_zero_of_first_ne_zero {R : Type} [CommRing R] {d : ℕ} (c : MvPowerSeries (Fin d ⊕ Fin d) R)
    (a b e : Fin d →₀ ℕ) (ha : a ≠ 0) :
    coeff (Finsupp.sumElim a (Finsupp.sumElim b e)) (at2 c x2 x3) = 0 := by
  classical
  have hX : ∀ s, Sum.elim (x2 (R := R) (d := d)) x3 s
      = X (Sum.elim (fun i => Sum.inr (Sum.inl i)) (fun i => Sum.inr (Sum.inr i)) s) := by
    intro s; cases s <;> rfl
  have hs : HasSubst (Sum.elim (x2 (R := R) (d := d)) x3) :=
    hasSubst_of_constantCoeff_zero fun s => by rw [hX]; exact constantCoeff_X _
  obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := by
    by_contra h; push_neg at h; exact ha (Finsupp.ext h)
  unfold at2
  rw [coeff_subst hs]
  apply finsum_eq_zero_of_forall_eq_zero
  intro α
  have key : ∃ β : Fin d ⊕ (Fin d ⊕ Fin d) →₀ ℕ, β (Sum.inl i) = 0 ∧
      (α.prod fun s k => (Sum.elim (x2 (R := R) (d := d)) x3 s) ^ k) = monomial β 1 := by
    unfold Finsupp.prod
    refine Finset.prod_induction _ (fun f => ∃ β : Fin d ⊕ (Fin d ⊕ Fin d) →₀ ℕ,
      β (Sum.inl i) = 0 ∧ f = monomial β 1) ?_ ?_ ?_
    · rintro f g ⟨β, hβ, rfl⟩ ⟨γ, hγ, rfl⟩
      exact ⟨β + γ, by simp [hβ, hγ], by rw [monomial_mul_monomial, one_mul]⟩
    · exact ⟨0, rfl, (monomial_zero_one).symm⟩
    · intro s _
      refine ⟨Finsupp.single (Sum.elim (fun i => Sum.inr (Sum.inl i)) (fun i => Sum.inr (Sum.inr i)) s) (α s), ?_, ?_⟩
      · cases s <;> simp
      · dsimp only
        rw [hX, X_pow_eq]
  obtain ⟨β, hβ, hp⟩ := key
  rw [hp, coeff_monomial_ne, smul_zero]
  intro h
  apply hi
  have := congrArg (fun w => w (Sum.inl i)) h
  simpa [hβ] using this

end GlobalTheory.Katz
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantCoeffSubstOfForallConstantCoeffZero
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory

theorem constantCoeff_subst_of_constantCoeff_zero :
    ∀ (R : Type) [CommRing R] (σ τ : Type) [Finite σ] (a : σ → MvPowerSeries τ R),
      (∀ i, constantCoeff (a i) = 0) → ∀ g : MvPowerSeries σ R,
        constantCoeff (subst a g) = constantCoeff g := by
  intro R _ σ τ _ a h g
  have ha : HasSubst a := hasSubst_of_constantCoeff_zero h
  have e : g = MvPowerSeries.C (constantCoeff g) + (g - MvPowerSeries.C (constantCoeff g)) := by ring
  conv_lhs => rw [e]
  rw [subst_add ha, map_add (f := _), subst_C,
    constantCoeff_subst_eq_zero ha h (f := g - MvPowerSeries.C (constantCoeff g)) (by simp)]
  simp

end GlobalTheory
end

