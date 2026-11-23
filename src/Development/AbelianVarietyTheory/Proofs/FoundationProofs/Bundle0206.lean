module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0203
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0317
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
public import Formalism.LocalRingCardinality.Bundle0007
public import Formalism.LocalRingCardinality.DataRRMetric
public import Formalism.LocalToGlobal.LatticeGeometry.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0204
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0205
public import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
public import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0009
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0157
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0220
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0217
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0362
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0607
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0115
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0136
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0126
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0006
public import ReciprocityTheory.GaloisValuations.Global
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0103
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0160
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0090

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EdgeClassCupProductGeometricStatement
section
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.edge_class_cup_product_geometric : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ c₁ : ℕ, ∃ c : ℕ, ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : GlobalTheory.K5.Tower p Ω) (L n : ℕ), n ≤ L → ∀ (x y lz lq η : Gal p Ω → ZMod (p ^ n)) (f : Ω),
  (∀ g ∈ Gn T L, ∀ h ∈ Gn T L, x (g * h) = x g + x h ∧ y (g * h) = y g + y h) →
  IsKum T n (Gn T L) (T.ζ (L + n)) lz → IsKum T n (Gn T L) (T.qq (L + n)) lq → IsInt (p := p) f → (∀ g ∈ Gn T L, g f = f) →
  (∀ g ∈ (Ggeo p Ω ⊓ Gn T L), ∀ h ∈ (Ggeo p Ω ⊓ Gn T L), x g * y h = η h - η (g * h) + η g) →
  (∀ g ∈ (Ggeo p Ω ⊓ Gn T L), ∃ S : Finset Ω, ∀ h ∈ (Ggeo p Ω ⊓ Gn T L), (∀ z ∈ S, h z = g z) → η h = η g) →
  Cob2 n (Gn T L) (fun g h => (p : Ω) ^ c₁ * (((x g).val : Ω) * ((y h).val : Ω)) + (p : Ω) ^ c₁ * f * (((lz g).val : Ω) * ((lq h).val : Ω))) →
  ∃ o : Ω, IsInt (p := p) o ∧ (∀ g ∈ (Ggeo p Ω ⊓ Gn T L), g o = o) ∧ ∀ σ ∈ Gn T L,
    Cob1 n (Ggeo p Ω ⊓ Gn T L) (fun h => (p : Ω) ^ c * ((η (σ * h * σ⁻¹) - η h - x h * y σ + x σ * y h).val : Ω) - (σ⁻¹ o - o - (p : Ω) ^ c * f * ((lz σ).val : Ω)) * ((lq h).val : Ω)) := by
  first | exact @GlobalTheory.EdgeAlg.edge_class_cup | exact GlobalTheory.EdgeAlg.edge_class_cup | (intros; apply GlobalTheory.EdgeAlg.edge_class_cup <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFixingMulFrobAt
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.KZ Matrix

namespace GlobalTheory.KZ

theorem exists_fixing_mul_frobAt :
    ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (s : Ω ≃ₐ[ℚ] Ω) (E0 : Finset Ω) (S : Finset ℕ),
      ∃ (s' : Ω ≃ₐ[ℚ] Ω) (q : ℕ), (∀ x ∈ E0, s' x = x) ∧ q.Prime ∧ q ∉ S ∧ FrobAt q (s * s') := by
  intro Ω _ _ _ s E0 S
  have : IsGalois ℚ Ω := {}
  let K : IntermediateField ℚ Ω := IntermediateField.adjoin ℚ (E0 : Set Ω)
  have : FiniteDimensional ℚ K :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  have hKo : IsOpen (K.fixingSubgroup : Set (G ℚ Ω)) := IntermediateField.fixingSubgroup_isOpen K
  let V : Set (G ℚ Ω) := {φ | s⁻¹ * φ ∈ K.fixingSubgroup}
  have hVo : IsOpen V := hKo.preimage (continuous_const_mul s⁻¹)
  have hVne : V.Nonempty := ⟨s, by simp [V, K.fixingSubgroup.one_mem]⟩
  let T : ℕ := ∏ p ∈ S.filter (· ≠ 0), p
  have hT : T ≠ 0 := Finset.prod_ne_zero_iff.2 fun p hp => (Finset.mem_filter.1 hp).2
  have hS : {v : HeightOneSpectrum (𝓞 ℚ) | (T : 𝓞 ℚ) ∈ v.asIdeal}.Finite :=
    (Ideal.finite_factors (I := Ideal.span {(T : 𝓞 ℚ)}) (by simpa using hT)).subset
      fun _ hv => Ideal.dvd_span_singleton.2 hv
  obtain ⟨φ, hφV, v, hv, hd, B, hB, hφ⟩ :=
    (GlobalTheory.Published.ChebotarevDegreeOne.dense (F := ℚ) (Ω := Ω) GlobalTheory.Published.chebotarevDegreeOne' hS).inter_open_nonempty
      V hVo hVne
  have h2 : Ideal.absNorm v.asIdeal = normV v := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]; rfl
  have hmem : ((normV v : ℕ) : 𝓞 ℚ) ∈ v.asIdeal := h2 ▸ Ideal.absNorm_mem v.asIdeal
  have hq : (normV v).Prime := by
    rw [← h2]
    exact ((GlobalTheory.absNorm_prime_iff_inertiaDeg_eq_one_and_finite_ramified ℚ).1 v).2 hd
  refine ⟨s⁻¹ * φ, normV v, ?_, hq, ?_, ?_⟩
  · intro x hx
    exact (mem_fixingSubgroup_iff _).1 hφV x (IntermediateField.subset_adjoin ℚ _ (by simpa using hx))
  · intro hqS
    apply hv
    show (T : 𝓞 ℚ) ∈ v.asIdeal
    have hdvd : normV v ∣ T := Finset.dvd_prod_of_mem _ (Finset.mem_filter.2 ⟨hqS, hq.ne_zero⟩)
    obtain ⟨k, hk⟩ := hdvd
    rw [hk, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ hmem
  · rw [mul_inv_cancel_left]
    have hqB : B.valuation ((normV v : ℕ) : Ω) < 1 := by
      have := (hB ((normV v : ℕ) : 𝓞 ℚ)).2 hmem
      simpa using this
    refine ⟨B, (ValuationSubring.mem_nonunits_iff _).2 hqB, fun x hx => ?_⟩
    have hx1 : B.valuation x ≤ 1 := (B.valuation_le_one_iff x).2 hx
    have hlt := hφ.2 x hx1
    refine ⟨?_, hlt⟩
    have hxq : x ^ normV v ∈ B := pow_mem hx _
    have hd' : φ x - x ^ normV v ∈ B := (B.valuation_le_one_iff _).1 hlt.le
    simpa using add_mem hd' hxq

end GlobalTheory.KZ

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsProvisionalDivX
section
open Formalism.BasicNotions NumberField

noncomputable section

namespace GlobalTheory.ProvisionalDivX

section Form

variable {K : Type} [Field K] (e : K →+* ℂ) {W : Type} [AddCommGroup W] [Module ℂ W] {n : ℕ}
  (c : Module.Basis (Fin n) ℂ W)

end Form

structure MjForm (D : D7) (j : ℕ) where

  H : HLat D.what₂.LL

  jm : H.V →ₛₗ[D.what₂.embLL] D.what₂.Mj j
  good : H.Good
  basis : LinearIndependent ℂ (fun i => jm (H.b i)) ∧
    Submodule.span ℂ (Set.range (fun i => jm (H.b i))) = ⊤
  lat : 1 ≤ j → j ≤ D.R.m → ∀ x, x ∈ H.L ↔ ∃ c : D.what₂.Mj j → 𝓞 D.what₂.LL,
    jm x = ∑ v ∈ (D.what₂.MjLat j).gen, D.what₂.embLL ((c v : 𝓞 D.what₂.LL) : D.what₂.LL) • v
  sub : 1 ≤ j → j ≤ D.R.m → ∀ x ∈ (D.what₂.MjLat j).gen, x ∈ Set.range jm
  metric : ∀ x, Formalism.HermitianLatticesTheory.cnorm (Formalism.HermitianLatticesTheory.fcoord H.b H.X
    (InfinitePlace.mk D.what₂.embLL) x) = ‖jm x‖

theorem resChar_eq_iff (D : D7) {p : ℕ} (hp : p.Prime) (w : D.what₂.places.Pl) :
    D.what₂.places.resChar w = p ↔ (p : 𝓞 D.what₂.LL) ∈ (D.plEq w).asIdeal := by
  constructor
  · intro h; rw [← h]; exact resChar_mem D w
  · intro hmem
    by_contra hne
    have hcop : Nat.Coprime (D.what₂.places.resChar w) p :=
      (Nat.coprime_primes (D.what₂.places.resChar_prime w) hp).mpr hne
    obtain ⟨a, b, hab⟩ : IsCoprime ((D.what₂.places.resChar w : ℕ) : 𝓞 D.what₂.LL) (p : 𝓞 D.what₂.LL) :=
      hcop.cast
    apply (D.plEq w).isPrime.ne_top
    rw [Ideal.eq_top_iff_one, ← hab]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (resChar_mem D w)) (Ideal.mul_mem_left _ _ hmem)

def placeEquiv (D : D7) (p : ℕ) [hp : Fact p.Prime] :
    Formalism.L2.Geo.PlL D p ≃ {w : D.what₂.places.Pl // D.what₂.places.resChar w = p} :=
  (D.plEq.subtypeEquiv (resChar_eq_iff D hp.out)).symm

theorem wtL_eq_ramIdx_mul (D : D7) (p : ℕ) [hp : Fact p.Prime] (la : Formalism.L2.Geo.PlL D p) :
    Formalism.L2.Geo.wtL D p la = (D.what₂.places.ramIdx (placeEquiv D p la).1 : ℝ) *
      (padicValNat p (Ideal.absNorm (D.plEq (placeEquiv D p la).1).asIdeal) : ℝ) /
        (Module.finrank ℚ D.what₂.LL : ℝ) := by
  have he : D.plEq (placeEquiv D p la).1 = la.1 := D.plEq.apply_symm_apply _
  have := liesOver_of_mem p hp.out la.1 la.2
  have hN := Ideal.pow_inertiaDeg p la.1.asIdeal
  have hlog : Real.log (p : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hp.out.one_lt)).ne'
  have hval : padicValNat p (p ^ la.1.asIdeal.inertiaDeg ℤ) = la.1.asIdeal.inertiaDeg ℤ := by
    rw [Nat.padicValNat_def, Nat.multiplicity_prime_pow]
  rw [D.ram_eq, he, Formalism.L2.Geo.wtL, ← hN, hval]
  push_cast
  rw [Real.log_pow]
  field_simp

def smallShim (D : D7) (r : ℕ) : DV.ShimX D.what₂.Tau :=
  provisionalShimX D.what₂.Tau (max r 2) 1 ∅ le_rfl (by omega) (by simp)

end GlobalTheory.ProvisionalDivX

namespace GlobalTheory

open ProvisionalDivX

def provisionalDivX (D : D7) (G : DV.Geo D.what₂.LL) (Y : G.Var)
    (jc : ∀ (p : ℕ) [Fact p.Prime], DV.KW p →+* ℂ)
    (M : ∀ (p : ℕ) [Fact p.Prime] (r : ℕ),
      DV.Mdl D p (max r 2) (DV.rkOf (DV.PsiOf D (jc p)) (max r 2) 1))
    (F : ∀ j, MjForm D j) : DivX D :=
  letI := D.host.cmStar
  { geo := G
    Lev := Unit
    levPr := fun _ => ∅
    shv := fun S _ => smallShim D S.rank
    shv_N := fun _ _ h => max_eq_left h
    shv_lev := fun _ _ => rfl
    PlP := fun p _ => Formalism.L2.Geo.PlL D p
    plpFin := fun p _ => Formalism.L2.Geo.finPl D p
    plpNe := fun p _ => Formalism.L2.Geo.plL_ne D p
    wtP := fun p _ => Formalism.L2.Geo.wtL D p
    divisorWeight_nonneg := fun p _ => Formalism.L2.Geo.wtL_nonneg D p
    divisorWeight_sum := fun p _ => Formalism.L2.Geo.wtL_sum D p
    plP := fun p _ => placeEquiv D p
    divisorWeight_def := fun p _ => wtL_eq_ramIdx_mul D p
    jC := fun p _ _ => jc p
    Mp := fun _ _ _ _ _ => Unit
    md := fun S _ p _ _ _ => M p S.rank
    vdd := fun _ _ => 0
    vdd_unram := fun _ _ _ => rfl
    phiFr_unram := fun _ _ _ _ _ _ => rfl
    vdd_nonneg := fun _ _ => le_rfl
    CurveM := fun _ _ _ _ _ _ => Empty
    degM := fun _ _ _ _ _ _ _ _ => 0
    htMdl := fun _ _ _ _ _ => ()
    htCurve := fun _ _ p _ =>
      { toFun := fun c => Empty.elim c
        invFun := fun c => c.2
        left_inv := fun c => Empty.elim c
        right_inv := fun c => Empty.elim c.2 }
    htCurve_deg := fun _ _ _ _ c => Empty.elim c
    MjH := fun j => (F j).H
    MjH_good := fun j => (F j).good
    jM := fun j => (F j).jm
    jM_basis := fun j => (F j).basis
    jM_lat := fun j => (F j).lat
    MjLat_sub := fun j => (F j).sub
    jM_metric := fun j _ _ => (F j).metric
    Qp := fun _ => ∅
    degreeZero_partial_set_empty := rfl
    Qp_muAt := fun _ => Finset.notMem_empty _
    Qp_g := fun _ _ _ => Finset.notMem_empty _
    QPl := fun _ => Empty
    qv := fun _ v => v.elim
    qv_gt := fun _ v => v.elim
    qv_char := fun _ _ v => v.elim
    nu := fun _ v => v.elim
    nu_ne := fun _ v => v.elim
    nu_abs := fun _ v => v.elim
    ZQ := fun _ v => v.elim
    quotientLocalValueFirst := fun _ v => v.elim
    typeDim := fun _ v => v.elim
    Comp := fun _ => Unit
    degHH := fun _ _ _ => 0
    Yv := fun _ _ => Y
    Ybd := fun _ _ => G.supp Y 0
    Lw := fun _ _ => 0
    iMj := fun _ _ => 0
    iMj_mem := fun _ _ _ => Submodule.zero_mem _
    logLam := fun j σ _ => Real.log (D.what₂.lamP D.what₂.mu0 j σ)
    logLam_base := fun _ _ => rfl
    kapR := fun _ => kapSharp D
    kapR_pos := fun _ => RowSide.kapOf_pos _ _
    kapR_conj := fun _ => rfl
    Surf := Empty
    surfCh2 := fun s => s.elim
    surfDegOm := fun s => s.elim
    SurfFp := Empty
    surfFpCh2 := fun s => s.elim }

end GlobalTheory

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ShimuraReciprocityConjugateFormLevel
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FNConj

theorem slash_neg_one_even {k : ℤ} (hk : Even k) (f : ℍ → ℂ) : f ∣[k] (-1 : SL(2, ℤ)) = f := by
  ext τ
  simp only [ModularForm.SL_slash_apply, ModularGroup.SL_neg_smul, one_smul]
  have : UpperHalfPlane.denom ((-1 : SL(2, ℤ)) : GL (Fin 2) ℝ) τ = (-1) * UpperHalfPlane.denom ((1 : SL(2, ℤ)) : GL (Fin 2) ℝ) τ := by
    simp [UpperHalfPlane.denom]
  rw [this, mul_zpow, (hk.neg).neg_one_zpow]
  simp [UpperHalfPlane.denom]

theorem redGL_neg_one (N : ℕ) : redGL N (-1) = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [redGL, Matrix.SpecialLinearGroup.coe_neg]

theorem redGL_gamma (N : ℕ) (γ : SL(2, ℤ)) (h : γ ∈ CongruenceSubgroup.Gamma N) : redGL N γ = 1 := by
  rw [CongruenceSubgroup.Gamma_mem] at h
  obtain ⟨h00, h01, h10, h11⟩ := h
  ext i j
  fin_cases i <;> fin_cases j <;> simp [redGL, h00, h01, h10, h11]

end GlobalTheory.FNConj

namespace GlobalTheory.FNConj

theorem main : ∀ (g : ℂ ≃+* ℂ) (N : ℕ) [NeZero N] (d : (ZMod N)ˣ) (k : ℕ) (f : ℍ → ℂ), ZetaAct g N d → Even k →
    (∀ γ ∈ CongruenceSubgroup.Gamma N, f ∣[(k : ℤ)] γ = f) → (∀ γ : SL(2, ℤ), ∃ a, HasQ N (f ∣[(k : ℤ)] γ) a) →
    ∃ f' : ℍ → ℂ, (∀ γ ∈ CongruenceSubgroup.Gamma N, f' ∣[(k : ℤ)] γ = f') ∧
      ∀ γ γ' : SL(2, ℤ), dg d * redGL N γ' = redGL N γ * dg d → QConj g N (f ∣[(k : ℤ)] γ) (f' ∣[(k : ℤ)] γ') := by
  intro g N _ d k f hg hk hinv hq
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  obtain ⟨hvact, hgact, hvass, -, -, -, -, -, -⟩ := GlobalTheory.WpFam.Act.rightActions N
  obtain ⟨c₁, c₂, hsep⟩ := _root_.GlobalTheory.FNSep.sep_family N
  obtain ⟨-, hadd, hsmul, -⟩ := GlobalTheory.QFam.isFam_algebra (GL (Fin 2) (ZMod N)) (gact N 1)
  obtain ⟨-, hadd', hsmul', -⟩ := GlobalTheory.QFam.isFam_algebra (GL (Fin 2) (ZMod N)) (gact N (dg d))
  obtain ⟨qc, qadd, -, qmul, -⟩ := GlobalTheory.QFam.qConj_ring g N hN

  set t : GL (Fin 2) (ZMod N) → ℍ → ℂ := fun α τ => wp N (vmul ![1, 0] α) τ + (c₁ : ℂ) * wp N (vmul ![0, 1] α) τ +
    (c₂ : ℂ) * wp N (vmul ![1, 1] α) τ with ht
  set t' : GL (Fin 2) (ZMod N) → ℍ → ℂ := fun α => t (α * dg d) with ht'
  have hw : ∀ e : Fin 2 → ZMod N, IsFam (gact N 1) 2 (fun α => wp N (vmul e α)) := fun e => by
    have := (GlobalTheory.WpFamGL.main N 1 e).1
    simpa only [mul_one] using this
  have hw' : ∀ e : Fin 2 → ZMod N, IsFam (gact N (dg d)) 2 (fun α => wp N (vmul e (α * dg d))) := fun e =>
    (GlobalTheory.WpFamGL.main N (dg d) e).1
  have htF : IsFam (gact N 1) 2 t :=
    (hadd _ _ _ (hadd _ _ _ (hw _) (hsmul _ _ _ (hw _))).1 (hsmul _ _ _ (hw _))).1
  have htF' : IsFam (gact N (dg d)) 2 t' :=
    (hadd' _ _ _ (hadd' _ _ _ (hw' _) (hsmul' _ _ _ (hw' _))).1 (hsmul' _ _ _ (hw' _))).1
  have hqw : ∀ (e : Fin 2 → ZMod N) (α : GL (Fin 2) (ZMod N)),
      QConj g N (wp N (vmul e α)) (wp N (vmul e (α * dg d))) := fun e α => by
    rw [← hvass]
    exact (GlobalTheory.WpFam.ConjExp.qConj_torsion N g d hg (vmul e α)).1
  have hqn : ∀ (c : ℕ) (e : Fin 2 → ZMod N) (α : GL (Fin 2) (ZMod N)),
      QConj g N (fun τ => (c : ℂ) * wp N (vmul e α) τ) (fun τ => (c : ℂ) * wp N (vmul e (α * dg d)) τ) := by
    intro c e α
    have := qmul _ _ _ _ (qc (c : ℂ)) (hqw e α)
    simpa only [map_natCast] using this
  have htq : ∀ α, QConj g N (t α) (t' α) := fun α =>
    qadd _ _ _ _ (qadd _ _ _ _ (hqw _ α) (hqn c₁ _ α)) (hqn c₂ _ α)

  obtain ⟨F, hF, hFγ, hF0⟩ := GlobalTheory.T.exists_slTwoPermutedModularFamily_of_level N (k : ℤ) f hinv
  have hFneg : ∀ α, F (-α) = F α := fun α => by
    have h1 := hF α (-1)
    rw [slash_neg_one_even (by exact_mod_cast hk.natCast) (F α)] at h1
    rw [h1, gact_one, redGL_neg_one, mul_neg_one]
  have hsepF : ∀ i j, t i = t j → F i = F j := fun i j h => by
    rcases hsep i j h with rfl | rfl
    · rfl
    · exact hFneg j
  have hFq : ∀ i, ∃ a, HasQ N (F i) a := fun i => by
    rcases hF0 i with ⟨γ, rfl⟩ | h0
    · rw [hFγ]; exact hq γ
    · refine ⟨fun _ => 0, fun τ => ?_⟩
      rw [h0]; simpa using (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℂ)) 0)
  obtain ⟨F', hF', hFF'⟩ := _root_.GlobalTheory.FN.conj_family_sep g (GL (Fin 2) (ZMod N)) (gact N 1) (gact N (dg d)) 2 k N t t' F hN
    (IsRAct.actBij (hgact 1)) (IsRAct.actBij (hgact (dg d))) htF htF' hF hsepF htq hFq
  have hslash : ∀ γ : SL(2, ℤ), F' 1 ∣[(k : ℤ)] γ = F' (dg d * redGL N γ * (dg d)⁻¹) := fun γ => by
    rw [hF' 1 γ, gact, one_mul]
  refine ⟨F' 1, fun γ hγ => ?_, fun γ γ' hγγ' => ?_⟩
  · rw [hslash, redGL_gamma N γ hγ, mul_one, mul_inv_cancel]
  · rw [hslash, hγγ', mul_inv_cancel_right, ← hFγ]
    exact hFF' _

end GlobalTheory.FNConj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaKillsFplusDiscreteForm
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.KZ GlobalTheory.Glue
open scoped MatrixGroups

namespace GlobalTheory.ThKill

theorem cgA_natCast {Ω : Type} [Field Ω] [Algebra ℚ Ω] (A : ValuationSubring Ω) (l n a b : ℕ)
    (h : ((a : ℕ) : ZMod (l ^ n)) = ((b : ℕ) : ZMod (l ^ n))) : CgA A l n (a : Ω) (b : Ω) := by
  have h' : ((a : ℤ) : ZMod (l ^ n)) = ((b : ℤ) : ZMod (l ^ n)) := by exact_mod_cast h
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h'
  obtain ⟨k, hk⟩ := h'
  refine ⟨((-k : ℤ) : Ω), intCast_mem A (-k), ?_⟩
  have hk' : ((b : ℤ) : Ω) - ((a : ℤ) : Ω) = ((l : ℤ) : Ω) ^ n * (k : Ω) := by
    have := congrArg (fun z : ℤ => (z : Ω)) hk
    push_cast at this ⊢
    linear_combination this
  push_cast at hk' ⊢
  linear_combination -hk'

theorem cgA_trans {Ω : Type} [Field Ω] [Algebra ℚ Ω] {A : ValuationSubring Ω} {l n : ℕ} {x y z : Ω}
    (h1 : CgA A l n x y) (h2 : CgA A l n y z) : CgA A l n x z := by
  obtain ⟨a, ha, e1⟩ := h1
  obtain ⟨b, hb, e2⟩ := h2
  exact ⟨a + b, add_mem ha hb, by linear_combination e1 + e2⟩

theorem cgA_mul {Ω : Type} [Field Ω] [Algebra ℚ Ω] {A : ValuationSubring Ω} {l n : ℕ} {x y t : Ω}
    (h : CgA A l n x y) (ht : t ∈ A) : CgA A l n (x * t) (y * t) := by
  obtain ⟨a, ha, e⟩ := h
  exact ⟨a * t, mul_mem ha ht, by linear_combination t * e⟩

theorem gamma1_le_of_dvd {N M : ℕ} (h : N ∣ M) :
    CongruenceSubgroup.Gamma1 M ≤ CongruenceSubgroup.Gamma1 N := by
  intro γ hγ
  rw [CongruenceSubgroup.Gamma1_mem] at hγ ⊢
  obtain ⟨h1, h2, h3⟩ := hγ
  have key : ∀ x y : ℤ, ((x : ZMod M)) = (y : ZMod M) → (x : ZMod N) = (y : ZMod N) := by
    intro x y hxy
    have := congrArg (ZMod.castHom h (ZMod N)) hxy
    simpa using this
  refine ⟨?_, ?_, ?_⟩
  · simpa using key _ 1 (by simpa using h1)
  · simpa using key _ 1 (by simpa using h2)
  · simpa using key _ 0 (by simpa using h3)

theorem isThB_level_mul {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (A : ValuationSubring Ω)
    (N M l n : ℕ) [Fact l.Prime] (b : X.Fn l) (φ : HahnSeries ℚ Ω) (h : IsThB X A N l n b φ) :
    IsThB X A (N * M) l n b φ := by
  obtain ⟨f, hI, hc, hδ, hD⟩ := h
  have hle : CongruenceSubgroup.Gamma1 (N * M * l ^ n) ≤ CongruenceSubgroup.Gamma1 (N * l ^ n) :=
    gamma1_le_of_dvd ⟨M, by ring⟩
  refine ⟨f, fun γ hγ => hI γ (hle hγ), hc, fun δ hδ' hneg => ?_, hD⟩
  obtain ⟨g, hg, e⟩ := hδ δ (gamma1_le_of_dvd (dvd_mul_right N M) hδ') hneg
  exact ⟨g, fun γ hγ => hg γ (hle hγ), e⟩

theorem B_level_mul {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (N M l w : ℕ) [Fact l.Prime] :
    X.B N l w ≤ X.B (N * M) l w := by
  apply Submodule.span_mono
  rintro b ⟨hp, hg⟩
  refine ⟨hp, fun γ hγ => hg γ ?_⟩
  rw [Gam, Subgroup.mem_inf] at hγ ⊢
  exact ⟨gamma1_le_of_dvd (dvd_mul_right N M) hγ.1, hγ.2⟩

theorem auxiliaryLevel_coprime_ge_five (l N : ℕ) [hl : Fact l.Prime] (hN : 1 ≤ N) (hlN : ¬ l ∣ N) :
    5 ≤ N * (if l = 5 then 7 else 5) ∧ ¬ l ∣ N * (if l = 5 then 7 else 5) := by
  refine ⟨?_, ?_⟩
  · split_ifs <;> nlinarith
  · intro h
    rcases (Nat.Prime.dvd_mul hl.out).1 h with h' | h'
    · exact hlN h'
    · split_ifs at h' with h5
      · subst h5; norm_num at h'
      · have := (Nat.prime_dvd_prime_iff_eq hl.out (by norm_num)).1 h'
        exact h5 this

theorem discrete (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    (ε : Ω →+* ℂ) (X : Tower Ω ε) (A : ValuationSubring Ω) (hj : ∃ φ : ℂ → ℂ, X.an X.jK = (φ : Mero) ∧ DifferentiableOn ℂ φ Hs) (hA : A.valuation (l : Ω) < 1) (hl2 : l ≠ 2)
    (N : ℕ) (hN : 1 ≤ N) (hlN : ¬ l ∣ N) (w : ℕ) (hw : Odd w) (F : Finset Ω) :
    ∃ c : ℕ, ∀ v : X.Fn l, v ∈ X.B N l w →
      (∀ s ∈ Ine (F := ℚ) A, (∀ y ∈ F, s y = y) → X.galB l s v = ((cycZ ℚ Ω l s : ℤ_[l]) ^ (w + 1)) • v) →
      ∀ (n : ℕ) (φ : HahnSeries ℚ Ω), IsThB X A N l n v φ → ∀ r, CgA A l n ((l : Ω) ^ c * φ.coeff r) 0 := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  obtain ⟨c, hc⟩ := GlobalTheory.T.integral_tate_inertia_cyclotomic_twist_torsion l Ω A hA (w + 1) (by omega) F
  refine ⟨c, fun v hv hgal n φ hφ r => ?_⟩
  have hφA : ∀ r, φ.coeff r ∈ A := by
    obtain ⟨f, -, -, -, hDl⟩ := hφ
    exact hDl.1
  refine hc n (φ.coeff r) (hφA r) (fun s hs hF => ?_)
  have hsA : ∀ x, x ∈ A ↔ s x ∈ A := fun x => (apply_mem_iff_of_mem_Dec (Ine_le_Dec A hs) x).symm
  set u : ℤ_[l] := (cycZ ℚ Ω l s : ℤ_[l]) ^ (w + 1) with hu
  have h1 := GlobalTheory.isThB_galB Ω ε X A N l n w s ((ValuationSubring.mem_nonunits_iff A).2 hA) hsA v hv φ hφ
  rw [hgal s hs hF] at h1
  have h2 := GlobalTheory.ThAdd.isThB_add Ω ε X A N l n w v v ((ValuationSubring.mem_nonunits_iff A).2 hA) hv hv u 0 φ φ hφ hφ
  rw [zero_smul, add_zero] at h2
  have huv : u • v ∈ X.B N l w := Submodule.smul_mem _ u hv
  obtain ⟨hN5, hlN5⟩ := auxiliaryLevel_coprime_ge_five l N hN hlN
  have h3 := GlobalTheory.T.cuspFunctionalValueModPrimePow_unique_oddWeight Ω ε X A _ l hj hl2 hlN5 hN5 ((ValuationSubring.mem_nonunits_iff A).2 hA) n w hw (u • v)
    (B_level_mul X N _ l w huv) _ _ (isThB_level_mul X A N _ l n _ _ h1) (isThB_level_mul X A N _ l n _ _ h2) r

  have h0 : ((0 : ℤ_[l]).appr n : ℕ) = 0 := by
    have hlt := PadicInt.appr_lt (0 : ℤ_[l]) n
    have hk : ((PadicInt.toZModPow n (0 : ℤ_[l]) : ZMod (l ^ n))) = 0 := map_zero _
    have hk' : (((0 : ℤ_[l]).appr n : ℕ) : ZMod (l ^ n)) = 0 := hk
    rw [ZMod.natCast_eq_zero_iff] at hk'
    exact Nat.eq_zero_of_dvd_of_lt hk' hlt
  rw [h0] at h3
  have e : ((((u.appr n : ℕ)) : Ω) • φ + ((0 : ℕ) : Ω) • φ).coeff r = ((u.appr n : ℕ) : Ω) * φ.coeff r := by simp
  have e' : (HahnSeries.map φ (s : Ω →+* Ω)).coeff r = s (φ.coeff r) := rfl
  rw [e, e'] at h3
  have hcg : CgA A l n ((u.appr n : ℕ) : Ω) ((((cycMod ℚ Ω l n s : ZMod (l ^ n)).val ^ (w + 1) : ℕ) : Ω)) :=
    cgA_natCast A l n _ _ (by
      have e1 : (((u.appr n : ℕ)) : ZMod (l ^ n)) = PadicInt.toZModPow n u := rfl
      rw [e1, hu, map_pow]
      push_cast
      congr 1
      simp [cycMod])
  rw [Nat.cast_pow] at hcg
  exact cgA_trans h3 (cgA_mul hcg (hφA r))

theorem th_kills_Fplus_discrete : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (A : ValuationSubring Ω),
  (∃ φ : ℂ → ℂ, X.an X.jK = (φ : Mero) ∧ DifferentiableOn ℂ φ Hs) → A.valuation (l : Ω) < 1 → ∀ (N w : ℕ) (F : Finset Ω), l ≠ 2 → ¬ l ∣ N → 1 ≤ N → Odd w → ∃ c : ℕ, ∀ b : X.Fn l, b ∈ X.B N l w →
  (∀ s ∈ Ine (F := ℚ) A, (∀ y ∈ F, s y = y) → X.galB l s b = ((cycZ ℚ Ω l s : ℤ_[l]) ^ (w + 1)) • b) →
  ∀ (n : ℕ) (φ : HahnSeries ℚ Ω), IsThB X A N l n b φ → ∀ r, CgA A l n ((l : Ω) ^ c * φ.coeff r) 0 := by
  intro l _ Ω _ _ _ ε X A hj hA N w F hl2 hlN hN hw
  exact discrete l Ω ε X A hj hA hl2 N hN hlN w hw F

end GlobalTheory.ThKill
end

