module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0003
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0440
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0464
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0457
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0123
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0125
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0452
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0135
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0153
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0463
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0448
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0139
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0140
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0143
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0148
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0447
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0462

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitOff
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

noncomputable section

namespace GlobalTheory.MovedKappaEx

def OffPrime {D : D7} (e : Formalism.L2.Theta.AE D) (q : ℕ) : Prop :=
  ∀ v ε, IsPlaceIdem D v ε → e + cA D e = algebraMap (AF D.host.F) (Formalism.L2.Theta.AE D) ε → ((q : 𝓞 D.host.F)) ∉ v.asIdeal

def splitOff {D : D7} (V : HSp D) (Q : Finset ℕ) : Subgroup (GfC V) :=
  Subgroup.closure {g | ∃ e, IsSplitIdem D e ∧ (∀ q ∈ Q, OffPrime e q) ∧ SuppAt e V (g : GA D V)}

def RatFin {D : D7} (V : HSp D) (g : GfC V) : Prop := ∃ γ ∈ GQ V, finHom V γ = finHom V (g : GA D V)

def UnitAt (q : ℕ) [Fact q.Prime] (c : ℂ) : Prop := ∀ lam : Qbar →+* ℂ_[q], ‖lamC lam c‖ = 1

section
variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
    {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

def JetKap (ch : Choice R) (p : Pair T) (x : FinPt ch.G p.small) (y : FinPt ch.G p.big) (κ : ℂ) : Prop :=
  ∀ k : FVar D (ch.G.pT p).rank (ch.G.pS p).rank →₀ ℕ,
      fockIn ch.W ch.S.N.frC p (ch.W.om p (ch.G.toPair p ((x * ch.S.N.u p.small : FinPt ch.G p.small) : Formalism.L2.Theta.GA D (ch.G.V p.small)) ((y * ch.S.N.u p.big : FinPt ch.G p.big) : Formalism.L2.Theta.GA D (ch.G.V p.big))) (ch.S.Z.vac p))
        (MvPolynomial.monomial k 1) 0 = ch.S.Z.c0 p * opp p ((k.prod fun v e => period ch.S.Z.δ v.1 ^ e) *
          Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) fun z => κ * Iop D (tor0 D D.host.ccK ch.S.Z.δ) (La0 D (tor0 D D.host.ccK ch.S.Z.δ) _ _) (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK ch.S.Z.δ) (GlobalTheory.MovedDict.srcLat ch.S.toGridChoice p x y) (GlobalTheory.MovedDict.tgtLat ch.S.toGridChoice p x y)) (ch.S.Z.e0 p) z)

end

end GlobalTheory.MovedKappaEx
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceTensorLatticeSelfDualStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlace_tensorLattice_selfDual : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E), B.IsGood σ →
    ∀ {n d : ℕ} (X : Spc F E n) (Y : Spc F E d) (r s r' s' : ℕ), X.IsHerm σ B r s → Y.IsSkew σ B r' s' →
    ∀ (v : Pl (F := F)), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v → PsiUnr B.ψ v →
    ∀ z : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evFin F v) z →
      (z ∈ latAtV X Y v ↔ ∀ γ ∈ latAtV X Y v,
        B.ψ (symp (R := AF F) (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) Y.J) z γ) = 1) := by
  first | exact @GlobalTheory.SplitLatSelfDual.latAtV_selfDual_split | exact GlobalTheory.SplitLatSelfDual.latAtV_selfDual_split | (intros; apply GlobalTheory.SplitLatSelfDual.latAtV_selfDual_split <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.StepSplittingCharactersTameLevelResidue
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.StepLaw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.StepLaw

variable {D : D7}

theorem isRes_one_of_unrAt (χ : Formalism.L2.Host.HChar D.host.E) (PP : Pl D.host.E) (h : χ.UnrAt PP) : IsRes χ PP 1 := by
  intro a k u hk hu
  have ha : a ∉ PP.asIdeal := by
    intro ha
    have h0 : (u : kP PP) = 0 := by rw [hu]; exact Ideal.Quotient.eq_zero_iff_mem.2 ha
    haveI : Nontrivial (kP PP) := Ideal.Quotient.nontrivial_iff.2 PP.isPrime.ne_top
    exact u.ne_zero h0
  have hv : Formalism.L2.Host.IsUnitAt PP (Formalism.L2.Host.atFin PP k) := by
    show Valued.v (((k : D.host.E)) : PP.adicCompletion D.host.E) = 1
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hk]
    exact (PP.valuation_eq_one_iff_notMem (K := D.host.E)).2 ha
  exact (h _ hv).symm

theorem natCast_mem_of_isConjPl {PP PP' : Pl D.host.E} (h : Lev.IsConjPl PP PP') {n : ℕ}
    (hn : (n : 𝓞 D.host.E) ∈ PP.asIdeal) : (n : 𝓞 D.host.E) ∈ PP'.asIdeal := by
  obtain ⟨c, hc, hc'⟩ := h _ hn
  have : c = (n : 𝓞 D.host.E) := by
    apply RingOfIntegers.ext
    rw [hc']
    simp
  exact this ▸ hc

theorem not_two_primes_mem (PP : Pl D.host.E) {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q)
    (h1 : (p : 𝓞 D.host.E) ∈ PP.asIdeal) (h2 : (q : 𝓞 D.host.E) ∈ PP.asIdeal) : False := by
  have hc : IsCoprime (p : 𝓞 D.host.E) (q : 𝓞 D.host.E) :=
    Nat.Coprime.cast ((Nat.coprime_primes hp hq).2 hne)
  obtain ⟨a, b, hab⟩ := hc
  apply PP.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← hab]
  exact add_mem (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_left _ _ h2)

theorem exists_prime_mem_of_isTwistPlaces {Q : Finset (Pl D.host.E)} (hQ : IsTwistPlaces D.host.g Q) {PP : Pl D.host.E}
    (h : PP ∈ Q) : ∃ q : ℕ, q.Prime ∧ (q : 𝓞 D.host.E) ∈ PP.asIdeal ∧ ∀ i, q ≠ D.host.g i := by
  obtain ⟨⟨q, hq, hc, -, hne⟩, -⟩ := hQ PP h
  refine ⟨q, hq, ?_, hne⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, ← hc, ← nsmul_one]
  exact card_nsmul_eq_zero'

theorem typePrime_mem_of_div {P : Formalism.L2.Host.PiBar D.host} {k : Fin 2} {PP : Pl D.host.E} (h : P.Div k PP) :
    ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
  have h1 := P.pb_over k
  have h2 : PP.under (𝓞 D.host.K) = P.pb k := h
  rw [← h2] at h1
  have h3 : algebraMap (𝓞 D.host.K) (𝓞 D.host.E) ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ PP.asIdeal := h1
  rwa [map_natCast] at h3

theorem TameOn.mul {χ χ' : (AE D)ˣ →* Circle} {e : AE D} {P : Finset (Pl D.host.E)}
    {c c' : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ} (h : TameOn χ e P c) (h' : TameOn χ' e P c') :
    TameOn (χ * χ') e P (fun PP => c PP * c' PP) := by
  intro x h1 hx h2 h3 u hu
  rw [MonoidHom.mul_apply, Circle.coe_mul, h x h1 hx h2 h3 u hu, h' x h1 hx h2 h3 u hu, ← Finset.prod_mul_distrib]
  simp

theorem TameOn.mul_inv_one {χ χ' : (AE D)ˣ →* Circle} {e : AE D} {P : Finset (Pl D.host.E)}
    {c : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ} (h : TameOn χ e P c) (h' : TameOn χ' e P fun _ => 1) :
    TameOn (χ * χ'⁻¹) e P c := by
  intro x h1 hx h2 h3 u hu
  have h4 := h' x h1 hx h2 h3 u hu
  rw [MonoidHom.mul_apply, MonoidHom.inv_apply, Circle.coe_mul, Circle.coe_inv, h x h1 hx h2 h3 u hu, h4]
  simp

theorem tameOn_step : ∀ (D : D7) (T0 : Type) (L : LevCh D T0) (μ0 : T0), L.Is μ0 → ∀ (t : T0) (j : Fin D.R.m), Disjoint L.Pg (L.Q t) ∧ ∀ (e : AE D) (P : Finset (Pl D.host.E)), (∀ PP, PP ∈ P ↔ PP ∈ L.Pg ∨ PP ∈ L.Q t) → IsIdemSum e P → TameOn (L.mu t ((j : ℕ) + 1)) e P (resChr L t ((j : ℕ) + 1)) ∧ TameOn (L.mu t ((j : ℕ) + 1) * L.eta⁻¹) e P (resChr L t ((j : ℕ) + 1)) := by
  classical
  intro D T0 L μ0 hL t j

  have hoff : ∀ (k : Fin 2) (PP : Pl D.host.E), ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal →
      PP ∉ L.Q t ∧ ¬ ∃ PP' ∈ L.Q t, Lev.IsConjPl PP' PP := by
    intro k PP hk
    refine ⟨fun hQ => ?_, fun ⟨PP', hQ, hc⟩ => ?_⟩
    · obtain ⟨q, hq, hm, hne⟩ := exists_prime_mem_of_isTwistPlaces (hL.Q_pl t) hQ
      exact not_two_primes_mem PP hq (D.host.g_prime k) (hne k) hm hk
    · obtain ⟨q, hq, hm, hne⟩ := exists_prime_mem_of_isTwistPlaces (hL.Q_pl t) hQ
      exact not_two_primes_mem PP hq (D.host.g_prime k) (hne k) (natCast_mem_of_isConjPl hc hm) hk
  have hPg : ∀ PP ∈ L.Pg, PP ∉ L.Q t ∧ ¬ ∃ PP' ∈ L.Q t, Lev.IsConjPl PP' PP := by
    intro PP h
    obtain ⟨k, hk⟩ := (hL.Pg PP).1 h
    exact hoff k PP (typePrime_mem_of_div hk)
  refine ⟨Finset.disjoint_left.2 fun PP h => (hPg PP h).1, fun e P hP he => ?_⟩
  have hM := L.C.isMu0 j
  have t1 : TameOn (L.mu0 ((j : ℕ) + 1)) e P (fun PP => if PP ∈ L.Pg then (L.chi ((j : ℕ) + 1) PP)⁻¹ else 1) := by
    refine GlobalTheory.T.tameHecke_integralUnits_eq_residueCharProduct D _ (L.C.mu0 j) e P _ (hL.mu0 j) hM.tame he ?_ ?_
    · intro PP h1 h2
      refine hM.unr PP fun k hk => ?_
      rcases _root_.GlobalTheory.StepLaw.div_or_isConjPl_div D L.C.P k PP hk with h | ⟨PP', h, hc⟩
      · exact h1 ((hP PP).2 (Or.inl ((hL.Pg PP).2 ⟨k, h⟩)))
      · exact h2 ⟨PP', (hP PP').2 (Or.inl ((hL.Pg PP').2 ⟨k, h⟩)), hc⟩
    · intro PP h
      by_cases hg : PP ∈ L.Pg
      · simp only [if_pos hg]
        exact hL.chi j PP hg
      · simp only [if_neg hg]
        have hQ := ((hP PP).1 h).resolve_left hg
        exact isRes_one_of_unrAt _ _ (hM.unr PP fun k hk => (hoff k PP hk).1 hQ)
  have t2 : TameOn (L.xi t) e P (fun PP => if PP ∈ L.Pg then 1 else L.xiR t PP) := by
    refine GlobalTheory.T.tameHecke_integralUnits_eq_residueCharProduct D _ (L.xiH t) e P _ (hL.xi t) (hL.xi_tame t) he ?_ ?_
    · intro PP h1 h2
      by_contra hn
      rcases (hL.Q_ram t PP).1 hn with h | ⟨PP', h, hc⟩
      · exact h1 ((hP PP).2 (Or.inr h))
      · exact h2 ⟨PP', (hP PP').2 (Or.inr h), hc⟩
    · intro PP h
      by_cases hg : PP ∈ L.Pg
      · simp only [if_pos hg]
        refine isRes_one_of_unrAt _ _ ?_
        by_contra hn
        rcases (hL.Q_ram t PP).1 hn with h | h
        · exact (hPg PP hg).1 h
        · exact (hPg PP hg).2 h
      · simp only [if_neg hg]
        exact hL.xiR t PP (((hP PP).1 h).resolve_left hg)
  have t3 : TameOn L.eta e P (fun _ => 1) :=
    GlobalTheory.T.tameHecke_integralUnits_eq_residueCharProduct D _ L.C.eta e P _ hL.eta (fun PP x hx _ => L.C.isEta.unr PP x hx) he
      (fun PP _ _ => L.C.isEta.unr PP) (fun PP _ => isRes_one_of_unrAt _ _ (L.C.isEta.unr PP))
  have t4 : TameOn (L.mu t ((j : ℕ) + 1)) e P (resChr L t ((j : ℕ) + 1)) := by
    have h := t1.mul t2
    have hc : (fun PP => (if PP ∈ L.Pg then (L.chi ((j : ℕ) + 1) PP)⁻¹ else 1) *
        (if PP ∈ L.Pg then 1 else L.xiR t PP)) = resChr L t ((j : ℕ) + 1) := by
      funext PP
      unfold resChr
      by_cases hg : PP ∈ L.Pg
      · simp only [if_pos hg, mul_one]
      · simp only [if_neg hg, one_mul]
    rw [hc] at h
    exact h
  exact ⟨t4, t4.mul_inv_one t3⟩

end GlobalTheory.StepLaw

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaChainStepVectorLocalPureTensor
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder

namespace GlobalTheory.StepVec

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem infPart_idemAt {a : AE D} {PP : Formalism.L2.DIV.Pl D.host.E} (h : Formalism.L2.NTheta.IsIdemAt a PP) : infPart D a = 0 := by
  classical
  have hs : IsIdemSum a {PP} := ⟨⟨fun _ => a, fun Q hQ => by rw [Finset.mem_singleton.1 hQ]; exact h, by simp⟩, h.1.2.1⟩
  exact GlobalTheory.PlaceDatum.infPart_idemSum hs

theorem prime_eq_of_idem {a : AE D} {P P' : Formalism.L2.DIV.Pl D.host.E} (h : Formalism.L2.NTheta.IsIdemAt a P)
    (h' : Formalism.L2.NTheta.IsIdemAt a P') : P = P' := by
  refine HeightOneSpectrum.ext (Ideal.ext fun x => ?_)
  by_cases hx : x = 0
  · rw [hx]; exact iff_of_true (zero_mem _) (zero_mem _)
  · exact (h.2 x hx).trans (h'.2 x hx).symm

set_option maxHeartbeats 2000000 in
theorem stepVecLocal : ∀ D : D7, StepVecLocal D := by
  classical
  intro D ψ θ S T sS sT ΛS ΛT βS βT LS χ Q ξ f₀ f μ 𝓕 t ht Hl cl hP hB hC _ _ hdisj hv
  obtain ⟨hvac, e, ⟨⟨es, hes, rfl⟩, hce⟩, hth⟩ := hv
  have hSd : IsSelfDualC S ΛS := hB.2.2.1
  have hTd : IsSelfDualC T ΛT := hB.2.2.2.1
  have hψ : IsStdChar D ψ (-1) := base_std hB

  generalize hs : LS.Pg ∪ Q = s at *
  have hPs : ∀ PP, PP ∈ LS.Pg → PP ∈ s := fun PP h => hs ▸ Finset.mem_union_left _ h
  have hQs : ∀ PP, PP ∈ Q → PP ∈ s := fun PP h => hs ▸ Finset.mem_union_right _ h
  have hsum := _root_.GlobalTheory.SplitIdemDict.idem_dictionary D
  choose vP φP hφ hpr using fun i : ↥s => hsum.1 (es i.1) i.1 (hes i.1 i.2)
  choose rP hrP using fun i : ↥s => (show ∃ r, IsRedMap (φP i) i.1 r from
    let ⟨r, h⟩ := (_root_.GlobalTheory.PlaceRed.red_dict D (vP i) (φP i) i.1 (hpr i)).1; ⟨r, h⟩)

  let ω : ∀ PP : Formalism.L2.DIV.Pl D.host.E, Matrix (Fin T.rank) (Fin S.rank) (Formalism.L2.DIV.kP PP) → ℂ := fun PP =>
    if h : PP ∈ LS.Pg then gLoc LS PP (Hl ⟨PP, h⟩) (cl ⟨PP, h⟩) (χ PP) else qLoc LS.r PP (ξ PP)
  let Φ : ↥s → WO S T → ℂ := fun i => locFn S T βS βT (es i.1) i.1 (ω i.1)
  have hPi : ∀ i : ↥s, (Formalism.L2.NTheta.IsIdemAt (es i.1) i.1) := fun i => hes i.1 i.2
  have hsplit : ∀ i : ↥s, IsSplitIdem D (es i.1) ∧ es i.1 + cA D (es i.1) = idem D (.inl (vP i)) := fun i =>
    ⟨(hφ i).1, (hφ i).2.1⟩
  obtain ⟨K, hK, hKC⟩ := GlobalTheory.PlaceDatum.exists_nsmul_of_frMapO
    (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ hSd)
    (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ hTd) βS βT
  have hsb : ∀ i : ↥s, IsSBHalf (es i.1) (latO S T ΛS ΛT fun _ => True) (Φ i) := fun i =>
    GlobalTheory.PlaceDatum.isSBHalf_of_red (es i.1) _ (frMapO S T βS βT) (GlobalTheory.PlaceDatum.frMapO_add βS βT)
      (GlobalTheory.PlaceDatum.exists_den_frMapO hSd.1.fg hTd.1.fg βS βT)
      ⟨K, hK, fun t ht => hKC t (GlobalTheory.PlaceDatum.infPart_of_half (infPart_idemAt (hPi i)) ht)⟩ {i.1}
      (fun y => ω i.1 (y i.1)) (fun y y' h => by rw [h i.1 (Finset.mem_singleton_self _)])

  have hcmpG : ∀ (i : ↥s) (hi : i.1 ∈ LS.Pg) (J : Subgroup (GL (Fin S.rank) ((vP i).adicCompletionIntegers D.host.F)))
      (lam : J →* ℂˣ) (mu : (Fv D.host.F (vP i))ˣ →* ℂˣ), IsLocLevel (φP i) i.1 LS (Hl ⟨i.1, hi⟩) (cl ⟨i.1, hi⟩) J lam →
      LiftsChar (φP i) i.1 mu (χ i.1) →
      onHalf (φP i) S T (frCo (φP i) βS) (frCo (φP i) βT) (es i.1) (fun y => localNewformFunction (vP i) J lam mu (rowsTB ht y)) = Φ i := by
    intro i hi J lam mu hJ hmu
    have h1 : (fun y => localNewformFunction (vP i) J lam mu (rowsTB ht y)) = viaRed (rP i) (ω i.1) := by
      funext y
      rw [GlobalTheory.T.localLevelDatum_eq_function_of_residueReduction D (vP i) (φP i) i.1 (rP i) (hrP i) _ _ t ht LS _ _ J lam hJ mu (χ i.1) hmu y]
      simp only [ω, dif_pos hi]
    rw [h1]
    exact _root_.GlobalTheory.StepVec.onHalf_viaRed_eq_locFn D (vP i) (φP i) (es i.1) i.1 (rP i) (hφ i) (hpr i) (hrP i) S T βS βT (ω i.1)
  have hcmpQ : ∀ (i : ↥s) (hi : i.1 ∈ Q) (mu : (Fv D.host.F (vP i))ˣ →* ℂˣ), LiftsChar (φP i) i.1 mu (ξ i.1)⁻¹ →
      onHalf (φP i) S T (frCo (φP i) βS) (frCo (φP i) βT) (es i.1) (phiQ (vP i) LS.r mu) = Φ i := by
    intro i hi mu hmu
    have hn : i.1 ∉ LS.Pg := fun h => Finset.disjoint_left.1 hdisj h hi
    have h1 : phiQ (vP i) LS.r mu = viaRed (b := T.rank) (a := S.rank) (rP i) (ω i.1) := by
      funext y
      rw [_root_.GlobalTheory.StepVec.phiQ_eq_viaRed_qLoc D (vP i) (φP i) i.1 (rP i) (hrP i) _ _ LS.r mu (ξ i.1) hmu y]
      simp only [ω, dif_neg hn]
    rw [h1]
    exact _root_.GlobalTheory.StepVec.onHalf_viaRed_eq_locFn D (vP i) (φP i) (es i.1) i.1 (rP i) (hφ i) (hpr i) (hrP i) S T βS βT (ω i.1)

  have hunder : ∀ i : ↥s, (i.1).asIdeal.under (𝓞 D.host.F) = (vP i).asIdeal := fun i => (hsum.2 _ _ _ (hpr i)).1
  have hcross := GlobalTheory.PlaceDatum.cross_eq_zero (R := AE D) GlobalTheory.PlaceDatum.isUnit_natCast (cA D) es s
    (fun i hi => (hes i hi).1.1) hce
  have hinj : Function.Injective vP := by
    intro i j hij
    have h1 := (hsplit i).2
    have h2 := (hsplit j).2
    rw [hij] at h1
    have h3 := GlobalTheory.PlaceDatum.idempotent_eq_of_orthogonal_decomp (hes i.1 i.2).1.1 (hes i.1 i.2).1.2.1 (hes j.1 j.2).1.1 (hes j.1 j.2).1.2.1
      (h1.trans h2.symm) (hcross _ i.2 _ j.2) (hcross _ j.2 _ i.2)
    exact Subtype.ext (prime_eq_of_idem (hes i.1 i.2) (h3 ▸ hes j.1 j.2))

  have hid : ∀ (i : ↥s) (v : FinPl D) (φ : SplitProj D v) (e' : AE D), IsIdemOf φ e' → IsProjAt φ i.1 →
      ∃ hv : v = vP i, e' = es i.1 ∧ hv ▸ φ = φP i := by
    intro i v φ e' h1 h2
    obtain ⟨hu, -, h3⟩ := hsum.2 v φ i.1 h2
    have hv : v = vP i := HeightOneSpectrum.ext (hu.symm.trans (hunder i))
    subst hv
    obtain ⟨-, h4, h5⟩ := h3 e' h1
    have h6 := h4 _ (hPi i)
    refine ⟨rfl, h6.symm, (h5 _ (h6 ▸ hφ i)).symm⟩

  have hmodel : ∀ i : ↥s, ∃ Tm, IsPlaceModel ψ (symplO S T) (heisO ψ S T) (es i.1) (latO S T ΛS ΛT fun _ => True) 1 f₀ Tm :=
    fun i => (_root_.GlobalTheory.PlaceModelOnto.placeModel_onto_local D ψ θ S T sS sT ΛS ΛT f₀ hB (vP i) (es i.1) (hsplit i).1 (hsplit i).2).1
  choose xθ hxθ using fun i : ↥s => GlobalTheory.PlaceDatum.exists_isThetaAt hψ hSd hTd (hes i.1 i.2).1.1
    (infPart_idemAt (hPi i)) (hmodel i) (hsb i)
  refine ⟨?_, ?_⟩
  · let x : Place D → WO S T → ℂ :=
      Sum.elim (fun v => if h : ∃ i, vP i = v then xθ h.choose else f₀) fun _ => f₀
    have hxi : ∀ i, x (.inl (vP i)) = xθ i := by
      intro i
      have h : ∃ j, vP j = vP i := ⟨i, rfl⟩
      show (if h : ∃ j, vP j = vP i then xθ h.choose else f₀) = xθ i
      rw [dif_pos h, hinj h.choose_spec]
    refine ⟨x, ⟨fun τ => rfl, fun v hv => ?_⟩, ?_⟩
    · show (if h : ∃ i, vP i = v then xθ h.choose else f₀) = f₀
      refine dif_neg ?_
      rintro ⟨i, rfl⟩
      exact hv i.1 i.2 (hunder i)
    · intro v φ e' he' mu
      refine ⟨fun PP hpp hmu J lam hJ => ?_, fun PP hq hpp hmu => ?_⟩
      · obtain ⟨hv, rfl, hφ'⟩ := hid ⟨PP.1, hPs _ PP.2⟩ v φ e' he' hpp
        subst hv
        obtain rfl : φ = φP ⟨PP.1, hPs _ PP.2⟩ := hφ'
        rw [hcmpG ⟨PP.1, hPs _ PP.2⟩ PP.2 J lam mu hJ hmu, hxi]
        exact hxθ _
      · obtain ⟨hv, rfl, hφ'⟩ := hid ⟨PP, hQs _ hq⟩ v φ e' he' hpp
        subst hv
        obtain rfl : φ = φP ⟨PP, hQs _ hq⟩ := hφ'
        rw [hcmpQ ⟨PP, hQs _ hq⟩ hq mu hmu, hxi]
        exact hxθ _
  · rintro x ⟨⟨hx1, hx2⟩, hloc⟩
    have hθ : ∀ i : ↥s, IsThetaAt ψ (symplO S T) (heisO ψ S T) (es i.1) (latO S T ΛS ΛT fun _ => True) 1 f₀ (Φ i)
        (x (.inl (vP i))) := by
      intro i
      by_cases hi : i.1 ∈ LS.Pg
      · obtain ⟨mu, hmu⟩ := (_root_.GlobalTheory.PlaceRed.red_dict D (vP i) (φP i) i.1 (hpr i)).2 (χ i.1)
        obtain ⟨J, lam, hJ⟩ := _root_.GlobalTheory.StepVec.exists_isLocLevel D (vP i) (φP i) i.1 (rP i) (hrP i) _ LS (Hl ⟨i.1, hi⟩) (cl ⟨i.1, hi⟩)
        have h := (hloc (vP i) (φP i) (es i.1) (hφ i) mu).1 ⟨i.1, hi⟩ (hpr i) hmu J lam hJ
        rwa [hcmpG i hi J lam mu hJ hmu] at h
      · have hq : i.1 ∈ Q := (Finset.mem_union.1 (hs ▸ i.2)).resolve_left hi
        obtain ⟨mu, hmu⟩ := (_root_.GlobalTheory.PlaceRed.red_dict D (vP i) (φP i) i.1 (hpr i)).2 (ξ i.1)⁻¹
        have h := (hloc (vP i) (φP i) (es i.1) (hφ i) mu).2 i.1 hq (hpr i) hmu
        rwa [hcmpQ i hq mu hmu] at h
    have hoff : ∀ p, (∀ i ∈ (Finset.univ : Finset ↥s), p ≠ .inl (vP i)) → x p = f₀ := by
      rintro (v | τ) h
      · refine hx2 v fun PP hPP hu => h ⟨PP, hPP⟩ (Finset.mem_univ _) ?_
        exact congrArg Sum.inl (HeightOneSpectrum.ext (hu.symm.trans (hunder ⟨PP, hPP⟩)))
      · exact hx1 τ
    have hsumes : ∑ i : ↥s, es i.1 = ∑ PP ∈ s, es PP := Finset.sum_coe_sort s es
    have hprod : ∀ y : ∀ PP : Formalism.L2.DIV.Pl D.host.E, Matrix (Fin T.rank) (Fin S.rank) (Formalism.L2.DIV.kP PP),
        omegaG LS χ y * omegaQ Q LS.r ξ 1 y = ∏ PP ∈ s, ω PP (y PP) := by
      intro y
      rw [← hs, Finset.prod_union hdisj, _root_.GlobalTheory.StepVec.omegaG_eq_prod_gLoc D _ _ LS χ Hl cl hP y, _root_.GlobalTheory.StepVec.omegaQ_one_eq_prod_qLoc D _ _ LS.r Q ξ y,
        ← Finset.prod_coe_sort LS.Pg fun PP => ω PP (y PP)]
      congr 1
      · refine Finset.prod_congr rfl fun PP _ => ?_
        simp only [ω, dif_pos PP.2]
      · refine Finset.prod_congr rfl fun PP hq => ?_
        simp only [ω, dif_neg fun h => Finset.disjoint_left.1 hdisj h hq]
    rw [← hsumes] at hth
    refine _root_.GlobalTheory.PlaceTensor.SplitProduct.thetaAt_sum_isPure D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hB hC ↥s Finset.univ vP (fun i => es i.1) (fun i _ => hsplit i)
      hinj.injOn Φ (fun i _ => hsb i) x f _ (fun i _ => hθ i) hoff ?_ ?_ hth
    · intro t' ht'
      have h := _root_.GlobalTheory.StepVec.prod_locFn_half D S T βS βT s es hes ω t' (hsumes ▸ ht')
      have h2 : ∏ i : ↥s, Φ i (es i.1 • t') = ∏ PP ∈ s, locFn S T βS βT (es PP) PP (ω PP) (es PP • t') :=
        Finset.prod_coe_sort s fun PP => locFn S T βS βT (es PP) PP (ω PP) (es PP • t')
      show (if _ then _ else _) = ∏ i : ↥s, Φ i (es i.1 • t')
      rw [h2, ← h]
      by_cases hI : IsIntM (frMapO S T βS βT t')
      · rw [if_pos ⟨ht', hI⟩, if_pos hI]
        exact hprod _
      · rw [if_neg fun h => hI h.2, if_neg hI]
    · intro t' ht'
      exact if_neg fun h => ht' h.1

end GlobalTheory.StepVec

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ToPairMul
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries

namespace GlobalTheory.RowReal

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem toPair_mul (p : Pair T) (g k : GA D (G.V p.small)) (h k' : GA D (G.V p.big)) :
    G.toPair p (g * k) (h * k') = G.toPair p g h * G.toPair p k k' := by
  cases p <;> simp [GridData.toPair, map_mul]

theorem ker_mul (W : G.Weil) (p : Pair T) (f : WO (G.pS p) (G.pT p) → ℂ) (g k : GA D (G.V p.small))
    (h k' : GA D (G.V p.big)) : W.ker p f (g * k) (h * k') = W.ker p (W.om p (G.toPair p k k') f) g h := by
  simp only [GridData.Weil.ker, thetaKO, toPair_mul, Prod.fst_mul, Prod.snd_mul, ← Prod.mk_mul_mk, Prod.mk.eta, map_mul,
    Module.End.mul_apply]

end GlobalTheory.RowReal
end
end

