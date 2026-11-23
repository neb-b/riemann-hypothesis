module

public import Mathlib
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0690
public import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveCrystalHodgeLiftClasses
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0620
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0618
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0592
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0631
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantCoeffIterateInvariantDerivationMonomial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0667
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0598
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0684
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0577
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0595
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0587
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0653
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0581
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0665
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0681
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0691
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifBaseChangeSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0062
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniformBaseChange.Transport
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CarriesAtRev
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.NonemptyCubicalPull
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0694
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0573
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0563
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0696

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InnerFockOmegaActionAdjointLines
section
noncomputable section
namespace GlobalTheory.FockAdjLines
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

theorem Jm_eq_diagonal (p q : ℕ) :
    Jm p q = Matrix.diagonal (Sum.elim (fun _ => 1) (fun _ => -1)) := by
  ext a b
  rcases a with a | a <;> rcases b with b | b <;>
    simp [Jm, Formalism.UG.Jpq, Matrix.diagonal_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem inner_omAct_adj : ∀ (p q r s : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ι : Pol p q r s →ₗ[ℂ] H), IsFockIP ι → ∀ (Z : Matrix (Ln p q r s) (Ln p q r s) ℂ) (P Q : Pol p q r s), inner ℂ (ι (omAct p q r s Z P)) (ι Q) = inner ℂ (ι P) (ι (omAct p q r s (Matrix.kroneckerMap (· * ·) (Jm p q) (Jm r s) * Z.conjTranspose * Matrix.kroneckerMap (· * ·) (Jm p q) (Jm r s)) Q)) := by
  intro p q r s H _ _ ι hι Z P Q
  refine GlobalTheory.FockAdj.inner_omAct hι _ _ ?_ P Q
  rintro ⟨a, c⟩ ⟨b, d⟩
  rw [Jm_eq_diagonal, Jm_eq_diagonal, Matrix.kroneckerMap_diagonal_diagonal _ (by simp) (by simp),
    Matrix.mul_diagonal, Matrix.diagonal_mul]
  rcases a with a | a <;> rcases b with b | b <;> rcases c with c | c <;> rcases d with d | d <;>
    simp [linePos]

end GlobalTheory.FockAdjLines
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IotaCompTrans
section
noncomputable section

namespace GlobalTheory.AbHomDesc

variable {R R₀ : Type} [CommRing R] [CommRing R₀] (I : Ideal R) (π : R →+* R₀)

def iota (hI : RingHom.ker π = I) (S : Subring R) : S ⧸ I.comap S.subtype →+* R₀ :=
  Ideal.Quotient.lift _ (π.comp S.subtype) fun x hx => by
    have h : (x : R) ∈ I := hx
    rw [← hI] at h
    exact h

theorem iota_comp_mk (hI : RingHom.ker π = I) (S : Subring R) :
    (iota I π hI S).comp (Ideal.Quotient.mk _) = π.comp S.subtype := rfl

theorem iota_injective (hI : RingHom.ker π = I) (S : Subring R) : Function.Injective (iota I π hI S) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro a ha
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [Ideal.Quotient.eq_zero_iff_mem]
  change (x : R) ∈ I
  rw [← hI]
  exact ha

def trans {S S' : Subring R} (h : S ≤ S') : S ⧸ I.comap S.subtype →+* S' ⧸ I.comap S'.subtype :=
  Ideal.quotientMap _ (Subring.inclusion h) fun x hx => hx

theorem iota_comp_trans (hI : RingHom.ker π = I) {S S' : Subring R} (h : S ≤ S') :
    (iota I π hI S').comp (trans I h) = iota I π hI S := by
  ext x
  rfl

theorem trans_comp_mk {S S' : Subring R} (h : S ≤ S') :
    (trans I h).comp (Ideal.Quotient.mk _) = (Ideal.Quotient.mk _).comp (Subring.inclusion h) := rfl

end GlobalTheory.AbHomDesc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNilDualFrobenius
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer

theorem GlobalTheory.DualFrobNil.isNil_dual_frobenius : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B), IsLift F.θ μ' → (∀ i, map F.θ (μ' i) = c.μ i) → ∀ (k : ℕ) (e : Fin d ⊕ Fin k → MvPowerSeries (Fin d) F.Q), IsBasis μ' e → IsAdapted F.θ μ' e → GlobalTheory.PDivLat.IsConn G.dual → ∀ U : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B, IsUnit U → (∀ i, In (⊤ : Ideal F.B) (frob p F.s (e i) - comb (fun l => (U * blk d k (p : F.B) 1) l i) e) ∧ ∀ i', i = Sum.inl i' → In (Ideal.span {(p : F.B)}) (frob p F.s (e i) - comb (fun l => (U * blk d k (p : F.B) 1) l i) e)) → IsNil F.θ F.σ (U.transpose⁻¹ * blk d k 1 (p : F.B)) := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε F G d c μ' hL hμ k e hB hA hconn U hU hfr
  obtain ⟨m, hmax, hpm⟩ := Ideal.exists_le_maximal (Ideal.span {(p : O)}) (by
    rw [Ne, Ideal.span_singleton_eq_top]; exact Fact.out)
  have hp : (p : O) ∈ m := hpm (Ideal.mem_span_singleton_self _)
  obtain ⟨c', hc'⟩ := _root_.GlobalTheory.FrobCoef.coef_logs_inv_frob p F.B F.Q F.s F.σ F.s_alg F.frame.inj d k e U hU hfr (fun a => (hA a).2)
    (fun r j => by obtain ⟨b, -, hb⟩ := (hB.1 r).2.1 j; exact ⟨b, hb⟩)
  refine _root_.GlobalTheory.DualFrobNilMat.isNil_of_block F.B O F.θ F.σ p m (by rw [map_natCast]; exact hp) hmax.ne_top
    (fun b => by obtain ⟨c, hc⟩ := F.σ_pow b; exact ⟨c, hc⟩) d k U c' (fun a j => (hc' a j).2) ?_
  set Sh : (Fin d → O ⧸ m) → (Fin d → O ⧸ m) :=
    fun w a => ∑ j, Ideal.Quotient.mk m (F.θ (c' a j)) * w j ^ p with hSh
  obtain ⟨n, hlift⟩ := _root_.GlobalTheory.QLog.Chart.exists_dual_lift_lin p O G d c m hp
  obtain ⟨r, hr⟩ := _root_.GlobalTheory.LocalDualNil.exists_pow_apply_mem p O G n m hmax (hconn n)
  have hθ : ∀ x ∈ RingHom.ker F.θ ⊔ Ideal.span {(p : F.B)}, F.θ x ∈ m := by
    intro x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    obtain ⟨w, rfl⟩ := Ideal.mem_span_singleton'.1 hz
    rw [map_add (f := _), RingHom.mem_ker.1 hy, zero_add, map_mul, map_natCast]
    exact m.mul_mem_left _ hp
  have step : ∀ (u : Fin d → O) (φ : G.dual.A n), (∀ Fs, φ (c.ev n Fs) - ∑ i, u i * lin Fs i ∈ m) →
      ∃ u' : Fin d → O, (∀ Fs, (φ ^ p) (c.ev n Fs) - ∑ i, u' i * lin Fs i ∈ m) ∧
        (fun a => Ideal.Quotient.mk m (u' a)) = Sh (fun a => Ideal.Quotient.mk m (u a)) := by
    intro u φ hφ
    refine ⟨fun a => constantCoeff ((invDer c.μ u)^[p] (X a)), fun Fs => ?_, ?_⟩
    · obtain ⟨t, ht⟩ := _root_.GlobalTheory.LawDer.constantCoeff_iterate_invDer_sub_linear p O d c.μ c.isLaw.const c.isLaw.unit c.isLaw.comm u Fs
      have h1 := _root_.GlobalTheory.LawDer.convPow_ev_sub_constantCoeff_iterate_mem p O G d c n m hp u φ hφ p Fs
      have h2 : (p : O) * t ∈ m := m.mul_mem_right t hp
      have e1 : (φ ^ p) (c.ev n Fs) - ∑ i, constantCoeff ((invDer c.μ u)^[p] (X i)) * lin Fs i =
          ((φ ^ p) (c.ev n Fs) - constantCoeff ((invDer c.μ u)^[p] Fs)) + p * t := by
        rw [← ht]; simp only [lin]; ring
      rw [e1]; exact m.add_mem h1 h2
    · funext a
      choose ũ hũ using fun i => F.frame.surj (u i)
      have hnat := _root_.GlobalTheory.LawDer.map_invDer_iterate F.B O F.θ d μ' hL.const ũ p (X a)
      have hmu : (fun i => map F.θ (μ' i)) = c.μ := funext hμ
      have hu : (fun i => F.θ (ũ i)) = u := funext hũ
      rw [hmu, hu, map_X] at hnat
      have key := hθ _ (_root_.GlobalTheory.FrobIter.constantCoeff_iterate_invDer_X_sub_mem p F.B O F.Q F.θ F.frame d μ' hL (e (Sum.inl a)) a (hB.1 _) (hA a).1
        (hA a).2 (c' a) (fun i => (hc' a i).1) ũ)
      have hcc : constantCoeff ((invDer c.μ u)^[p] (X a)) =
          F.θ (constantCoeff ((invDer μ' ũ)^[p] (X a))) := by
        rw [← hnat, ← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply]
      simp only [hSh]
      rw [hcc, ← hu]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [← map_pow, ← map_mul, ← map_sum]
      rw [Ideal.Quotient.eq]
      set_option synthInstance.maxHeartbeats 100000 in
        simpa [map_sub, map_sum, map_mul, map_pow] using key
  have iter : ∀ t (u : Fin d → O) (φ : G.dual.A n), (∀ Fs, φ (c.ev n Fs) - ∑ i, u i * lin Fs i ∈ m) →
      ∃ u' : Fin d → O, (∀ Fs, (φ ^ (p ^ t)) (c.ev n Fs) - ∑ i, u' i * lin Fs i ∈ m) ∧
        (fun a => Ideal.Quotient.mk m (u' a)) = Sh^[t] (fun a => Ideal.Quotient.mk m (u a)) := by
    intro t
    induction t with
    | zero => intro u φ hφ; exact ⟨u, by simpa using hφ, rfl⟩
    | succ t ih =>
      intro u φ hφ
      obtain ⟨u1, h1, e1⟩ := ih u φ hφ
      obtain ⟨u2, h2, e2⟩ := step u1 _ h1
      refine ⟨u2, fun Fs => ?_, ?_⟩
      · rw [pow_succ, pow_mul]; exact h2 Fs
      · rw [e2, e1, Function.iterate_succ_apply']
  refine ⟨r, fun w => ?_⟩
  obtain ⟨u, rfl⟩ : ∃ u : Fin d → O, (fun a => Ideal.Quotient.mk m (u a)) = w :=
    ⟨fun a => (Ideal.Quotient.mk_surjective (w a)).choose,
      funext fun a => (Ideal.Quotient.mk_surjective (w a)).choose_spec⟩
  obtain ⟨φ, hφ⟩ := hlift u
  obtain ⟨u', h', e'⟩ := iter r u φ hφ
  rw [← e']
  funext a
  have h1 : φ 1 ∈ m := by
    have := hφ 1
    simpa [lin, coeff_one] using this
  have hle : r ≤ p ^ r := (Nat.lt_pow_self (Fact.out : p.Prime).one_lt).le
  have h3 := hr φ h1 (p ^ r) hle (c.x n a)
  have h4 := h' (X a)
  rw [(c.isEval n).1 a] at h4
  have hs : ∑ i, u' i * lin (X a : MvPowerSeries (Fin d) O) i = u' a := by
    simp [lin, coeff_X, Finsupp.single_eq_single_iff]
  rw [hs] at h4
  have h5 : u' a ∈ m := by
    have := m.sub_mem h3 h4
    simpa using this
  simpa [Ideal.Quotient.eq_zero_iff_mem] using h5
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPerPull
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechPer.Nat

theorem isPer_pull : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), ∀ (A' : Over (Sp ℂ)) [GrpObj A'] (g' : ℕ) (L' : LB A'.left) (u' : HolUnif A' L' g') (φ : A' ⟶ A) (M : (Fin g' → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (h : φ.left ≫ str A = str A' ≫ spMap (RingHom.id ℂ)), (∀ w, u.ex (M w) = u'.ex w ≫ φ) → ∀ (hM : ∀ l : u'.Λ, M l ∈ u.Λ) x x' q, IsPull1 h x x' → IsPer u.ex u.Λ x q → IsPer u'.ex u'.Λ x' fun l => q ⟨M l, hM l⟩ := by
  intro A _ g L u A' _ g' L' u' φ M h hex hM x x' q hp hx
  obtain ⟨c, h₀, rfl, ⟨hd, hc, hw⟩, hq⟩ := hx
  obtain ⟨c', rfl⟩ := Hyp1.mk_surjective _ x'
  have hp' : Hyp1.mk _ (pullZZ1 (pairPull h) c) = Hyp1.mk _ (pullZZ1 (pairRes φ.left (str A')) c') := hp
  obtain ⟨b, hb⟩ := Hyp1.mk_eq_mk.1 hp'
  obtain ⟨a1, a2, a3, a4, a5, a6, -, a8, a9, a10, -, a12⟩ := _root_.GlobalTheory.CechPer.pre_val_rules A g L u
  obtain ⟨b1, b2, b3, b4, b5, b6, -, b8, b9, b10, -, b12⟩ := _root_.GlobalTheory.CechPer.pre_val_rules A' g' L' u'
  let Mc : (Fin g' → ℂ) →L[ℂ] (Fin g → ℂ) := LinearMap.toContinuousLinearMap M
  have hP := _root_.GlobalTheory.CechPer.evForm_secPull A g L u A' g' L' u' φ Mc h hex
  have hpre : ∀ (U : A.left.Opens) z, z ∈ pre u'.ex (φ.left ⁻¹ᵁ U) ↔ M z ∈ pre u.ex U := by
    intro U z
    change ⊤ ≤ (u'.ex z).left ⁻¹ᵁ (φ.left ⁻¹ᵁ U) ↔ ⊤ ≤ (u.ex (M z)).left ⁻¹ᵁ U
    rw [hex]
    rfl
  have hf : ∀ (p l : Pair φ.left) (e : l ≤ p) (a : Opposite.op p.1.1 ⟶ Opposite.op l.1.1)
      (a' : Opposite.op p.1.2 ⟶ Opposite.op l.1.2),
      (show Sec (str A') l.1.1.1 from b (Opposite.op l)) - Sec.res (str A') (Pair.le_fst e) (b (Opposite.op p)) =
        secPull (str A) (str A') l (c.1.1 _ _ a') - (show Sec (str A') l.1.1.1 from c'.1.1 _ _ a) := by
    intro p l e a a'
    exact congrArg (fun t : Tot1 (OPair φ.left (str A')) => t.1 (Opposite.op p) (Opposite.op l) (homOfLE e).op) hb
  have hω : ∀ (p : Pair φ.left), KaehlerDifferential.D ℂ (Sec (str A') p.1.1.1) (b (Opposite.op p)) =
      (semiHom_secPull h p).m1 (c.1.2 (Opposite.op p.1.2)) -
        (show Ω[Sec (str A') p.1.1.1⁄ℂ] from c'.1.2 (Opposite.op p.1.1)) := by
    intro p
    have e1 := congrArg (fun t : Tot1 (OPair φ.left (str A')) => t.2 (Opposite.op p)) hb
    have e2 : q1 (pairRes φ.left (str A')) (Opposite.op p) (c'.1.2 (Opposite.op p.1.1)) = c'.1.2 (Opposite.op p.1.1) :=
      SemiHom.oneFormMap_eq_self_of_id _ (fun _ => rfl) _
    exact e1.trans (congrArg (fun t => (semiHom_secPull h p).m1 (c.1.2 (Opposite.op p.1.2)) - t) e2)
  have hstep : ∀ (p l : Pair φ.left) (e : l ≤ p), ∀ z ∈ pre u'.ex l.1.1.1, ∀ (a : Opposite.op p.1.1 ⟶ Opposite.op l.1.1),
      h₀ l.1.2 (M z) - val u'.ex l.1.1.1 (b (Opposite.op l)) z =
        h₀ p.1.2 (M z) - val u'.ex p.1.1.1 (b (Opposite.op p)) z + val u'.ex l.1.1.1 (c'.1.1 _ _ a) z := by
    intro p l e z hz a
    obtain ⟨hz', hv, -⟩ := hP l z hz
    let a' : Opposite.op p.1.2 ⟶ Opposite.op l.1.2 := (homOfLE (Pair.le_snd e)).op
    have hs : ∀ x y v w : Sec (str A') l.1.1.1, x - y = v - w →
        val u'.ex l.1.1.1 x z - val u'.ex l.1.1.1 y z = val u'.ex l.1.1.1 v z - val u'.ex l.1.1.1 w z := by
      intro x y v w e
      obtain ⟨ev, hev⟩ := b10 _ z hz
      rw [hev x, hev y, hev v, hev w, ← map_sub, ← map_sub, e]
    have e1 : val u'.ex l.1.1.1 (b (Opposite.op l)) z -
        val u'.ex l.1.1.1 (Sec.res (str A') (Pair.le_fst e) (b (Opposite.op p))) z =
        val u'.ex l.1.1.1 (secPull (str A) (str A') l (c.1.1 _ _ a')) z - val u'.ex l.1.1.1 (c'.1.1 _ _ a) z :=
      hs _ _ _ _ (hf p l e a a')
    have e3 : val u'.ex l.1.1.1 (Sec.res (str A') (Pair.le_fst e) (b (Opposite.op p))) z =
        val u'.ex p.1.1.1 (b (Opposite.op p)) z := b9 _ _ _ _ z hz
    have e4 : val u'.ex l.1.1.1 (secPull (str A) (str A') l (c.1.1 _ _ a')) z =
        val u.ex l.1.2.1 (c.1.1 _ _ a') (M z) := hv _
    have e2 := hc p.1.2 l.1.2 a' (M z) hz'
    linear_combination e2 - e1 - e3 - e4
  refine _root_.GlobalTheory.CechPer.isPer_of_basis A' g' L' u' c' (Pair φ.left) (fun p => p.1.1)
    (fun p z => h₀ p.1.2 (M z) - val u'.ex p.1.1.1 (b (Opposite.op p)) z) _ ?_ ?_ ?_ ?_ ?_
  · intro p r z hzp hzr
    have h1 : M z ∈ pre u.ex (p.1.2.1 ⊓ r.1.2.1) := by
      rw [a5]; exact ⟨(hP p z hzp).1, (hP r z hzr).1⟩
    obtain ⟨U, hU, hzU⟩ := a8 _ _ h1
    have h2 : z ∈ pre u'.ex (p.1.1.1 ⊓ r.1.1.1 ⊓ φ.left ⁻¹ᵁ U.1) := by
      rw [b5, b5]; exact ⟨⟨hzp, hzr⟩, (hpre _ _).2 hzU⟩
    obtain ⟨W, hW, hzW⟩ := b8 _ _ h2
    let l : Pair φ.left := ⟨(W, U), hW.trans inf_le_right⟩
    have lp : l ≤ p := Subtype.coe_le_coe.1 (Prod.le_def.2
      ⟨show W.1 ≤ p.1.1.1 from hW.trans (inf_le_left.trans inf_le_left), show U.1 ≤ p.1.2.1 from hU.trans inf_le_left⟩)
    have lr : l ≤ r := Subtype.coe_le_coe.1 (Prod.le_def.2
      ⟨show W.1 ≤ r.1.1.1 from hW.trans (inf_le_left.trans inf_le_right), show U.1 ≤ r.1.2.1 from hU.trans inf_le_right⟩)
    exact ⟨l, Pair.le_fst lp, Pair.le_fst lr, hzW, hstep p l lp z hzW, hstep r l lr z hzW⟩
  · intro U' z hz
    obtain ⟨U, -, hzU⟩ := a8 _ _ (a12 (M z))
    have h2 : z ∈ pre u'.ex (U'.1 ⊓ φ.left ⁻¹ᵁ U.1) := by
      rw [b5]; exact ⟨hz, (hpre _ _).2 hzU⟩
    obtain ⟨W, hW, hzW⟩ := b8 _ _ h2
    exact ⟨⟨(W, U), hW.trans inf_le_right⟩, show W.1 ≤ U'.1 from hW.trans inf_le_left, hzW⟩
  · intro p
    exact ((hd p.1.2).comp Mc.differentiable.differentiableOn fun z hz => (hP p z hz).1).sub (b2 _ _)
  · intro p z hz
    obtain ⟨hz', -, hE⟩ := hP p z hz
    have d1 : DifferentiableAt ℂ (h₀ p.1.2) (Mc z) := (hd p.1.2).differentiableAt ((a1 _).mem_nhds hz')
    have d2 : DifferentiableAt ℂ (val u'.ex p.1.1.1 (b (Opposite.op p))) z :=
      (b2 _ _).differentiableAt ((b1 _).mem_nhds hz)
    have d3 : HasFDerivAt (fun z => h₀ p.1.2 (M z) - val u'.ex p.1.1.1 (b (Opposite.op p)) z)
        ((fderiv ℂ (h₀ p.1.2) (Mc z)).comp Mc - fderiv ℂ (val u'.ex p.1.1.1 (b (Opposite.op p))) z) z :=
      (d1.hasFDerivAt.comp z Mc.hasFDerivAt).sub d2.hasFDerivAt
    have e1 := congrArg (evForm u'.ex p.1.1.1 z) (hω p)
    rw [map_sub, hE] at e1
    have e2 := ((_root_.GlobalTheory.CechPer.evForm_rules A' g' L' u' _ z hz).2.2 (b (Opposite.op p))).symm.trans e1
    rw [d3.fderiv, hw p.1.2 _ hz']
    exact (congrArg (fun t => _ - t) e2).trans (sub_sub_cancel _ _)
  · intro p l z hz
    have e1 := hq p.1.2 ⟨M l, hM l⟩ (M z) (hP p z hz).1
    change h₀ p.1.2 (M (z + l)) - _ = _
    have e2 : val u'.ex p.1.1.1 (b (Opposite.op p)) (z + l) = val u'.ex p.1.1.1 (b (Opposite.op p)) z := b4 _ _ l z
    rw [map_add (f := _), e2]
    change h₀ p.1.2 (M z + M l) = _ at e1
    rw [e1]
    ring

end GlobalTheory.CechPer.Nat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullDegIdentitySymm
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.IndefiniteRowSideFullHecke.RigidPullbackIdentification (CarriesAt PullIdent)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

open GlobalTheory.PullDegSymm

namespace GlobalTheory.PullDegSymm

theorem carriesAt_gm {X X' Y : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {w : LB.Iso L' (L.pull F)}
    {p' : Y ⟶ X'} {p : Y ⟶ X} {hp : p' ≫ F = p} {n : ℤ}
    {a : LB.Gen (LB.LinComb L' (K := PUnit) (fun _ => p') (fun _ => n))}
    {b : LB.Gen (LB.LinComb L (K := PUnit) (fun _ => p) (fun _ => n))}
    (H : CarriesAt L L' F w p' p hp n a b) {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (j : L.ι) (j' : L'.ι)
    (h₁ : F (p' (r z)) ∈ L.U j) (h₂ : p' (r z) ∈ L'.U j') :
    gm r z (LB.wchart L (fun _ : PUnit => p) (fun _ => j)) (b.s (fun _ => j)) =
      gw w (r ≫ p') z j j' ^ n * gm r z (LB.wchart L' (fun _ : PUnit => p') (fun _ => j')) (a.s (fun _ => j')) := by
  have hm : r z ∈ p' ⁻¹ᵁ (LB.div (L.pull F) L').U (fun _ => j, j') := ⟨mem_pull.2 h₁, h₂⟩
  have e := congrArg (gm r z _) (H j j')
  refine (gm_res _ z _ hm _).symm.trans (e.trans ?_)
  exact (map_mul _ _ _).trans (congrArg₂ (· * ·) ((map_zpow _ _ _).trans (congrArg (· ^ n)
    (gm_pull _ _ z _ hm _))) (gm_res _ z _ hm _))

theorem exists_psiOn_rev : ∀ (R : Type) [CommRing R] [IsDomain R] (D D' : DegPre R) (p : PullIdent (RingHom.id R) D D')
    (W : (Spec (CommRingCat.of R)).Opens) (ψW : PsiOn D W) (g : (TK R).left ⟶ (TW W).left)
    (hg : g ≫ W.ι = jK R ≫ GlobalTheory.IndefiniteRowSideFullHecke.RigidPullbackIdentification.specOf (RingHom.id R)),
    (∀ χ : D'.X, CarriesAt D.P.L D'.P.L p.F p.w (D'.xK χ) (g ≫ (toUnit (TW W) ≫ D.c (p.xe χ)).left)
      (GlobalTheory.IndefiniteRowSideFullHecke.RigidPullbackIdentification.ptK_comp (RingHom.id R) p.F (D.c (p.xe χ)) (D'.c χ) (p.c_eq χ) W g hg) (-1) (D'.psi χ)
      (LB.pullGen D.P.L _ _ (ψW.psi (p.xe χ)) g)) →
    ∃ ψW' : PsiOn D' W, ∀ χ : D'.X, PMaps p.w (K := PUnit) (fun _ => (toUnit (TW W) ≫ D'.c χ).left)
      (fun _ => (toUnit (TW W) ≫ D.c (p.xe χ)).left) (fun _ => -1) (ψW'.psi χ) (ψW.psi (p.xe χ)) (𝟙 _) := by
  intro R _ _ D D' p W ψW g hg H
  have hgj : g ≫ W.ι = jK R := by rw [hg, specOf_id', Category.comp_id]
  have hc : ∀ χ : D'.X, ∀ _ : PUnit, (toUnit (TW W) ≫ D'.c χ).left ≫ p.F =
      𝟙 _ ≫ (toUnit (TW W) ≫ D.c (p.xe χ)).left := by
    intro χ _
    show (W.ι ≫ (D'.c χ).left) ≫ p.F = 𝟙 _ ≫ W.ι ≫ (D.c (p.xe χ)).left
    rw [Category.assoc, p.c_eq, specOf_id', Category.id_comp, Category.id_comp]
  choose ψ hψg hψm using fun χ : D'.X => GlobalTheory.DegPull.exists_pmaps ((isGen_iff _).1 p.w_gen) D.P.isLB
    D'.P.isLB (𝟙 _) (hc χ) (ψW.psi (p.xe χ)) (ψW.psi_gen _)
  refine ⟨⟨ψ, hψg, fun χ => ?_⟩, hψm⟩
  apply corr_of_val D'.P.isLB
  intro y J hJ
  rw [val_pull hJ, val_pull hJ, Category.id_comp, Category.id_comp]
  have hr : (jK R ∣_ W) ≫ W.ι = (jK R ⁻¹ᵁ W).ι ≫ jK R := morphismRestrict_ι _ _
  have hιg : (jK R ⁻¹ᵁ W).ι ≫ g = jK R ∣_ W := by
    rw [← cancel_mono W.ι, Category.assoc, hgj, hr]
  have hpt : (jK R ∣_ W) ≫ (toUnit (TW W) ≫ D'.c χ).left = (jK R ⁻¹ᵁ W).ι ≫ D'.xK χ := by
    show (jK R ∣_ W) ≫ W.ι ≫ (D'.c χ).left = (jK R ⁻¹ᵁ W).ι ≫ jK R ≫ (D'.c χ).left
    rw [← Category.assoc, hr, Category.assoc]
  obtain ⟨jD, hjD⟩ := exists_chart D.P.isLB (p.F (((jK R ⁻¹ᵁ W).ι ≫ D'.xK χ) y))
  have mq : ((jK R ⁻¹ᵁ W).ι ≫ D'.xK χ) y ∈ D'.P.L.U (J ((jK R ⁻¹ᵁ W).ι ≫ D'.xK χ)) := hJ _
  have k1 := hψm χ _ (jK R ∣_ W) y (fun _ => jD) (fun _ => J ((jK R ⁻¹ᵁ W).ι ≫ D'.xK χ))
    (fun _ => (congrArg (fun f => p.F (f y) ∈ D.P.L.U jD) hpt).mpr hjD)
    (fun _ => (congrArg (fun f => f y ∈ D'.P.L.U (J ((jK R ⁻¹ᵁ W).ι ≫ D'.xK χ))) hpt).mpr mq)
  rw [Category.comp_id, Fintype.prod_unique, hpt] at k1
  have k2 := carriesAt_gm (H χ) (jK R ⁻¹ᵁ W).ι y jD (J ((jK R ⁻¹ᵁ W).ι ≫ D'.xK χ)) hjD mq
  have hq : (jK R ⁻¹ᵁ W).ι ≫ g ≫ (toUnit (TW W) ≫ D.c (p.xe χ)).left =
      ((jK R ⁻¹ᵁ W).ι ≫ D'.xK χ) ≫ p.F := by
    rw [← Category.assoc, hιg, ← hpt, Category.assoc, hc χ PUnit.unit, Category.id_comp]
  have a := gm_pullGen D.P.L _ _ (ψW.psi (p.xe χ)) g (jK R ⁻¹ᵁ W).ι y (fun _ => jD)
    (Set.mem_iInter.2 fun _ => (congrArg (fun f => f y ∈ D.P.L.U jD) hq).mpr hjD)
  rw [hιg] at a
  rw [val_of (ψ χ) (jK R ∣_ W) y J (fun _ => J ((jK R ⁻¹ᵁ W).ι ≫ D'.xK χ)) (fun _ => by rw [hpt]),
      val_of (D'.psi χ) (jK R ⁻¹ᵁ W).ι y J (fun _ => J ((jK R ⁻¹ᵁ W).ι ≫ D'.xK χ)) (fun _ => rfl)]
  exact mul_left_cancel (k1.symm.trans (a.symm.trans k2))

theorem psiOn_carries_pullbackIdent_reverse_of_pmaps {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} (p : PullIdent (RingHom.id R) D D')
    {W : (Spec (CommRingCat.of R)).Opens} (ψW : PsiOn D W) {g : (TK R).left ⟶ (TW W).left}
    (hg : g ≫ W.ι = jK R ≫ GlobalTheory.IndefiniteRowSideFullHecke.RigidPullbackIdentification.specOf (RingHom.id R)) (ψW' : PsiOn D' W)
    (hψ : ∀ χ : D'.X, PMaps p.w (K := PUnit) (fun _ => (toUnit (TW W) ≫ D'.c χ).left)
      (fun _ => (toUnit (TW W) ≫ D.c (p.xe χ)).left) (fun _ => -1) (ψW'.psi χ) (ψW.psi (p.xe χ)) (𝟙 _))
    (χ : D.X) (χ' : D'.X) (hχ : p.xe χ' = χ) (hx : D.xK χ ≫ Finv p = g ≫ (toUnit (TW W) ≫ D'.c χ').left) :
    CarriesAt D'.P.L D.P.L (Finv p) (wInv p) (D.xK χ) (g ≫ (toUnit (TW W) ≫ D'.c χ').left) hx (-1) (D.psi χ)
      (LB.pullGen D'.P.L _ _ (ψW'.psi χ') g) := by
  subst hχ
  rw [carriesAt_iff]
  intro y j jD h₁ h₂
  have hgj : g ≫ W.ι = jK R := by rw [hg, specOf_id', Category.comp_id]
  have hP : g ≫ (toUnit (TW W) ≫ D.c (p.xe χ')).left = D.xK (p.xe χ') := by
    show g ≫ W.ι ≫ (D.c (p.xe χ')).left = jK R ≫ (D.c (p.xe χ')).left
    rw [← Category.assoc, hgj]
  have m₁ : (toUnit (TW W) ≫ D'.c χ').left (g y) ∈ D'.P.L.U j :=
    (congrArg (fun f => f y ∈ D'.P.L.U j) hx).mp h₁
  have m₂ : p.F ((toUnit (TW W) ≫ D'.c χ').left (g y)) ∈ D.P.L.U jD := by
    have : p.F ((toUnit (TW W) ≫ D'.c χ').left (g y)) = D.xK (p.xe χ') y := by
      have e := congrArg (fun f => f y) hx
      exact (congrArg p.F e.symm).trans (base_cancel (Finv_F p) _)
    rw [this]; exact h₂
  have k := hψ χ' (TK R).left g y (fun _ => jD) (fun _ => j) (fun _ => m₂) (fun _ => m₁)
  rw [Category.comp_id, Fintype.prod_unique] at k
  obtain ⟨J, hJ, eJ⟩ := exists_good D.P.L D.P.isLB y (fun _ : PUnit => D.xK (p.xe χ')) (fun _ => jD)
    (fun _ _ _ => rfl) (fun _ => h₂)
  have v := GlobalTheory.ArcSpecialise.psiOn_generic ψW (p.xe χ') g (𝟙 _) (by rw [hgj, Category.id_comp]) hJ
  rw [val_of _ g y J (fun _ => jD) (fun _ => by rw [hP]; exact eJ PUnit.unit),
    val_of _ (𝟙 _) y J (fun _ => jD) (fun _ => by rw [Category.id_comp]; exact eJ PUnit.unit)] at v
  have a₁ := gm_pullGen D'.P.L _ _ (ψW'.psi χ') g (𝟙 _) y (fun _ => j) (Set.mem_iInter.2 fun _ => m₁)
  rw [Category.id_comp] at a₁
  have key : ∀ {G : Type} [CommGroup G] (A B C E : G), C = A ^ (-1 : ℤ) * B → C = E → B = A⁻¹ ^ (-1 : ℤ) * E := by
    intro G _ A B C E h₁ h₂
    rw [← h₂, h₁]; group
  refine a₁.trans ?_
  rw [show gw (wInv p) (D.xK (p.xe χ')) y j jD = _ from gw_revIso p.w (Finv_F p) _ y j jD h₁ h₂, hx]
  exact key _ _ _ _ k v

theorem psi_carries_rev : ∀ (R : Type) [CommRing R] [IsDomain R] (D D' : DegPre R) (p : PullIdent (RingHom.id R) D D')
    (W : (Spec (CommRingCat.of R)).Opens) (ψW : PsiOn D W) (g : (TK R).left ⟶ (TW W).left)
    (hg : g ≫ W.ι = jK R ≫ GlobalTheory.IndefiniteRowSideFullHecke.RigidPullbackIdentification.specOf (RingHom.id R)) (ψW' : PsiOn D' W),
    (∀ χ : D'.X, PMaps p.w (K := PUnit) (fun _ => (toUnit (TW W) ≫ D'.c χ).left)
      (fun _ => (toUnit (TW W) ≫ D.c (p.xe χ)).left) (fun _ => -1) (ψW'.psi χ) (ψW.psi (p.xe χ)) (𝟙 _)) →
    ∀ χ : D.X, CarriesAt D'.P.L D.P.L (GlobalTheory.PullDegSymm.Finv p) (GlobalTheory.PullDegSymm.wInv p) (D.xK χ)
      (g ≫ (toUnit (TW W) ≫ D'.c (p.xe.symm χ)).left)
      (GlobalTheory.IndefiniteRowSideFullHecke.RigidPullbackIdentification.ptK_comp (RingHom.id R) (GlobalTheory.PullDegSymm.Finv p) (D'.c (p.xe.symm χ)) (D.c χ)
        (GlobalTheory.PullDegSymm.c_eq' p χ) W g hg) (-1) (D.psi χ) (LB.pullGen D'.P.L _ _ (ψW'.psi (p.xe.symm χ)) g) := fun R _ _ D D' p W ψW g hg ψW' hψ χ =>
  psiOn_carries_pullbackIdent_reverse_of_pmaps p ψW hg ψW' hψ χ (p.xe.symm χ) (p.xe.apply_symm_apply χ) _

theorem isPullDeg_symm : ∀ (R : Type) [CommRing R] [IsDomain R] (D D' : DegPre R),
    IsPullDeg (RingHom.id R) D D' → Nonempty (IsPullDeg (RingHom.id R) D' D) := by
  intro R _ _ D D' hD
  obtain ⟨p⟩ := GlobalTheory.PullDegCompare.nonempty_iff.1 ⟨hD⟩
  obtain ⟨W, ψW, g, hg, H⟩ := p.w_psi
  obtain ⟨ψW', hψ⟩ := exists_psiOn_rev R D D' p W ψW g hg H
  exact GlobalTheory.PullDegCompare.nonempty_iff.2 ⟨⟨Finv p, cart' p, F_one' p, F_mul' p, wInv p, wInv_isGen p, w_rig' p,
    p.xe.symm, c_eq' p, ⟨W, ψW', g, hg, psi_carries_rev R D D' p W ψW g hg ψW' hψ⟩⟩⟩

end GlobalTheory.PullDegSymm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTestPullbackStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isTest_comp_isPullD_of_isTest : ∀ (Rg : Type) [CommRing Rg] (A B : Over (Sp Rg)) [GrpObj A] [GrpObj B] (L : LB A.left) (M : LB B.left) (T T' : Scheme.{0}) (t : T ⟶ Sp Rg) (h : T' ⟶ T) (A₁ B₁ : Over T) [GrpObj A₁] [GrpObj B₁] (φA₁ : A₁.left ⟶ A.left) (φB₁ : B₁.left ⟶ B.left) (Φ₁ : A₁ ⟶ B₁), IsTest A B L M t A₁ B₁ φA₁ φB₁ Φ₁ → ∃ (A₂ : Over T') (_ : GrpObj A₂) (B₂ : Over T') (_ : GrpObj B₂) (φA₂ : A₂.left ⟶ A.left) (φB₂ : B₂.left ⟶ B.left) (Φ₂ : A₂ ⟶ B₂), IsTest A B L M (h ≫ t) A₂ B₂ φA₂ φB₂ Φ₂ ∧ IsPullD φA₁ φB₁ Φ₁ φA₂ φB₂ Φ₂ h := by
  first | (exact @GlobalTheory.HomFixMat.isTest_pullback) | (exact GlobalTheory.HomFixMat.isTest_pullback) | (intros; apply GlobalTheory.HomFixMat.isTest_pullback  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneWhittakerVectorDimHolds
section
namespace GlobalTheory.GenericProduct

theorem oneGenericVector : OneGenericVector := GlobalTheory.T.whittakerSpaceDim_parabolicInduction_cuspidal_eq_one

theorem genericMultOne_holds : GlobalTheory.IndefiniteRowSideFullHecke.GenericMultiplicityOne.GenericMultOne := genericMultOne oneGenericVector

theorem oneWhittakerVector_holds : GlobalTheory.IndefiniteRowSideFullHecke.CuspidalInducedCharacter.OneWhittakerVector :=
  GlobalTheory.CuspidalIdempotentCharacters.genericMultOne_iff.1 genericMultOne_holds

end GlobalTheory.GenericProduct
end

