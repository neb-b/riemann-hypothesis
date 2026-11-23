module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0015
public import Development.WeilBound.CoreStatements.HodgeTatePoints.FlagbAlg
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0005
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0016

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.ExistsLineBundleTwistMulOf
section
namespace PositivityTheory.HtPt.KtwS

open GroundTheory.Heights₂.Heights.Kleiman MvPolynomial

noncomputable section

universe u v w

section Helpers

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem exists_lineBundle_pow (hLT : LineTwist.Statement.{u, w}) (Q : LineBundle S x) (n : ℕ) :
    ∃ Q' : LineBundle S x, Q'.toSubSystem = Q.toSubSystem.pow n := by
  induction n with
  | zero => exact ⟨twistBundle S x 0, rfl⟩
  | succ n ih =>
    obtain ⟨Q', hQ'⟩ := ih
    obtain ⟨Q'', hQ''⟩ := hLT S Ω N x Q' Q
    exact ⟨Q'', by rw [hQ'', hQ']; rfl⟩

theorem exists_lineBundle_twistMulOf (hLT : LineTwist.Statement.{u, w}) (M : LineBundle S x) (a : ℕ)
    (c : ℤ) : ∃ Q : LineBundle S x, Q.toSubSystem = twistMul M.toSubSystem a c := by
  obtain ⟨P, hP⟩ := exists_lineBundle_pow hLT M a
  obtain ⟨Q, hQ⟩ := hLT S Ω N x P (twistBundle S x c)
  exact ⟨Q, by rw [hQ, hP]; rfl⟩

variable {K' : Type w} [Field K'] [Algebra S K'] {y : Fin (N + 1) → K'}

theorem exists_restrict_pow (hLT : LineTwist.Statement.{u, w}) (hRT : RestrictTwist.Statement.{u, w})
    (hxy : ∀ i, y i ≠ 0 → x i ≠ 0) (hle : primeOf (S := S) x ≤ primeOf (S := S) y)
    (M : LineBundle S x) (M' : LineBundle S y) (r : Ω → K')
    (h : RestrictData M.toSubSystem hxy M'.toSubSystem r) (n : ℕ) :
    ∃ (Q : LineBundle S x) (Q' : LineBundle S y) (r' : Ω → K'), Q.toSubSystem = M.toSubSystem.pow n ∧
      Q'.toSubSystem = M'.toSubSystem.pow n ∧ RestrictData Q.toSubSystem hxy Q'.toSubSystem r' := by
  induction n with
  | zero =>
    obtain ⟨r', hr'⟩ := hRT.1 S Ω N x K' y hxy hle 0
    exact ⟨twistBundle S x 0, twistBundle S y 0, r', rfl, rfl, hr'⟩
  | succ n ih =>
    obtain ⟨Q, Q', r', hQ, hQ', hr⟩ := ih
    obtain ⟨Qn, hQn⟩ := hLT S Ω N x Q M
    obtain ⟨Qn', hQn'⟩ := hLT S K' N y Q' M'
    obtain ⟨r'', hr''⟩ := hRT.2 S Ω N x K' y hxy Q M Q' M' r' r hr h
    refine ⟨Qn, Qn', r'', by rw [hQn, hQ]; rfl, by rw [hQn', hQ']; rfl, ?_⟩
    rw [hQn, hQn']
    exact hr''

theorem exists_restrict_twistMul_pow (hLT : LineTwist.Statement.{u, w})
    (hRT : RestrictTwist.Statement.{u, w}) (hxy : ∀ i, y i ≠ 0 → x i ≠ 0)
    (hle : primeOf (S := S) x ≤ primeOf (S := S) y) (M : LineBundle S x) (M' : LineBundle S y)
    (r : Ω → K') (h : RestrictData M.toSubSystem hxy M'.toSubSystem r) (a : ℕ) (c : ℤ) (b : ℕ) :
    ∃ (Q : LineBundle S x) (Q' : LineBundle S y) (r' : Ω → K'),
      Q.toSubSystem = (twistMul M.toSubSystem a c).pow b ∧
      Q'.toSubSystem = (twistMul M'.toSubSystem a c).pow b ∧
      RestrictData Q.toSubSystem hxy Q'.toSubSystem r' := by
  obtain ⟨P, P', rP, hP, hP', hrP⟩ := exists_restrict_pow hLT hRT hxy hle M M' r h a
  obtain ⟨rc, hrc⟩ := hRT.1 S Ω N x K' y hxy hle c
  obtain ⟨L, hL⟩ := hLT S Ω N x P (twistBundle S x c)
  obtain ⟨L', hL'⟩ := hLT S K' N y P' (twistBundle S y c)
  obtain ⟨rL, hrL⟩ := hRT.2 S Ω N x K' y hxy P (twistBundle S x c) P' (twistBundle S y c) rP rc hrP hrc
  obtain ⟨Q, Q', r', hQ, hQ', hr'⟩ := exists_restrict_pow hLT hRT hxy hle L L' rL
    (by rw [hL, hL']; exact hrL) b
  refine ⟨Q, Q', r', ?_, ?_, hr'⟩
  · rw [hQ, hL, hP]; rfl
  · rw [hQ', hL', hP']; rfl

end Helpers

section OnW

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem StepTwo.onW (hLT : LineTwist.Statement.{u, w}) (hTA : TwistAlg.Statement.{u, w})
    (hRT : RestrictTwist.Statement.{u, w}) (hNR : NefRestrict.Statement.{u, w})
    (hJP : StepData.JProper.Statement.{u, w}) (hDrop : SubvarDrop.Statement.{u, w})
    (hPt : PrimeFiltration.Point.Statement.{u, w}) (hRes : PrimeFiltration.Restrict.Statement.{u, w})
    (hRQ : PrimeFiltration.RestrictQuot.Statement.{u, w}) (hTV : TwistVanish.Statement.{u, w})
    (T : StepData k x) (hK : ∀ e ≤ T.d, VeryAmpleNefPlusAmple.InDim.{u, w} k e)
    (pp : Ideal (Poly k N)) (hpr : pp.IsPrime) (hhom : ∀ p ∈ pp, ∀ d : ℕ, homogeneousComponent d p ∈ pp)
    (hle : primeOf (S := k) x ≤ pp) (hJ : ∀ (f : Poly k N) (e : ℕ), f ∈ T.J → f.IsHomogeneous e → f ∈ pp)
    (hrel : ∃ j, (X j : Poly k N) ∉ pp) :
    ∃ c₁ : ℤ, ∀ (b : ℕ) (Q : LineBundle k x), Q.toSubSystem = T.L.pow b → ∀ c : ℤ, c₁ ≤ c →
      Subsingleton (SubSystem.quotH (Q.twist (twistSys k x c))
        ((Q.twist (twistSys k x c)).twist (idealSys x pp)) 1) := by
  obtain ⟨j, hjp⟩ := hrel
  have hj : x j ≠ 0 := fun h0 => hjp (hle ((mem_primeOf_of_isHomogeneous x (isHomogeneous_X k j)).mpr
    (by rw [aeval_X]; exact h0)))
  obtain ⟨hcp, hpt⟩ := hPt k Ω N x pp hpr hhom hle j hj hjp

  have := hcp
  let A := chartRing k x (singleChart hj)
  let I : Ideal A := chartPrime pp hj
  let ψ : A →ₐ[k] I.ResidueField := IsScalarTower.toAlgHom k A I.ResidueField
  have hker : RingHom.ker ψ = I := Ideal.ker_algebraMap_residueField I
  have hxy : ∀ i, ψ (ratio hj i) ≠ 0 → x i ≠ 0 := by
    intro i h hx
    apply h
    have h0 : ratio (S := k) hj i = 0 := Subtype.ext (by change x i / x j = 0; rw [hx, zero_div])
    rw [h0, map_zero]
  have hpy : primeOf (S := k) (fun i => ψ (ratio hj i)) = pp := hpt _ ψ hker
  have hxy' : primeOf (S := k) x ≤ primeOf (S := k) (fun i => ψ (ratio hj i)) := hpy ▸ hle

  obtain ⟨f, e₀, hfJ, hfh, hfq⟩ := hJP k Ω N x T
  obtain ⟨e, he, hsub⟩ := hDrop k Ω N x T.d pp T.dim hpr hhom hle ⟨j, hjp⟩ ⟨f, hJ f e₀ hfJ hfh, hfq⟩
  have hsubW : IsSubvar (fun i => ψ (ratio hj i))
      (primeOf (S := k) (fun i => ψ (ratio hj i))) e := by
    rw [hpy]
    exact ⟨hsub.isPrime, hsub.homog, le_of_eq hpy, hsub.relevant, hsub.dim⟩

  obtain ⟨M', rM, hM'⟩ := hRes k Ω N x pp hpr hhom hle j hj hjp _ ψ hker hxy T.M
  have hRM : RestrictData T.M.toSubSystem hxy M'.toSubSystem rM :=
    ⟨fun I => (hM' I).1, fun I => (hM' I).2.1, fun I => (hM' I).2.2.1, fun I => (hM' I).2.2.2⟩
  have hnef : Nef M'.toSubSystem := hNR k Ω N x _ _ hxy hxy' T.M M' rM hRM T.nef

  have hts : 0 < T.t - T.s' := by
    have hd : (1 : ℚ) ≤ (T.d : ℚ) + 1 := by
      have := (Nat.cast_nonneg T.d : (0 : ℚ) ≤ T.d); linarith
    have ht : 0 < T.t := by
      by_contra hneg'
      have hneg : T.t ≤ 0 := not_lt.mp hneg'
      have : T.t / ((T.d : ℚ) + 1) ≤ 0 := div_nonpos_of_nonpos_of_nonneg hneg (by positivity)
      linarith [T.s'_pos, T.s'_lt]
    have : T.t / ((T.d : ℚ) + 1) ≤ T.t := div_le_self ht.le hd
    linarith [T.s'_lt]
  obtain ⟨q, m', hq, hm', hva⟩ := hK e he _ N _ M' hsubW hnef (T.t - T.s') hts
  obtain ⟨rr, h, hvb⟩ := hva
  have hqm : (q : ℤ) * T.m = T.p * m' := by
    have : (((q : ℤ) * T.m : ℤ) : ℚ) = ((T.p * m' : ℤ) : ℚ) := by
      push_cast; rw [T.m_eq, hm']; ring
    exact_mod_cast this

  obtain ⟨B, hB⟩ := exists_lineBundle_twistMulOf hLT M' q m'
  obtain ⟨L', hL'⟩ := exists_lineBundle_twistMulOf hLT M' T.p T.m
  have hv : ∀ b₂ : ℕ, ∃ c₀ : ℤ, ∀ (b' : ℕ) (c : ℤ), c₀ ≤ c →
      Subsingleton (((((twistMul M'.toSubSystem T.p T.m).pow b₂).twist
        ((twistMul M'.toSubSystem q m').pow b')).twist (twistSys k (fun i => ψ (ratio hj i)) c)).H 1) := by
    intro b₂
    obtain ⟨G, hG⟩ := exists_lineBundle_pow hLT L' b₂
    obtain ⟨c₀, hc₀⟩ := hTV k _ N _ G B rr h (fun l => by rw [hB]; exact hvb.mem_secs l)
      (fun I => by rw [hB]; exact hvb.generates I)
    refine ⟨c₀, fun b' c hc => ?_⟩
    have hs := hc₀ b' c hc
    rwa [hG, hL', hB] at hs
  choose cv hcv using hv
  refine ⟨∑ b₂ ∈ Finset.range q, |cv b₂|, fun b Q hQ c hc => ?_⟩
  obtain ⟨Qb, Qb', r', hQb, hQb', hrd⟩ :=
    exists_restrict_twistMul_pow hLT hRT hxy hxy' T.M M' rM hRM T.p T.m b
  obtain ⟨eqv⟩ := hRQ k Ω N x pp hpr hhom hle j hj hjp _ ψ hker hxy Qb Qb' r' hrd c 1
  have hQbQ : Qb.toSubSystem = Q.toSubSystem := by rw [hQb, hQ]; rfl
  have hW : Qb'.toSubSystem = ((twistMul M'.toSubSystem T.p T.m).pow (b % q)).twist
      ((twistMul M'.toSubSystem q m').pow (T.p * (b / q))) := by
    rw [hQb', ← hTA k _ N _ M'.toSubSystem T.p q T.m m' (b / q) (b % q) hqm, Nat.div_add_mod b q]
  have hlt : b % q < q := Nat.mod_lt b (by omega)
  have hcb : cv (b % q) ≤ c :=
    le_trans (le_abs_self _) (le_trans (Finset.single_le_sum (f := fun b₂ => |cv b₂|)
      (fun _ _ => abs_nonneg _) (Finset.mem_range.mpr hlt)) hc)
  have hs : Subsingleton ((Qb'.twist (twistSys k (fun i => ψ (ratio hj i)) c)).H 1) := by
    rw [hW]; exact hcv (b % q) (T.p * (b / q)) c hcb
  rw [← hQbQ]
  exact @Equiv.subsingleton _ _ eqv.toEquiv hs

end OnW

theorem StepTwo.proof (hRed : StepTwo.Reduce.Statement.{u, v, w}) (hLT : LineTwist.Statement.{u, w})
    (hTA : TwistAlg.Statement.{u, w}) (hRT : RestrictTwist.Statement.{u, w})
    (hNR : NefRestrict.Statement.{u, w}) (hJP : StepData.JProper.Statement.{u, w})
    (hDrop : SubvarDrop.Statement.{u, w}) (hPt : PrimeFiltration.Point.Statement.{u, w})
    (hRes : PrimeFiltration.Restrict.Statement.{u, w})
    (hRQ : PrimeFiltration.RestrictQuot.Statement.{u, w}) (hTV : TwistVanish.Statement.{u, w}) :
    StepTwo.Statement.{u, v, w} := by
  intro k _ Ω _ _ N x T hK E _ _ _ _ M₁ M₂ hle hJ
  obtain ⟨n, pr, sh, hpr, hred⟩ := hRed k Ω N x E M₁ M₂ hle T.J hJ
  have hLpow : ∀ b : ℕ, ∃ Q : LineBundle k x, Q.toSubSystem = T.L.pow b := fun b => by
    obtain ⟨L, hL⟩ := exists_lineBundle_twistMulOf hLT T.M T.p T.m
    obtain ⟨Q, hQ⟩ := exists_lineBundle_pow hLT L b
    exact ⟨Q, by rw [hQ, hL]; rfl⟩
  choose Qb hQb using hLpow
  have hW : ∀ i, ∃ c₁ : ℤ, (∃ j, (X j : Poly k N) ∉ pr i) → ∀ (b : ℕ) (c : ℤ), c₁ ≤ c →
      Subsingleton (SubSystem.quotH ((Qb b).twist (twistSys k x c))
        (((Qb b).twist (twistSys k x c)).twist (idealSys x (pr i))) 1) := by
    intro i
    by_cases hrel : ∃ j, (X j : Poly k N) ∉ pr i
    · obtain ⟨c₁, hc₁⟩ := StepTwo.onW hLT hTA hRT hNR hJP hDrop hPt hRes hRQ hTV T hK (pr i)
        (hpr i).1 (hpr i).2.1 (hpr i).2.2.1 (hpr i).2.2.2 hrel
      exact ⟨c₁, fun _ b c hc => hc₁ b (Qb b) (hQb b) c hc⟩
    · exact ⟨0, fun h => absurd h hrel⟩
  choose cw hcw using hW
  refine ⟨∑ i, |cw i - sh i|, fun b c hc => ?_⟩
  have hs := hred (Qb b) c (fun i hi => hcw i hi b (c + sh i) (by
    have h1 : |cw i - sh i| ≤ ∑ i, |cw i - sh i| :=
      Finset.single_le_sum (f := fun i => |cw i - sh i|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
    have h2 := le_abs_self (cw i - sh i)
    linarith))
  rwa [hQb b] at hs

end

end PositivityTheory.HtPt.KtwS
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.FlagbLoc
section
noncomputable section

namespace PositivityTheory.HtPt.Flagb

open AlgebraicGeometry CategoryTheory NumberField GlobalTheory.CompanionTheory.Ar

variable {Ω L : Type} [Field Ω] [AddCommGroup L] [Module Ω L]

theorem exists_lead {r : ℕ} (b₀ b : Fin r → L) (hF : ∀ i, flagStep Ω b i = flagStep Ω b₀ i) (i : Fin r) :
    ∃ τ : Ω, b i - τ • b₀ i ∈ flagStep Ω b₀ i := by
  have h1 : b i ∈ flagStep Ω b₀ (i + 1) := by
    rw [← hF]; exact Submodule.subset_span ⟨i, by simp, rfl⟩
  have h2 : b₀ '' {k | (k : ℕ) < i + 1} = insert (b₀ i) (b₀ '' {k | (k : ℕ) < i}) := by
    rw [← Set.image_insert_eq]
    congr 1
    ext k
    simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Fin.ext_iff]
    omega
  unfold flagStep at h1
  rw [h2, Submodule.mem_span_insert] at h1
  obtain ⟨a, z, hz, h⟩ := h1
  exact ⟨a, by rw [h, add_sub_cancel_left]; exact hz⟩

theorem div_mem_of_span (R : Subring Ω) {a c : Ω} (h : a ∈ Submodule.span R {c}) : a / c ∈ R := by
  obtain ⟨u, rfl⟩ := Submodule.mem_span_singleton.1 h
  by_cases hc : c = 0
  · simp [hc]
  · show (u : Ω) * c / c ∈ R
    rw [mul_div_cancel_right₀ _ hc]; exact u.2

theorem tens_gen {X : Scheme.{0}} {ξ : Spec (CommRingCat.of Ω) ⟶ X} (Λ : Lat ξ Ω) (q : Cpt ξ) (ε : ℤ)
    (hε : ε = 1 ∨ ε = -1) (τ c : Ω) (h : Λ.IsGenAt q τ)
    (hc : Lat.tens (fun _ : Unit => Λ) (fun _ => ε) q = Submodule.span (regAt ξ q) {c}) :
    τ ^ ε / c ∈ regAt ξ q ∧ c / τ ^ ε ∈ regAt ξ q := by
  constructor
  · refine div_mem_of_span _ ?_
    rw [← hc]
    exact Submodule.subset_span ⟨fun _ => τ, fun _ => h, by simp⟩
  · refine div_mem_of_span _ ?_
    have : Lat.tens (fun _ : Unit => Λ) (fun _ => ε) q ≤ Submodule.span (regAt ξ q) {τ ^ ε} := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨s, hs, rfl⟩
      replace hs : ∀ i, Λ.IsGenAt q (s i) := hs
      have h1 : s () / τ ∈ regAt ξ q := div_mem_of_span _ (by
        rw [← h.2, (hs ()).2]; exact Submodule.mem_span_singleton_self _)
      have h2 : τ / s () ∈ regAt ξ q := div_mem_of_span _ (by
        rw [← (hs ()).2, h.2]; exact Submodule.mem_span_singleton_self _)
      have h3 := h.1
      have h4 := (hs ()).1
      rcases hε with rfl | rfl
      · refine Submodule.mem_span_singleton.2 ⟨⟨_, h1⟩, ?_⟩
        show s () / τ * τ ^ (1 : ℤ) = _
        simp [h3]
      · refine Submodule.mem_span_singleton.2 ⟨⟨_, h2⟩, ?_⟩
        show τ / s () * τ ^ (-1 : ℤ) = _
        simp
        field_simp
    exact this (hc ▸ Submodule.mem_span_singleton_self _)

theorem mem_span_of_dual {V : Type} [AddCommGroup V] [Module Ω V] [FiniteDimensional Ω V] (R : Subring Ω) {r : ℕ}
    (f : Fin r → Module.Dual Ω V) (hf : LinearIndependent Ω f) (hs : Submodule.span Ω (Set.range f) = ⊤)
    (u : Module.Dual Ω V) (hu : ∀ e : V, (∀ j, f j e ∈ R) → u e ∈ R) : u ∈ Submodule.span R (Set.range f) := by
  classical
  let B : Module.Basis (Fin r) Ω (Module.Dual Ω V) := Module.Basis.mk hf hs.ge
  have hB : ∀ j, B j = f j := fun j => Module.Basis.mk_apply _ _ j
  have h1 : ∀ j, B.repr u j ∈ R := by
    intro j
    have h2 : ∀ w : Module.Dual Ω V, w ((Module.evalEquiv Ω V).symm (B.coord j)) = B.repr w j := fun w => by
      rw [Module.apply_evalEquiv_symm_apply]; rfl
    rw [← h2]
    refine hu _ fun i => ?_
    rw [h2, ← hB, B.repr_self, Finsupp.single_apply]
    split_ifs
    · exact R.one_mem
    · exact R.zero_mem
  rw [← B.sum_repr u]
  refine Submodule.sum_mem _ fun j _ => ?_
  exact Submodule.smul_mem (Submodule.span R (Set.range f)) (⟨_, h1 j⟩ : R) (Submodule.subset_span ⟨j, (hB j).symm⟩)

theorem apply_mem_of_span (R : Subring Ω) (w : Module.Dual Ω L) (s : Set L) (h : ∀ x ∈ s, w x ∈ R) (e : L)
    (he : e ∈ Submodule.span R s) : w e ∈ R := by
  induction he using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => rw [map_zero]; exact R.zero_mem
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx =>
    have : w (c • x) = (c : Ω) * w x := map_smul w (c : Ω) x
    rw [this]; exact mul_mem c.2 hx

theorem exists_nat_diff {E : Type} [Field E] [NumberField E] (x : E) :
    ∃ n : ℕ, n ≠ 0 ∧ ∃ δ ∈ differentIdeal ℤ (𝓞 E), (δ : E) = n * x := by
  obtain ⟨y, hy, hi⟩ := (show IsAlgebraic ℤ x from
    (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic x)).exists_integral_multiple
  obtain ⟨z, hz⟩ : ∃ z : 𝓞 E, algebraMap (𝓞 E) E z = y * x := ⟨⟨y • x, hi⟩, by rw [← zsmul_eq_mul]; rfl⟩
  have hN := Ideal.absNorm_mem (differentIdeal ℤ (𝓞 E))
  have hN0 : Ideal.absNorm (differentIdeal ℤ (𝓞 E)) ≠ 0 := fun h =>
    differentIdeal_ne_bot (A := ℤ) (B := 𝓞 E) (Ideal.absNorm_eq_zero_iff.1 h)
  refine ⟨Ideal.absNorm (differentIdeal ℤ (𝓞 E)) * y.natAbs ^ 2, mul_ne_zero hN0 (pow_ne_zero _ (by simpa using hy)),
    _, Ideal.mul_mem_right ((y : 𝓞 E) * z) _ hN, ?_⟩
  have : ((y.natAbs ^ 2 : ℕ) : E) = (y : E) * y := by
    rw [← Int.cast_natCast, Nat.cast_pow, Int.natAbs_sq, Int.cast_pow, sq]
  rw [Nat.cast_mul, this]
  simp only [map_mul, map_natCast, map_intCast]
  rw [hz]; ring

end PositivityTheory.HtPt.Flagb
end
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.GaSurj
section
noncomputable section

namespace PositivityTheory.HtPt.Ga

open Module NumberField GlobalTheory.CompanionTheory.Ar.HT TensorProduct

section

variable {A K : Type} [CommRing A] [Field K] [Algebra A K] {E : Type} [Field E] [NumberField E]
  {c : E ≃+* E} {p R N : ℕ}
  {Ω : Type} [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω]
  (D : HTChart A K c p R N Ω)

theorem h_mem_om' (x : Fin N → 𝓞 E) : D.h x ∈ D.om' :=
  Submodule.mem_sup_left (Submodule.subset_span ⟨x, rfl⟩)

theorem proj_mem_omHT (σ : E →+* K) {y : Ω} (hy : y ∈ D.om') : eigProj D.ρΩ σ y ∈ D.omHT σ :=
  ⟨y, hy, rfl⟩

theorem q_mem (σ : E →+* K) (x : Fin N → A) : D.q σ x ∈ D.omHT σ := by
  unfold HTChart.q
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
  exact proj_mem_omHT D σ (h_mem_om' D _)

theorem q_add (σ : E →+* K) (x y : Fin N → A) : D.q σ (x + y) = D.q σ x + D.q σ y := by
  unfold HTChart.q
  simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]

theorem q_smul (σ : E →+* K) (a : A) (x : Fin N → A) : D.q σ (a • x) = a • D.q σ x := by
  unfold HTChart.q
  simp only [Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]

private theorem toZMod_cycZ_eq_one_of_cycMod_eq_one (σ : E →+* K) (hσ : ∀ a : 𝓞 E, σ (a : E) ∈ (algebraMap A K).range)
    (z : Fin N → 𝓞 E) :
    ∃ x : Fin N → A, ∃ y' ∈ D.om, eigProj D.ρΩ σ (D.h z) = D.q σ x + ((p : A) ^ R) • eigProj D.ρΩ σ y' := by
  choose y hy he using fun i => D.h_lin (z i) (Pi.single i 1)
  choose b hb using fun i => hσ (z i)
  have hz : z = ∑ i, z i • Pi.single i (1 : 𝓞 E) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  have hrho : ∀ (a : 𝓞 E) (v : Ω), eigProj D.ρΩ σ (D.ρΩ a v) = σ (a : E) • eigProj D.ρΩ σ v := by
    intro a v
    have h1 := congrArg (fun f : Module.End K Ω => f v) (ProjEig.eigProj_mul_rho_comm D.ρΩ σ a)
    have h2 := congrArg (fun f : Module.End K Ω => f v) (ProjEig.rho_mul_eigProj D.ρΩ σ a)
    simp only [Module.End.mul_apply, LinearMap.smul_apply] at h1 h2
    rw [h1, h2]
  refine ⟨b, ∑ i, y i, Submodule.sum_mem _ fun i _ => hy i, ?_⟩
  conv_lhs => rw [hz]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum]
  simp only [he, map_add (f := _), hrho, ← hb, algebraMap_smul]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Finset.sum_add_distrib, map_sum, Finset.smul_sum]
  unfold HTChart.q
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_nsmul, ← Nat.cast_smul_eq_nsmul A]
  push_cast
  rfl

theorem exists_q_add (σ : E →+* K) (hσ : ∀ a : 𝓞 E, σ (a : E) ∈ (algebraMap A K).range)
    {y : Ω} (hy : y ∈ D.om') :
    ∃ x : Fin N → A, ∃ y' ∈ D.om, eigProj D.ρΩ σ y = D.q σ x + ((p : A) ^ R) • eigProj D.ρΩ σ y' := by
  obtain ⟨s, hs, t, ht, rfl⟩ := Submodule.mem_sup.mp hy
  obtain ⟨y0, hy0, rfl⟩ := Submodule.mem_map.mp ht
  clear hy ht
  have key : ∃ x : Fin N → A, ∃ y' ∈ D.om,
      eigProj D.ρΩ σ s = D.q σ x + ((p : A) ^ R) • eigProj D.ρΩ σ y' := by
    induction hs using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨z, rfl⟩ := hv
      exact toZMod_cycZ_eq_one_of_cycMod_eq_one D σ hσ z
    | zero => exact ⟨0, 0, D.om.zero_mem, by simp [HTChart.q]⟩
    | add u v _ _ hu hv =>
      obtain ⟨x1, y1, hy1, e1⟩ := hu
      obtain ⟨x2, y2, hy2, e2⟩ := hv
      refine ⟨x1 + x2, y1 + y2, D.om.add_mem hy1 hy2, ?_⟩
      rw [map_add (f := _), e1, e2, q_add, map_add (f := _), smul_add]
      abel
    | smul a v _ hv =>
      obtain ⟨x1, y1, hy1, e1⟩ := hv
      refine ⟨a • x1, a • y1, D.om.smul_mem a hy1, ?_⟩
      rw [LinearMap.map_smul_of_tower, e1, q_smul, LinearMap.map_smul_of_tower, smul_add, smul_comm a]
  obtain ⟨x, y', hy', e⟩ := key
  have ht0 : eigProj D.ρΩ σ (((p : A) ^ R • LinearMap.id : Ω →ₗ[A] Ω) y0)
      = ((p : A) ^ R) • eigProj D.ρΩ σ y0 := by
    simp [LinearMap.map_smul_of_tower]
  refine ⟨x, y' + y0, D.om.add_mem hy' hy0, ?_⟩
  rw [map_add (f := _), e, ht0, map_add (f := _), smul_add, add_assoc]

end

theorem q_surj : ∀ (A K : Type) [CommRing A] [Field K] [Algebra A K] [CharZero K] (hAK : Function.Injective (algebraMap A K)) (E : Type) [Field E] [NumberField E] (c : E ≃+* E) (hc : ∀ x, c (c x) = x) (p R N : ℕ) [Fact p.Prime] (Ω : Type) [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω] (D : HTChart A K c p R N Ω) (κ : A) (σ : E →+* K) (m : ℕ), (∀ a : 𝓞 E, σ (a : E) ∈ (algebraMap A K).range) → κ * (p : A) ^ m ∣ (p : A) ^ R → (∀ x ∈ D.om, κ • x ∈ D.om') → (∀ x, D.q σ x ∈ D.omHT σ) ∧ (D.omHT σ).FG ∧ ∀ y ∈ D.omHT σ, ∃ x : Fin N → A, ∃ y' ∈ D.omHT σ, y = D.q σ x + ((p : A) ^ m) • y' := by
  intro A K _ _ _ _ hAK E _ _ c hc p R N _ Ω _ _ _ _ D κ σ m hσ hdiv hκ
  classical
  refine ⟨fun x => q_mem D σ x, ?_, ?_⟩
  · unfold HTChart.omHT eigQuot
    apply Submodule.FG.map
    unfold HTChart.om'
    refine Submodule.FG.sup ?_ (Submodule.FG.map _ D.om_lat.fg)
    obtain ⟨T, hT⟩ := (Module.Finite.fg_top : (⊤ : Submodule ℤ (Fin N → 𝓞 E)).FG)
    refine ⟨T.image D.h, le_antisymm ?_ ?_⟩
    · apply Submodule.span_mono
      intro v hv
      simp only [Finset.coe_image, Set.mem_image] at hv
      obtain ⟨z, _, rfl⟩ := hv
      exact ⟨z, rfl⟩
    · rw [Submodule.span_le]
      rintro _ ⟨z, rfl⟩
      have hz : z ∈ Submodule.span ℤ (T : Set (Fin N → 𝓞 E)) := hT ▸ Submodule.mem_top
      induction hz using Submodule.span_induction with
      | mem w hw =>
        exact Submodule.subset_span (by simp only [Finset.coe_image]; exact ⟨w, hw, rfl⟩)
      | zero => simp
      | add u v _ _ hu hv =>
        rw [map_add (f := _)]
        exact Submodule.add_mem _ hu hv
      | smul n u _ hu =>
        rw [map_zsmul]
        exact zsmul_mem hu n
  · intro y hy
    simp only [HTChart.omHT, eigQuot] at hy
    obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp hy
    obtain ⟨x, y'', hy'', e⟩ := exists_q_add D σ hσ hw
    obtain ⟨d, hd⟩ := hdiv
    refine ⟨x, d • eigProj D.ρΩ σ (κ • y''), ?_, ?_⟩
    · exact Submodule.smul_mem _ d (proj_mem_omHT D σ (hκ y'' hy''))
    · rw [LinearMap.restrictScalars_apply, e, hd, LinearMap.map_smul_of_tower]
      congr 1
      simp only [smul_smul]
      congr 1
      ring

end PositivityTheory.HtPt.Ga
end
end

