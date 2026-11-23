module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.Bundle0017
public import Development.WeilBound.CoreStatements.AutomorphicKernels.DepthZeroCuspidal.WhittakerSupportTildeOf

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.FinsumInvT
section
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG
open UpperTheory.Gal.CertificateRingHomMap (GUf Plc comp lev GLw IsCen mat sim)
open UpperTheory.Gal.W2.Seed UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Pl UpperTheory.Gal.Spc
open scoped TensorProduct Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open GlobalTheory.LFun (KGL satEig heckeVec IsSatVecGL)

namespace UpperTheory.Gal.W2.Seed

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {w : Plc E}

private theorem tj_eq {ϖ : w.adicCompletion E} {i : ℕ} (t : GLw n w)
    (ht : t.val = Matrix.diagonal fun k : Fin n => if (k : ℕ) < i then ϖ else 1) :
    Tj ℂ n (Ov E w) ϖ i = dosetInd ℂ (KGL w (n := n)) t := by
  unfold Tj dosetInd
  congr 1
  ext y
  rw [Set.mem_setOf_eq, DoubleCoset.mem_doubleCoset]
  constructor
  · rintro ⟨a, ha, b, hb, e⟩
    refine ⟨a, ha, b, hb, Units.ext ?_⟩
    rw [e, Units.val_mul, Units.val_mul, ht]
    rfl
  · rintro ⟨a, ha, b, hb, rfl⟩
    refine ⟨a, ha, b, hb, ?_⟩
    rw [Units.val_mul, Units.val_mul, ht]
    rfl

private theorem dos_invT (t : GLw n w) (h : invT n _ t⁻¹ = t) (a : GLw n w) :
    dosetInd ℂ (KGL w (n := n)) t (invT n _ a) = dosetInd ℂ (KGL w (n := n)) t⁻¹ a := by
  have h' : invT n _ t = t⁻¹ := by
    have := congrArg (invT n _) h
    rw [UpperTheory.Gal.CertificateRingHomMap.invT_invT'] at this
    exact this.symm
  have key : invT n _ a ∈ DoubleCoset.doubleCoset t (KGL w (n := n) : Set (GLw n w)) (KGL w (n := n)) ↔
      a ∈ DoubleCoset.doubleCoset t⁻¹ (KGL w (n := n) : Set (GLw n w)) (KGL w (n := n)) := by
    rw [DoubleCoset.mem_doubleCoset, DoubleCoset.mem_doubleCoset]
    constructor
    · rintro ⟨k, hk, l, hl, e⟩
      refine ⟨_, UpperTheory.Gal.CertificateRingHomMap.invT_mem_KGL hk, _, UpperTheory.Gal.CertificateRingHomMap.invT_mem_KGL hl, ?_⟩
      have := congrArg (invT n _) e
      rwa [UpperTheory.Gal.CertificateRingHomMap.invT_invT', map_mul, map_mul, h'] at this
    · rintro ⟨k, hk, l, hl, rfl⟩
      exact ⟨_, UpperTheory.Gal.CertificateRingHomMap.invT_mem_KGL hk, _, UpperTheory.Gal.CertificateRingHomMap.invT_mem_KGL hl, by rw [map_mul, map_mul, h]⟩
  unfold dosetInd
  by_cases hm : a ∈ DoubleCoset.doubleCoset t⁻¹ (KGL w (n := n) : Set (GLw n w)) (KGL w (n := n))
  · rw [Set.indicator_of_mem hm, Set.indicator_of_mem (key.2 hm)]; rfl
  · rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem (fun h => hm (key.1 h))]

private theorem dos_mul (t a k : GLw n w) (hk : k ∈ KGL w (n := n)) :
    dosetInd ℂ (KGL w (n := n)) t (a * k) = dosetInd ℂ (KGL w (n := n)) t a := by
  have key : a * k ∈ DoubleCoset.doubleCoset t (KGL w (n := n) : Set (GLw n w)) (KGL w (n := n)) ↔
      a ∈ DoubleCoset.doubleCoset t (KGL w (n := n) : Set (GLw n w)) (KGL w (n := n)) := by
    rw [DoubleCoset.mem_doubleCoset, DoubleCoset.mem_doubleCoset]
    constructor
    · rintro ⟨u, hu, l, hl, e⟩
      exact ⟨u, hu, l * k⁻¹, (KGL w (n := n)).mul_mem hl ((KGL w (n := n)).inv_mem hk), by
        rw [← mul_assoc, ← e, mul_inv_cancel_right]⟩
    · rintro ⟨u, hu, l, hl, rfl⟩
      exact ⟨u, hu, l * k, (KGL w (n := n)).mul_mem hl hk, by simp only [mul_assoc]⟩
  unfold dosetInd
  by_cases hm : a ∈ DoubleCoset.doubleCoset t (KGL w (n := n) : Set (GLw n w)) (KGL w (n := n))
  · rw [Set.indicator_of_mem hm, Set.indicator_of_mem (key.2 hm)]; rfl
  · rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem (fun h => hm (key.1 h))]

private theorem finsum_invT {M : Type} [AddCommMonoid M] (F : GLw n w → M)
    (hF : ∀ a, ∀ k ∈ KGL w (n := n), F (a * k) = F a) :
    ∑ᶠ c : GLw n w ⧸ KGL w (n := n), F (invT n _ c.out) = ∑ᶠ c : GLw n w ⧸ KGL w (n := n), F c.out := by
  let f : GLw n w ⧸ KGL w (n := n) → GLw n w ⧸ KGL w (n := n) := fun c => QuotientGroup.mk (invT n _ c.out)
  have hf : Function.Involutive f := fun c => by
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (KGL w (n := n)) (invT n _ c.out)
    simp only [f]
    rw [hk, map_mul, UpperTheory.Gal.CertificateRingHomMap.invT_invT', QuotientGroup.mk_mul_of_mem _ (UpperTheory.Gal.CertificateRingHomMap.invT_mem_KGL k.2),
      QuotientGroup.out_eq']
  have hshift : ∀ c, F (invT n _ c.out) = F ((Function.Involutive.toPerm f hf c).out) := fun c => by
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (KGL w (n := n)) (invT n _ c.out)
    rw [Function.Involutive.coe_toPerm]
    simp only [f]
    rw [hk, hF _ _ k.2]
  rw [finsum_congr hshift]
  exact finsum_comp_equiv (Function.Involutive.toPerm f hf) (f := fun c => F c.out)

end UpperTheory.Gal.W2.Seed

theorem UpperTheory.Gal.W2.Seed.tEig_of_thLoc :
    UpperTheory.Gal.CertificateRingHomMap.ThLoc → TEig := by
  intro hT E _ _ _ n hn x U w₀ Up V w hw hF i hi t ht z hz B hB g
  obtain ⟨-, s2, -, s4⟩ := V.form.sat w hw hF.2.1 hF.2.2.1 B hB
  obtain ⟨ϖ, hϖ, htd⟩ := ht
  obtain ⟨hT1, hT2⟩ := hT E n
  have hcen := V.kap.cen w hF.2.2.2.1 hF.2.2.2.2 z hz
  have hpow : ∀ (j : ℕ) (G : GUf E n), V.Φ (G * z ^ j) = (((V.κ.val w : ℂˣ) : ℂ)⁻¹ ^ j) • V.Φ G := by
    intro j
    induction j with
    | zero => intro G; simp
    | succ j ih =>
      intro G
      rw [pow_succ, ← mul_assoc, hcen, ih, smul_smul, pow_succ, mul_comm]
  have hinv : invT n _ t⁻¹ = t := by
    apply Units.ext
    rw [UpperTheory.Gal.CertificateRingHomMap.invT_val, inv_inv, htd, Matrix.diagonal_transpose]
  set G' : GUf E n := UpperTheory.Gal.CertificateRingHomMap.th g * z ^ i with hG'
  let Fn : GLw n w → Module.Dual ℂ V.W.Sp := fun a => dosetInd ℂ (KGL w (n := n)) t a • V.Φ (G' * UpperTheory.Gal.CertificateRingHomMap.loc hw a)
  have hFn : ∀ a, ∀ k ∈ KGL w (n := n), Fn (a * k) = Fn a := fun a k hk => by
    have h1 : V.Φ (G' * UpperTheory.Gal.CertificateRingHomMap.loc hw a * UpperTheory.Gal.CertificateRingHomMap.loc hw k) = V.Φ (G' * UpperTheory.Gal.CertificateRingHomMap.loc hw a) :=
      congrFun (GlobalTheory.LGrp.mem_fixed.1 s2 k hk) _
    simp only [Fn]
    rw [UpperTheory.Gal.W2.Seed.dos_mul _ _ _ hk, map_mul, ← mul_assoc, h1]
  have hterm : ∀ c : GLw n w ⧸ KGL w (n := n), dosetInd ℂ (KGL w (n := n)) t⁻¹ c.out •
      V.Φ (UpperTheory.Gal.CertificateRingHomMap.th (g * (z ^ i)⁻¹ * UpperTheory.Gal.CertificateRingHomMap.loc hw c.out)) = Fn (invT n _ c.out) := fun c => by
    simp only [Fn]
    rw [UpperTheory.Gal.W2.Seed.dos_invT t hinv, map_mul, map_mul, hT1, map_inv, map_pow, hT2 hn x w z hz, inv_pow, inv_inv]
  have hev := congrFun (s4 ϖ hϖ i hi) G'
  unfold heckeVec at hev
  rw [finsum_apply (GlobalTheory.LFun.finite_heckeVec (Final.GLintComm E w n) (GlobalTheory.LFun.Tj_mem_hecke hϖ i) _ V.Φ),
    UpperTheory.Gal.W2.Seed.tj_eq t htd] at hev
  rw [finsum_congr hterm, UpperTheory.Gal.W2.Seed.finsum_invT Fn hFn]
  refine Eq.trans hev ?_
  rw [Pi.smul_apply, hG', hpow, smul_smul]
  rfl
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PActsConv
section
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG
open UpperTheory.Gal.CertificateRingHomMap (GUf Plc comp lev GLw IsCen mat sim)
open UpperTheory.Gal.W2.Seed UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Pl UpperTheory.Gal.Spc
open scoped TensorProduct Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem conv_eq_hAct {X : Type} [Group X] (K : Subgroup X) (f f' : X → ℂ) (g : X) :
    conv K f f' g = hAct K f (fun x => f' (x⁻¹ * g)) 1 := by
  simp only [conv, hAct, one_mul, smul_eq_mul]

private theorem conv_tf {X M : Type} [Group X] [Group M] (hA : TfAdm) (T : TyLev X M) (ψ : X → ℂ) (c : ℂ) (h h' : X)
    (hψ : T.Acts ψ c h) (hh' : T.L.pr h' = 1) :
    conv T.K₀ ψ (T.tf h') = c • conv T.K₀ (T.tf h) (T.tf h') := by
  funext g
  have hΦ : T.IsTy (fun x => T.tf h' (x⁻¹ * g)) := by
    intro k hk x
    have hk' : k⁻¹ ∈ T.K := T.K.inv_mem hk
    simp only [_root_.mul_inv_rev, mul_assoc]
    rw [((hA X M T h' hh').2 k⁻¹ hk' (x⁻¹ * g)).1, smul_eq_mul]
    congr 1
    have e : ∀ (p1 : T.L.pr k⁻¹ ∈ T.J) (p2 : T.L.pr k ∈ T.J),
        (⟨T.L.pr k⁻¹, p1⟩ : T.J) = (⟨T.L.pr k, p2⟩ : T.J)⁻¹ := fun p1 p2 =>
      Subtype.ext (map_inv _ _)
    rw [e _ (T.fact.2 k hk)]
    simp
  have key := congrFun (hψ.2.2 ℂ _ hΦ) 1
  rw [Pi.smul_apply, conv_eq_hAct, conv_eq_hAct, key, Pi.smul_apply]

theorem UpperTheory.Gal.W2.Seed.pActsConv :
    TfAdm → TfIdem → ActsConv := by
  intro hA hI X M _ _ T ψ c h hψ
  constructor
  · rw [conv_tf hA T ψ c h 1 hψ (map_one _), (hI X M T h hψ.2.1).2.1]
  · intro c' h' hh'
    have hlin : ∀ f : X → ℂ, conv T.K₀ ψ (c' • f) = c' • conv T.K₀ ψ f := by
      intro f
      funext g
      rw [Pi.smul_apply]
      unfold conv
      rw [smul_finsum]
      congr 1
      funext i
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    rw [hlin, conv_tf hA T ψ c h h' hψ hh', smul_smul, mul_comm c' c]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PCenFacts
section
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG
open UpperTheory.Gal.CertificateRingHomMap (GUf Plc comp lev GLw IsCen mat sim)
open UpperTheory.Gal.W2.Seed UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Pl UpperTheory.Gal.Spc
open scoped TensorProduct Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Gal.W2.Seed.pCenFacts :
    Sides → CenFacts := by
  intro hS E _ _ _ A n _ x hx q hq hsp w hw z hz
  obtain ⟨-, -, -, h4, -⟩ := hS E A x hx q hq hsp w hw
  have hscal : ∀ (u : Plc E) (a : GL (Fin n) (u.adicCompletion E)), comp u z * a = a * comp u z := by
    intro u a
    by_cases h : UpperTheory.Gal.CertificateRingHomMap.SameK x (UpperTheory.Gal.CertificateRingHomMap.cj u) w
    · apply Units.ext
      rw [Units.val_mul, Units.val_mul, (hz u).1 h, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
    · rw [(hz u).2 h, one_mul, mul_one]
  refine ⟨fun g => UpperTheory.Gal.CertificateRingHomMap.guf_ext ?_ fun u => ?_, fun u hu => ?_⟩
  · rw [map_mul, map_mul, mul_comm]
  · rw [map_mul, map_mul, hscal]
  · refine (hz u).2 fun h => hu ?_
    have h' := h4 _ h
    have e : (UpperTheory.Gal.CertificateRingHomMap.cj u).asIdeal = _ :=
      (GlobalTheory.Mem.Chr.conjPl_iff_comap _ _ _).1 (conjPl_conjSrc (GlobalTheory.SplitPts.conjE E) u)
    rw [e, Ideal.mem_comap, map_natCast] at h'
    exact h'
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PCongConj
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU UpperTheory.Gal.CertificateRingHomMap UpperTheory.Gal.W2.Seed
open scoped Classical

private theorem comp_rel {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (k : GUf E n) (u : Plc E) :
    ((comp (cj u) k).val.map (conjLoc (GlobalTheory.SplitPts.conjE E) u))ᵀ * (comp u k).val =
      pLoc E u (GroundTheory.Global.AdeleBaseChange.finiteAdeleMap ℚ E ((sim k : AfQˣ) : AfQ)) •
        (1 : Matrix (Fin n) (Fin n) (u.adicCompletion E)) := by
  have h := congrArg (RingHom.mapMatrix (pLoc E u)) (mem_Sim.1 k.2)
  rw [map_mul] at h
  refine Eq.trans ?_ (h.trans ?_)
  · rfl
  · ext i j
    by_cases hij : i = j <;> simp [hij, Matrix.one_apply, sim]

theorem UpperTheory.Gal.W2.Seed.pCongConj :
    UpperTheory.Gal.CertificateRingHomMap.LocComm → CongConj := by
  intro _ E _ _ _ n N w g hs hc i k
  have hrel := comp_rel g w
  rw [hs, Units.val_one, map_one, map_one, one_smul] at hrel
  have hG : ((comp (UpperTheory.Gal.CertificateRingHomMap.cj w) g).val.map (conjLoc (GlobalTheory.SplitPts.conjE E) w))ᵀ = ((comp w g)⁻¹).val := by
    calc ((comp (UpperTheory.Gal.CertificateRingHomMap.cj w) g).val.map (conjLoc (GlobalTheory.SplitPts.conjE E) w))ᵀ
        = ((comp (UpperTheory.Gal.CertificateRingHomMap.cj w) g).val.map (conjLoc (GlobalTheory.SplitPts.conjE E) w))ᵀ * ((comp w g).val * ((comp w g)⁻¹).val) := by
          rw [Units.mul_inv, Matrix.mul_one]
      _ = _ := by rw [← Matrix.mul_assoc, hrel, Matrix.one_mul]
  have hv := (conjLoc_spec (GlobalTheory.SplitPts.conjE E) w).2.2
  have hent : conjLoc (GlobalTheory.SplitPts.conjE E) w (((comp (UpperTheory.Gal.CertificateRingHomMap.cj w) g).val - 1) i k) = (((comp w g)⁻¹).val - 1) k i := by
    rw [← hG]
    by_cases hik : i = k
    · subst hik; simp [Matrix.sub_apply]
    · simp [Matrix.sub_apply, Matrix.one_apply, hik, Ne.symm hik]
  calc Valued.v (((comp (UpperTheory.Gal.CertificateRingHomMap.cj w) g).val - 1) i k)
      = Valued.v (conjLoc (GlobalTheory.SplitPts.conjE E) w (((comp (UpperTheory.Gal.CertificateRingHomMap.cj w) g).val - 1) i k)) := (hv _).symm
    _ = Valued.v ((((comp w g)⁻¹).val - 1) k i) := by rw [hent]
    _ ≤ Valued.v (N : w.adicCompletion E) := hc k i
    _ = Valued.v (conjLoc (GlobalTheory.SplitPts.conjE E) w (N : (UpperTheory.Gal.CertificateRingHomMap.cj w).adicCompletion E)) := by
          rw [map_natCast (conjLoc (GlobalTheory.SplitPts.conjE E) w) N]
    _ = Valued.v (N : (UpperTheory.Gal.CertificateRingHomMap.cj w).adicCompletion E) := hv _
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PCongGrpEx
section
noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG
open GlobalTheory.LFun (KGL satEig)
open GlobalTheory.CongL (SatU)
open GlobalTheory.Cong (Apart)
open UpperTheory.Gal.CertificateRingHomMap (GUf Plc comp lev GLw IsCen mat sim)
open UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Pl UpperTheory.Gal.Spc
open scoped TensorProduct Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Gal.W2.Seed

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

private theorem vN_le_one (N : ℕ) (w : Plc E) : Valued.v (N : w.adicCompletion E) ≤ 1 :=
  (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 E) E w).1 (natCast_mem (w.adicCompletionIntegers E) N)

private theorem vN_ne_zero {N : ℕ} (hN : 0 < N) (w : Plc E) : Valued.v (N : w.adicCompletion E) ≠ 0 := by
  haveI : CharZero (w.adicCompletion E) :=
    charZero_of_injective_algebraMap (algebraMap E (w.adicCompletion E)).injective
  exact (Valuation.ne_zero_iff _).2 (Nat.cast_ne_zero.2 hN.ne')

private theorem vN_lt_one {N : ℕ} (w : Plc E) (h : (N : 𝓞 E) ∈ w.asIdeal) :
    Valued.v (N : w.adicCompletion E) < 1 := by
  have h1 : Valued.v (algebraMap E (w.adicCompletion E) ((N : 𝓞 E) : E)) = w.valuation E ((N : 𝓞 E) : E) :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _
  have h2 : algebraMap E (w.adicCompletion E) ((N : 𝓞 E) : E) = (N : w.adicCompletion E) := by simp
  rw [← h2, h1]
  exact (HeightOneSpectrum.valuation_lt_one_iff_mem w _).2 h

private theorem entry_mul_le {w : Plc E} {A B : Matrix (Fin n) (Fin n) (w.adicCompletion E)}
    {r s : WithZero (Multiplicative ℤ)} (hA : ∀ i j, Valued.v (A i j) ≤ r) (hB : ∀ i j, Valued.v (B i j) ≤ s)
    (i j : Fin n) : Valued.v ((A * B) i j) ≤ r * s := by
  rw [Matrix.mul_apply]
  refine Valuation.map_sum_le _ fun l _ => ?_
  rw [map_mul]
  exact mul_le_mul' (hA _ _) (hB _ _)

private theorem cong_one (N : ℕ) (w : Plc E) : Cong1 N w (1 : GL (Fin n) (w.adicCompletion E)) := fun i k => by
  simp

private theorem cong_mul {N : ℕ} {w : Plc E} {x y : GL (Fin n) (w.adicCompletion E)}
    (hx : Cong1 N w x) (hy : Cong1 N w y) : Cong1 N w (x * y) := fun i k => by
  have e : (x * y).val - 1 = (x.val - 1) * (y.val - 1) + (x.val - 1) + (y.val - 1) := by
    rw [Units.val_mul]; noncomm_ring
  rw [e, Matrix.add_apply, Matrix.add_apply]
  have h := vN_le_one (E := E) N w
  refine Valuation.map_add_le _ (Valuation.map_add_le _ ?_ (hx i k)) (hy i k)
  exact (entry_mul_le hx hy i k).trans (mul_le_of_le_one_left' h)

private theorem cong_conj {N : ℕ} {w : Plc E} {a y : GL (Fin n) (w.adicCompletion E)}
    (ha : a ∈ KGL w (n := n)) (hy : Cong1 N w y) : Cong1 N w (a * y * a⁻¹) := fun i k => by
  have e : (a * y * a⁻¹).val - 1 = a.val * (y.val - 1) * (a⁻¹).val := by
    have h : a.val * (a⁻¹).val = 1 := by rw [← Units.val_mul]; simp
    rw [Units.val_mul, Units.val_mul, mul_sub, sub_mul, mul_one, h]
  obtain ⟨h1, h2⟩ := GlobalTheory.AdelicU.mem_GLint_iff.1 ha
  have h1' : ∀ i j, Valued.v (a.val i j) ≤ 1 := fun i j => (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 E) E w).1 (h1 i j)
  have h2' : ∀ i j, Valued.v ((a⁻¹).val i j) ≤ 1 := fun i j => (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 E) E w).1 (h2 i j)
  rw [e]
  simpa using entry_mul_le (entry_mul_le h1' hy) h2' i k

private theorem cong_entry {N : ℕ} {w : Plc E} {y : GL (Fin n) (w.adicCompletion E)} (hy : Cong1 N w y) (i j : Fin n) :
    Valued.v (y.val i j) ≤ max (Valued.v (N : w.adicCompletion E)) (Valued.v ((1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j)) := by
  have e : y.val i j = (y.val - 1) i j + (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j := by simp
  rw [e]
  exact (Valuation.map_add _ _ _).trans (max_le_max_right _ (hy i j))

private theorem cong_int {N : ℕ} {w : Plc E} {y : GL (Fin n) (w.adicCompletion E)} (hy : Cong1 N w y) (i j : Fin n) :
    y.val i j ∈ w.adicCompletionIntegers E := by
  refine (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 E) E w).2 ((cong_entry hy i j).trans (max_le (vN_le_one N w) ?_))
  by_cases h : i = j
  · subst h; simp
  · rw [Matrix.one_apply_ne h]; simp

private def congGrp (N : ℕ) (w : Plc E) : Subgroup (GL (Fin n) (w.adicCompletion E)) where
  carrier := {y | Cong1 N w y ∧ Cong1 N w y⁻¹}
  one_mem' := ⟨cong_one N w, by simpa using cong_one N w⟩
  mul_mem' := fun {x y} hx hy => ⟨cong_mul hx.1 hy.1, by rw [_root_.mul_inv_rev]; exact cong_mul hy.2 hx.2⟩
  inv_mem' := fun {x} hx => ⟨hx.2, by simpa using hx.1⟩

private theorem isOpen_ball {w : Plc E} {c : w.adicCompletion E} (hc : c ≠ 0) :
    IsOpen {x : w.adicCompletion E | Valued.v x ≤ Valued.v c} := by
  have h0 : IsOpen ((w.adicCompletionIntegers E : Set (w.adicCompletion E))) :=
    Valued.isOpen_valuationSubring _
  have h1 : {x : w.adicCompletion E | Valued.v x ≤ Valued.v c} =
      (fun x => c⁻¹ * x) ⁻¹' (w.adicCompletionIntegers E : Set (w.adicCompletion E)) := by
    ext x
    have hv : Valued.v c ≠ 0 := (Valuation.ne_zero_iff _).2 hc
    simp only [Set.mem_setOf_eq, Set.mem_preimage, SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 E) E w,
      map_mul, map_inv₀]
    rw [inv_mul_le_iff₀ (zero_lt_iff.2 hv), mul_one]
  rw [h1]
  exact h0.preimage (continuous_const.mul continuous_id)

private theorem isOpen_cong {N : ℕ} (hN : 0 < N) (w : Plc E) :
    IsOpen {y : GL (Fin n) (w.adicCompletion E) | Cong1 N w y} := by
  have hc : (N : w.adicCompletion E) ≠ 0 := fun h => vN_ne_zero hN w (by rw [h, map_zero])
  have e : {y : GL (Fin n) (w.adicCompletion E) | Cong1 N w y} =
      ⋂ i, ⋂ k, (fun y : GL (Fin n) (w.adicCompletion E) => (y.val - 1) i k) ⁻¹'
        {x | Valued.v x ≤ Valued.v (N : w.adicCompletion E)} := by
    ext y
    simp [Cong1]
  rw [e]
  refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun k => (isOpen_ball hc).preimage ?_
  exact ((Units.continuous_val.sub continuous_const).matrix_elem i k)

private theorem isOpen_congGrp {N : ℕ} (hN : 0 < N) (w : Plc E) :
    IsOpen (congGrp (n := n) N w : Set (GL (Fin n) (w.adicCompletion E))) :=
  (isOpen_cong hN w).inter ((isOpen_cong hN w).preimage continuous_inv)

private theorem congGrp_le (N : ℕ) (w : Plc E) : congGrp (n := n) N w ≤ KGL w (n := n) := fun _ hy =>
  GlobalTheory.AdelicU.mem_GLint_iff.2 ⟨cong_int hy.1, cong_int hy.2⟩

private theorem congGrp_le_iw {N : ℕ} (w : Plc E) (hN : (N : 𝓞 E) ∈ w.asIdeal) : congGrp (n := n) N w ≤ Iw n w := by
  intro y hy
  have hK : y ∈ GlobalTheory.SplitWeil.KO (w.adicCompletion E) (Fin n) := by
    rw [GlobalTheory.SmGL.SphCompletion.KO_completion]
    exact congGrp_le N w hy
  refine GlobalTheory.SmGL.mem_iwahori.2 ⟨hK, fun i j hij => ?_⟩
  haveI : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have he := ValuativeRel.isEquiv (ValuativeRel.valuation (w.adicCompletion E))
    (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ)))
  rw [he.lt_one_iff_lt_one]
  have h0 : (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j = 0 := Matrix.one_apply_ne hij.ne'
  refine (cong_entry hy.1 i j).trans_lt (max_lt (vN_lt_one w hN) ?_)
  simp [h0]

theorem pCongGrpEx : CongGrpEx := by
  intro E _ _ _ n N hN w
  refine ⟨congGrp N w, fun y => Iff.rfl, isOpen_congGrp hN w, ?_, congGrp_le N w, ?_, fun h => congGrp_le_iw w h,
    fun y hy => ?_⟩
  · exact (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w n).2.of_isClosed_subset
      (Subgroup.isClosed_of_isOpen _ (isOpen_congGrp hN w)) (congGrp_le N w)
  · intro a ha y
    have key : ∀ a ∈ KGL w (n := n), ∀ y, y ∈ congGrp N w → a * y * a⁻¹ ∈ congGrp N w := fun a ha y hy =>
      ⟨cong_conj ha hy.1, by
        have : (a * y * a⁻¹)⁻¹ = a * y⁻¹ * a⁻¹ := by group
        rw [this]; exact cong_conj ha hy.2⟩
    refine ⟨fun h => ?_, key a ha y⟩
    have := key a⁻¹ (inv_mem ha) _ h
    simpa [mul_assoc] using this
  · have := GlobalTheory.SmGL.iwahori_le_KO _ _ hy
    rwa [GlobalTheory.SmGL.SphCompletion.KO_completion] at this

end UpperTheory.Gal.W2.Seed
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PCuspTh
section
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG
open UpperTheory.Gal.CertificateRingHomMap (GUf Plc comp lev GLw IsCen mat sim)
open UpperTheory.Gal.W2.Seed UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Pl UpperTheory.Gal.Spc
open scoped TensorProduct Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Gal.W2.Seed.pCuspTh :
    CuspTh := by
  intro E _ _ _ n w σ
  let σ' : SmIrr (GLw n w) :=
    { V := σ.V
      ρ := σ.ρ.comp (invT n (w.adicCompletion E))
      smooth := PositivityTheory.LocalParametersCuspidal.DepthZeroGlueing.WhittakerInverseTranspose.isSmooth_comp_invT σ.smooth
      irred := PositivityTheory.LocalParametersCuspidal.DepthZeroGlueing.WhittakerInverseTranspose.isIrreducible_comp_invT σ.irred }
  refine ⟨σ', LinearEquiv.refl ℂ _, fun g g' v h => ?_, fun hc => ?_⟩
  · have hg : g' = invT n (w.adicCompletion E) g := Units.ext h
    subst hg
    show σ.ρ (invT n _ (invT n _ g)) v = σ.ρ g v
    rw [UpperTheory.Gal.CertificateRingHomMap.invT_invT']
  · have h2 := PositivityTheory.LocalParametersCuspidal.DepthZeroGlueing.WhittakerInverseTranspose.isCuspidal_comp_invT (ρ := σ'.ρ) hc
    have h3 : σ'.ρ.comp (invT n (w.adicCompletion E)) = σ.ρ :=
      MonoidHom.ext fun g => by
        show σ.ρ (invT n _ (invT n _ g)) = σ.ρ g
        rw [UpperTheory.Gal.CertificateRingHomMap.invT_invT']
    rwa [h3] at h2
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PFacEq
section
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG
open UpperTheory.Gal.CertificateRingHomMap (GUf Plc comp lev GLw IsCen mat sim)
open UpperTheory.Gal.W2.Seed UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Pl UpperTheory.Gal.Spc
open scoped TensorProduct Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Gal.W2.Seed.pFacEq :
    FacEq := by
  intro E _ _ _ A n p _ S F hc w
  have h1 : IsFac F w (fac F.tr hc w) := by
    refine ⟨fun g => ?_, fun y => ?_⟩
    · have e : F.tr.j (F.tr.sec (F.tr.j g)) = F.tr.j g := F.tr.j_sec _
      have := (F.tr.j_eq _ _).1 e w.1 w.2.2
      rw [F.j_tr]
      exact this
    · rw [F.j_tr]
      rfl
  refine ⟨h1, fun L hL => ?_⟩
  have hpr : L.pr = (fac F.tr hc w).pr := MonoidHom.ext fun h => by
    obtain ⟨g, rfl⟩ := F.surj h
    rw [hL.1 g, h1.1 g]
  have hloc : L.loc = (fac F.tr hc w).loc := MonoidHom.ext fun y => by
    rw [hL.2 y, h1.2 y]
  cases hf : fac F.tr hc w with
  | mk pr loc pr_loc comm =>
    cases L with
    | mk pr' loc' pr_loc' comm' =>
      rw [hf] at hpr hloc
      simp only at hpr hloc
      subst hpr hloc
      rfl
end

