module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.KatoTwistedClassNormCompatibleCyclotomic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.Bundle0008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.TopCocG
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.SPushPsi
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.FrobeniusConjugateInertia.FrobConjIne
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.BarMul
section
open scoped MatrixGroups Matrix Classical
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Nb

private theorem frac_eq (D D' : ℕ) [NeZero D] (h : D' = D) (a : ℤ) :
    ∃ j : ℤ, (a : ℚ) / (D' : ℚ) = (((a : ZMod D).val : ℕ) : ℚ) / D + j := by
  subst h
  refine ⟨a / (D' : ℤ), ?_⟩
  have h1 : ((((a : ZMod D').val : ℕ) : ℤ)) = a % (D' : ℤ) := ZMod.val_intCast a
  have h2 : (((a : ZMod D').val : ℕ) : ℚ) = ((a % (D' : ℤ) : ℤ) : ℚ) := by
    rw [← h1]
    push_cast
    rfl
  have hD : (D' : ℚ) ≠ 0 := by exact_mod_cast NeZero.ne D'
  have e : a % (D' : ℤ) = a - (D' : ℤ) * (a / (D' : ℤ)) := Int.emod_def a D'
  rw [h2, e]
  push_cast
  field_simp
  ring

private theorem two_ne (l D : ℕ) [Fact l.Prime] (hl : l ≠ 2) (hD : l ∣ D) (a : ℤ) (ha : (a : ZMod l) ≠ 0) :
    (2 : ZMod D) * (a : ZMod D) ≠ 0 := by
  intro h0
  have h1 := congrArg (ZMod.castHom hD (ZMod l)) h0
  simp only [map_mul, map_ofNat, map_intCast, map_zero] at h1
  rcases mul_eq_zero.mp h1 with h2 | h2
  · have h3 : ((2 : ℕ) : ZMod l) = 0 := by exact_mod_cast h2
    rw [ZMod.natCast_eq_zero_iff] at h3
    exact hl ((Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_two).mp h3)
  · exact ha h2

private theorem bar_mul (l L N p : ℕ) (hL : L ≠ 0) (h : Nat.Coprime p (N * l ^ L)) :
    ((bar l L N p : ℤ) : ZMod l) * (p : ZMod l) = 1 := by
  by_cases hM : N * l ^ L = 0
  · have hp : p = 1 := by
      simpa [hM] using h
    subst hp
    have hv : ((1 : ZMod (N * l ^ L))⁻¹).val = 1 := by
      rw [ZMod.inv_one, ZMod.val_one'' (by omega)]
    simp only [bar, Nat.cast_one, hv, Int.cast_one, mul_one]
  · haveI : NeZero (N * l ^ L) := ⟨hM⟩
    have hdvd : l ∣ N * l ^ L := Dvd.dvd.mul_left (dvd_pow_self l hL) N
    have hu : ((p : ZMod (N * l ^ L)) * (p : ZMod (N * l ^ L))⁻¹) = 1 := ZMod.coe_mul_inv_eq_one p h
    have h1 := congrArg (ZMod.castHom hdvd (ZMod l)) hu
    rw [map_mul, map_one, map_natCast] at h1
    have h2 : ((bar l L N p : ℤ) : ZMod l) = ZMod.castHom hdvd (ZMod l) ((p : ZMod (N * l ^ L))⁻¹) := by
      unfold bar
      rw [Int.cast_natCast, ZMod.natCast_val]
      rfl
    rw [h2, mul_comm]
    exact h1

theorem UpperTheory.V.Z.Kato.Nb.sTopT :
    UpperTheory.V.Z.Kato.Nb.STopT := by
  intro Ω _ _ _ ε X l _ N p _ _ x c d w g hH hP hcop hLw hLift n r
  obtain ⟨ws, hws⟩ := hLw
  have api := sApi Ω ε X l
  have inv := sInvApi Ω ε X l N w
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    exact ⟨fun σ _ => (inv 0).2.2.2.2.2.2.1 _, fun σ _ τ _ => (api 0).2.2.2.2.2.2.2.2.1 _ _,
      ⟨∅, fun σ _ τ _ _ => (api 0).2.2.2.2.2.2.2.2.1 _ _⟩⟩
  · have hl2 : l ≠ 2 := hH.odd
    have hlp : l.Prime := Fact.out
    have hL0 : r + n ≠ 0 := by omega
    have hpl : p.Coprime l := Nat.Coprime.coprime_dvd_right ⟨N * c * d, by ring⟩ hcop
    have hpN : p.Coprime N := Nat.Coprime.coprime_dvd_right ⟨l * c * d, by ring⟩ hcop
    have hpc : p.Coprime c := Nat.Coprime.coprime_dvd_right ⟨l * N * d, by ring⟩ hcop
    have hpNL : p.Coprime (N * l ^ (r + n)) := Nat.Coprime.mul_right hpN (Nat.Coprime.pow_right _ hpl)
    have hcN : c.Coprime N := Nat.Coprime.coprime_dvd_right ⟨6 * l, by ring⟩ hH.cc
    have hcl : c.Coprime l := Nat.Coprime.coprime_dvd_right ⟨6 * N, by ring⟩ hH.cc
    have hdN : d.Coprime N := Nat.Coprime.coprime_dvd_right ⟨6 * l, by ring⟩ hH.cd
    have hdl : d.Coprime l := Nat.Coprime.coprime_dvd_right ⟨6 * N, by ring⟩ hH.cd
    have hpd : p.Coprime d := Nat.Coprime.coprime_dvd_right ⟨l * N * c, by ring⟩ hcop
    have hM0 : N * l ^ (r + n) * p ≠ 0 :=
      mul_ne_zero (mul_ne_zero (NeZero.ne N) (pow_ne_zero _ hlp.ne_zero)) (NeZero.ne p)
    haveI : NeZero (N * l ^ (r + n) * p) := ⟨hM0⟩
    have hMeq : lvT l n r N p = N * (N * l ^ (r + n) * p) := by
      unfold lvT
      ring
    haveI : NeZero (lvT l n r N p) := ⟨by rw [hMeq]; exact mul_ne_zero (NeZero.ne N) hM0⟩
    have hLev : Lev l n N (N * l ^ (r + n) * p) (lvT l n r N p) g :=
      ⟨hMeq, ⟨l ^ (r + n) * p, by ring⟩, ⟨N * l ^ r * p, by ring⟩, hn, hH.cop, hH.g0⟩
    have hLv : Lv c d (N * l ^ (r + n) * p) :=
      ⟨Nat.pos_of_ne_zero hM0,
        Nat.Coprime.mul_right (Nat.Coprime.mul_right hcN (Nat.Coprime.pow_right _ hcl)) hpc.symm,
        Nat.Coprime.mul_right (Nat.Coprime.mul_right hdN (Nat.Coprime.pow_right _ hdl)) hpd.symm⟩
    have hdvdl : l ∣ N * l ^ (r + n) * p := Dvd.dvd.mul_right (Dvd.dvd.mul_left (dvd_pow_self l hL0) N) p
    have hbp : ((bar l (r + n) N p : ℤ) : ZMod l) * (p : ZMod l) = 1 := bar_mul l (r + n) N p hL0 hpNL
    have hlL : ((l : ZMod l)) ^ (r + n) = 0 := by
      rw [ZMod.natCast_self]
      exact zero_pow hL0
    have hN0 : (N : ZMod l) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      exact (Nat.Prime.coprime_iff_not_dvd hlp).mp hH.cop
    have ha0 : (((bar l (r + n) N p * ((N : ℤ) + ((x.val : ℕ) : ℤ) * ((topT l (r + n) N : ℕ) : ℤ) * (l : ℤ) ^ (r + n)) * (p : ℤ) + (N : ℤ) * (l : ℤ) ^ (r + n)) : ℤ) : ZMod l) ≠ 0 := by
      have e : (((bar l (r + n) N p * ((N : ℤ) + ((x.val : ℕ) : ℤ) * ((topT l (r + n) N : ℕ) : ℤ) * (l : ℤ) ^ (r + n)) * (p : ℤ) + (N : ℤ) * (l : ℤ) ^ (r + n)) : ℤ) : ZMod l) = (N : ZMod l) := by
        push_cast
        linear_combination (N : ZMod l) * hbp + (((bar l (r + n) N p : ℤ) : ZMod l) * ((x.val : ℕ) : ZMod l) * ((topT l (r + n) N : ℕ) : ZMod l) * (p : ZMod l) + (N : ZMod l)) * hlL
      rw [e]
      exact hN0
    have hb1 : (((bar l (r + n) N p * (N : ℤ) * (p : ℤ) + (N : ℤ) * (l : ℤ) ^ (r + n)) : ℤ) : ZMod l) ≠ 0 := by
      have e : (((bar l (r + n) N p * (N : ℤ) * (p : ℤ) + (N : ℤ) * (l : ℤ) ^ (r + n)) : ℤ) : ZMod l) = (N : ZMod l) := by
        push_cast
        linear_combination (N : ZMod l) * hbp + (N : ZMod l) * hlL
      rw [e]
      exact hN0
    let x₀ : Row (N * l ^ (r + n) * p) :=
      ![(((bar l (r + n) N p * ((N : ℤ) + ((x.val : ℕ) : ℤ) * ((topT l (r + n) N : ℕ) : ℤ) * (l : ℤ) ^ (r + n)) * (p : ℤ) + (N : ℤ) * (l : ℤ) ^ (r + n)) : ℤ) : ZMod (N * l ^ (r + n) * p)),
        (((0 : ℤ)) : ZMod (N * l ^ (r + n) * p))]
    let y₀ : Row (N * l ^ (r + n) * p) :=
      ![(((bar l (r + n) N p * ((topT l (r + n) N : ℕ) : ℤ) * (l : ℤ) ^ (r + n) * (p : ℤ)) : ℤ) : ZMod (N * l ^ (r + n) * p)),
        (((bar l (r + n) N p * (N : ℤ) * (p : ℤ) + (N : ℤ) * (l : ℤ) ^ (r + n)) : ℤ) : ZMod (N * l ^ (r + n) * p))]
    have hOk : Ok x₀ y₀ := by
      refine ⟨fun h => ?_, fun h => ?_⟩
      · have h1 := congrFun h 0
        simp only [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul, Nat.cast_ofNat] at h1
        exact two_ne l _ hl2 hdvdl _ ha0 h1
      · have h1 := congrFun h 1
        simp only [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul, Nat.cast_ofNat] at h1
        exact two_ne l _ hl2 hdvdl _ hb1 h1
    have hx : ∀ i : Fin 2, ∃ j : ℤ, ixUT l (r + n) N p x i = toQ (N * l ^ (r + n) * p) x₀ i + j := by
      intro i
      fin_cases i
      · exact frac_eq _ _ rfl _
      · exact frac_eq _ _ rfl _
    have hy : ∀ i : Fin 2, ∃ j : ℤ, ixVT l (r + n) N p i = toQ (N * l ^ (r + n) * p) y₀ i + j := by
      intro i
      fin_cases i
      · exact frac_eq _ _ rfl _
      · exact frac_eq _ _ rfl _
    obtain ⟨β, hβ, hcg⟩ := sTopRel Ω ε X l n N (N * l ^ (r + n) * p) (lvT l n r N p) w g hLev hLift c d ws hws hLv
      x₀ y₀ hOk _ _ hx hy
    exact sTopCocG Ω ε X l n N _ _ w g hLev hLift x₀ y₀ hOk (ws n _) (hws.coc n _ hLv) _ β hβ hcg
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.CohApi
section
open scoped MatrixGroups Matrix Classical
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Nb

theorem UpperTheory.V.Z.Kato.Nb.sCohApi :
    UpperTheory.V.Z.Kato.Nb.SCohApi := by
  intro Ω _ _ _ ε X l hl N w n hN A _ κ
  obtain ⟨he, hadd, hsm, hsum, -, hact, hgal, hsucc, h0, -, -⟩ := sApi Ω ε X l n
  obtain ⟨i0, iadd, ism, -, isum, isucc, iz, -⟩ := sInvApi Ω ε X l N w n
  have cast : ∀ {a b b' : X.Fn l}, CgF X l n a b → b = b' → CgF X l n a b' := fun h e => e ▸ h
  have lin : ∀ T : X.Fn l →ₗ[ℤ_[l]] X.Fn l, (∀ a b, CgF X l n a b → CgF X l n (T a) (T b)) →
      (∀ a, InvM X l N w n a → InvM X l N w n (T a)) →
      (∀ s a, InvM X l N w n a → CgF X l n (X.galB l s (T a)) (T (X.galB l s a))) →
      ∀ z z', CohB X l N w n κ z z' → CohB X l N w n κ (fun s y => T (z s y)) (fun s y => T (z' s y)) := by
    rintro T h1 h2 h3 z z' ⟨b, hb, hz⟩
    refine ⟨fun y => T (b y), fun y => h2 _ (hb y), fun s y => ?_⟩
    refine he.trans (cast (h1 _ _ (hz s y)) (by rw [map_add (f := _), map_sub])) ?_
    exact (hadd _ _ _ _ (he.refl _) (hadd _ _ _ _ (he.symm (h3 s _ (hb _))) (he.refl _)).2).1
  have ofCg : ∀ z z' : (Ω ≃ₐ[ℚ] Ω) → A → X.Fn l, (∀ s y, CgF X l n (z s y) (z' s y)) → CohB X l N w n κ z z' :=
    fun z z' h => ⟨fun _ => 0, fun _ => i0, fun s y => cast (h s y) (by simp)⟩
  refine ⟨⟨fun z => ofCg z z fun s y => he.refl _, ?_, ?_⟩, ofCg, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro z z' ⟨b, hb, hz⟩
    refine ⟨fun y => 0 - b y, fun y => (iadd _ _ i0 (hb y)).2, fun s y => ?_⟩
    have h := (hadd _ _ _ _ (he.symm (hz s y)) (he.refl (X.galB l s (b (y * κ s)) - b y))).2
    rw [add_sub_cancel_right] at h
    exact cast h (by simp only [map_sub, map_zero]; abel)
  · rintro z z' z'' ⟨b, hb, hz⟩ ⟨c, hc, hz'⟩
    refine ⟨fun y => b y + c y, fun y => (iadd _ _ (hb y) (hc y)).1, fun s y => ?_⟩
    refine he.trans (hz s y) (cast (hadd _ _ _ _ (hz' s y) (he.refl _)).1 ?_)
    simp only [map_add (f := _)]; abel
  · rintro z z' v v' ⟨b, hb, hz⟩ ⟨c, hc, hv⟩
    refine ⟨⟨fun y => b y + c y, fun y => (iadd _ _ (hb y) (hc y)).1, fun s y => ?_⟩,
      ⟨fun y => b y - c y, fun y => (iadd _ _ (hb y) (hc y)).2, fun s y => ?_⟩⟩
    · refine cast (hadd _ _ _ _ (hz s y) (hv s y)).1 ?_
      simp only [map_add (f := _), Pi.add_apply]; abel
    · refine cast (hadd _ _ _ _ (hz s y) (hv s y)).2 ?_
      simp only [map_sub, Pi.sub_apply]; abel
  · rintro k t z z' ⟨b, hb, hz⟩
    refine ⟨fun y => k • b (y * t), fun y => ism k _ (hb _), fun s y => ?_⟩
    refine cast (hsm k _ _ (hz s (y * t))) ?_
    simp only [map_smul, smul_add, smul_sub, mul_right_comm y t]
  · rintro z z' ⟨b, hb, hz⟩
    exact ⟨b, fun y => isucc _ (hb y), fun s y => hsucc _ _ (hz s y)⟩
  · intro z z'
    exact ⟨fun _ => 0, fun _ => iz _, fun s y => h0 _ _⟩
  · rintro A' _ _ _ π z z' ⟨b, hb, hz⟩
    refine ⟨fun t => ∑ y ∈ Finset.univ.filter (fun y => π y = t), b y, fun t => isum _ _ _ fun y _ => hb y, fun s t => ?_⟩
    refine cast (hsum _ _ _ _ fun y _ => hz s y) ?_
    have e : ∑ y ∈ Finset.univ.filter (fun y => π y = t * π (κ s)), b y =
        ∑ y ∈ Finset.univ.filter (fun y => π y = t), b (y * κ s) := by
      symm
      refine Finset.sum_equiv (Equiv.mulRight (κ s)) (fun y => ?_) (fun y _ => rfl)
      simp
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [GlobalTheory.KA.push, e, Finset.sum_add_distrib, Finset.sum_sub_distrib, map_sum]
  · intro p hp hc z z' h
    have hd := (GlobalTheory.KZ.Betti.isDiam_sgD (l := l) hN.ne' hl.out.ne_zero (Nat.Coprime.coprime_mul_left_right hc)).1
    refine ⟨lin _ (fun a b hab => ?_) (sHeckeInv Ω ε X l N w n p hN hp hc) (sHeckeGal Ω ε X l N w n p hN hp hc) z z' h,
      lin _ (hact _) (fun a ha => ((sGalAct Ω ε X l N w n hN 1 a ha).2 _ hd).1)
        (fun s a ha => ((sGalAct Ω ε X l N w n hN s a ha).2 _ hd).2) z z' h⟩
    simp only [Tower.heckeT, LinearMap.add_apply, LinearMap.sum_apply]
    exact (hadd _ _ _ _ (hsum _ _ _ _ fun j _ => hact _ _ _ hab) (hact _ _ _ hab)).1
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.FrobeniusConjugateInertia
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.KA UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.V.Z.Kato.Nb
open scoped Matrix MatrixGroups Classical

namespace UpperTheory.V.Z.Kato.Nb.EulerSystemNorms

variable {l : ℕ} [Fact l.Prime] {Ω : Type} [Field Ω] [Algebra ℚ Ω]

private theorem cont_bar : Continuous (cycBar ℚ Ω l) :=
  (Continuous.units_map ((algebraMap ℚ_[l] (Qbar l)).comp PadicInt.Coe.ringHom).toMonoidHom
    ((continuous_algebraMap ℚ_[l] (Qbar l)).comp continuous_subtype_val)).comp (continuous_cycZ ℚ Ω l)

private theorem cont_hom {M : Type} [Monoid M] [TopologicalSpace M] (f : G ℚ Ω →* Mˣ) (h : Continuous fun s => (f s : M)) :
    Continuous f :=
  Units.continuous_iff.2 ⟨h, (h.comp continuous_inv).congr fun s => by simp⟩

private theorem cont_cls [IsAlgClosure ℚ Ω] (N : ℕ) [NeZero N] (δ : (ZMod N)ˣ → Qbar l) :
    Continuous fun s => δ (Chr.cls ℚ Ω N s) := by
  refine (IsLocallyConstant.comp ((IsLocallyConstant.iff_exists_open _).2 fun s => ?_) δ).continuous
  refine ⟨(fun t => s⁻¹ * t) ⁻¹' ((Chr.cls ℚ Ω N).ker : Set (G ℚ Ω)),
    (Chr.clsFacts ℚ Ω N).1.preimage (continuous_const.mul continuous_id), by simp, fun t ht => ?_⟩
  have h : Chr.cls ℚ Ω N (s⁻¹ * t) = 1 := ht
  rw [map_mul, map_inv, inv_mul_eq_one] at h
  exact h.symm

private theorem trace_eq {k : Type} [Field k] (g : GL (Fin 2) k) (a : k)
    (h : (g : Matrix (Fin 2) (Fin 2) k) ^ 2 - a • (g : Matrix (Fin 2) (Fin 2) k) + (g : Matrix (Fin 2) (Fin 2) k).det • 1 = 0) :
    (g : Matrix (Fin 2) (Fin 2) k).trace = a := by
  have hd : (g : Matrix (Fin 2) (Fin 2) k).det ≠ 0 := (Matrix.isUnits_det_units g).ne_zero
  generalize (g : Matrix (Fin 2) (Fin 2) k) = m at h hd
  have e := fun i j => congrFun (congrFun h i) j
  have e00 := e 0 0
  have e01 := e 0 1
  simp [pow_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two] at e00 e01
  rw [Matrix.det_fin_two] at hd
  rw [Matrix.trace_fin_two]
  have e10 := e 1 0
  have e11 := e 1 1
  simp [pow_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two] at e10 e11
  apply mul_right_cancel₀ hd
  linear_combination m 1 1 * e00 - m 1 0 * e01

private theorem stable_top {W : R2 Ω l} (h : IsIrr (W.comp (H0g W).subtype)) (U : Submodule (Qbar l) (Fin 2 → Qbar l))
    (h0 : U ≠ ⊥) (hU : ∀ s, ∀ v ∈ U, mat W s *ᵥ v ∈ U) : U = ⊤ :=
  (h.2.2 U le_top fun s v hv => hU s v hv).resolve_left h0

private theorem not_scalar {W : R2 Ω l} (h : IsIrr (W.comp (H0g W).subtype)) : ∃ s, ∀ t : Qbar l, mat W s ≠ t • 1 := by
  by_contra hn
  push Not at hn
  have h1 := stable_top h (Submodule.span (Qbar l) {![1, 0]}) (by simp) fun s v hv => by
    obtain ⟨t, ht⟩ := hn s
    rw [ht, Matrix.smul_mulVec, Matrix.one_mulVec]
    exact Submodule.smul_mem _ _ hv
  have h2 : (![0, 1] : Fin 2 → Qbar l) ∈ Submodule.span (Qbar l) {(![1, 0] : Fin 2 → Qbar l)} := h1 ▸ Submodule.mem_top
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 h2
  simpa using congrFun hc 1

private theorem inv_mem (cf : Coef l) {q : ℕ} (h : Nat.Coprime q l) : ((q : Qbar l))⁻¹ ∈ cf.O := by
  have hu : IsUnit (q : ℤ_[l]) := PadicInt.isUnit_iff.2 (PadicInt.norm_natCast_eq_one_iff.2 h.symm)
  obtain ⟨y, hy⟩ := hu.exists_right_inv
  have e := congrArg (algebraMap ℤ_[l] (Qbar l)) hy
  rw [map_mul, map_natCast, map_one] at e
  rw [← eq_inv_of_mul_eq_one_right e]
  exact cf.O.algebraMap_mem y

end UpperTheory.V.Z.Kato.Nb.EulerSystemNorms

open UpperTheory.V.Z.Kato.Nb.EulerSystemNorms in
theorem UpperTheory.V.Z.Kato.Nb.sEuler :
    UpperTheory.V.Z.Kato.Nb.SEuler := by
  intro l _ Ω _ _ _ ι e gN A W ε X pr N _ x c d gm ψ cf hA he hlN S hNf hint
  obtain ⟨-, -, -, -, hO, -, -⟩ := sInteg l Ω ι e gN A W ε X pr N x c d gm ψ cf hA he hint
  have hD := sDiamChar l Ω ι e gN A W ε X pr N x c d gm ψ cf hA he hlN
  obtain ⟨hc, hd, -, -, hadd, hsm, -, hgal, ⟨δ', hT⟩, -, -, χ₀, -, -, hχ⟩ := hA
  have hl : l.Prime := Fact.out
  have hN : 0 < N := NeZero.pos N
  obtain ⟨S0, hES⟩ := sEs l Ω ε X hNf.l_odd N (2 * e - 1) hN
  let ρ : R2 Ω l := tw W (cycBar ℚ Ω l ^ e * χ₀⁻¹)
  have hρ : ∀ s, mat ρ s = rhoK W e ψ s := fun s => by
    rw [mat, tw_val, rhoK, thK, ← hχ]
    simp [mul_comm]
  have hn0 : l * N * c * d ≠ 0 := by
    have := hl.pos
    positivity
  have key : ∀ w : Pl, w ∉ S → normV w ∉ S0 → Nat.Coprime (normV w) (l * N) → ∃ a δ : Qbar l,
      (∀ b ∈ X.B N l (2 * e - 1), pr (X.heckeT N l (normV w) b) = a • pr b ∧ pr (X.diam N l (normV w) b) = δ • pr b) ∧
      ∀ (B : ValuationSubring Ω) (σ : G ℚ Ω), IsPlaceOver B w → IsFrob B (normV w) σ →
        (rhoK W e ψ σ).trace = a ∧ (rhoK W e ψ σ).det = (normV w : Qbar l) ^ (2 * e) * δ := by
    by_cases hz : ∃ b ∈ X.B N l (2 * e - 1), pr b ≠ 0
    · obtain ⟨δ, hδ⟩ := hD hz
      let χ : G ℚ Ω →* (Qbar l)ˣ := cycBar ℚ Ω l ^ (2 * e) * δ.comp (Chr.cls ℚ Ω N)
      have hspan : Submodule.span (Qbar l) (pr '' (X.B N l (2 * e - 1) : Set (X.Fn l))) = ⊤ := by
        refine stable_top hNf.irr _ (fun h => ?_) fun s v hv => ?_
        · obtain ⟨b, hb, hb0⟩ := hz
          exact hb0 ((Submodule.span_eq_bot.1 h) _ ⟨b, hb, rfl⟩)
        · have h1 : mat W s = ((cycBar ℚ Ω l ^ e * χ₀⁻¹) s⁻¹ : Qbar l) • mat ρ s := by
            rw [mat, mat, tw_val, smul_smul, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, one_smul]
          rw [h1, Matrix.smul_mulVec]
          refine Submodule.smul_mem _ _ ?_
          refine (Submodule.span_le (p := (Submodule.span (Qbar l) (pr '' (X.B N l (2 * e - 1) : Set (X.Fn l)))).comap
            (Matrix.mulVecLin (mat ρ s)))).2 ?_ hv
          rintro _ ⟨b, hb, rfl⟩
          refine Submodule.subset_span ⟨_, (sBStab Ω ε X l N _ hN b hb).1 s, ?_⟩
          rw [hgal s b hb, ← hρ]
          rfl
      have hχF : ∀ (w : Pl), Nat.Coprime (normV w) (l * N) → ∀ (B : ValuationSubring Ω) (σ : G ℚ Ω), IsPlaceOver B w →
          IsFrob B (normV w) σ → (χ σ : Qbar l) = (normV w : Qbar l) ^ (2 * e) * δ (Chr.cls ℚ Ω N σ) := fun w hw B σ hB hσ => by
        rw [← eps_frobAt l ((normV_prime w).coprime_iff_not_dvd.1 hw.coprime_mul_right_right) hB hσ]
        simp [χ]
      have hrel : ∀ (w : Pl), normV w ∉ S0 → Nat.Coprime (normV w) (l * N) → ∀ (B : ValuationSubring Ω) (σ : G ℚ Ω),
          IsPlaceOver B w → IsFrob B (normV w) σ →
          mat ρ σ ^ 2 - ι.symm (gN.a (normV w)) • mat ρ σ + (χ σ : Qbar l) • 1 = 0 := fun w hw0 hw B σ hB hσ => by
        have hnd := (normV_prime w).coprime_iff_not_dvd.1 hw
        have h1 : Matrix.mulVecLin (mat ρ σ - ι.symm (gN.a (normV w)) • 1 + (χ σ : Qbar l) • mat ρ σ⁻¹) = 0 := by
          refine LinearMap.ext_on hspan ?_
          rintro _ ⟨b, hb, rfl⟩
          have hb' := (sBStab Ω ε X l N _ hN b hb).1 σ⁻¹
          have h2 := congrArg pr (hES w B σ hw0 (normV_prime w) hB hσ b hb)
          rw [(hT _ (normV_prime w) hnd b hb).1, hadd, hsm, hgal σ b hb,
            hδ _ _ (normV_prime w) hnd (cls_frobAt N hw.coprime_mul_left_right.symm hB hσ) _ hb', hgal _ b hb, smul_smul,
            show 2 * e - 1 + 1 = 2 * e by omega, ← hρ, ← hρ] at h2
          rw [hχF w hw B σ hB hσ, Matrix.mulVecLin_apply, Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec,
            Matrix.smul_mulVec, Matrix.one_mulVec, h2]
          simp
        have h3 : mat ρ σ - ι.symm (gN.a (normV w)) • 1 + (χ σ : Qbar l) • mat ρ σ⁻¹ = 0 :=
          Matrix.toLin'.injective (h1.trans (map_zero _).symm)
        have h4 := congrArg (· * mat ρ σ) h3
        simp only [add_mul, sub_mul, smul_mul_assoc, one_mul, zero_mul, mat, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one,
          Units.val_one] at h4
        rw [pow_two, mat, ← Units.val_mul, ← map_mul]
        exact h4
      have hc0 : Continuous fun s => (χ₀ s : Qbar l) := by
        simp only [hχ]
        exact ((GlobalTheory.KZ.IwC.isLocallyConstant_cycMod 1).comp fun u : (ZMod (l ^ 1))ˣ => ψ (((u : ZMod (l ^ 1)).val : ℕ) : ZMod l)).continuous
      have hcρ : Continuous ρ := cont_hom _ (by
        simp only [ρ, tw_val]
        exact (Units.continuous_val.comp ((cont_bar.pow e).mul (cont_hom χ₀ hc0).inv)).smul (Units.continuous_val.comp hNf.cont))
      have hcχ : Continuous χ := (cont_bar.pow (2 * e)).mul (cont_hom (δ.comp (Chr.cls ℚ Ω N)) (cont_cls (Ω := Ω) N fun u => (δ u : Qbar l)))
      have hdet := sDetChar l Ω ρ χ hcρ hcχ (by
        obtain ⟨s, hs⟩ := not_scalar hNf.irr
        refine ⟨s, fun t ht => hs (((cycBar ℚ Ω l ^ e * χ₀⁻¹) s : Qbar l)⁻¹ * t) ?_⟩
        rw [mul_smul, ← ht, tw_val, smul_smul, inv_mul_cancel₀ (Units.ne_zero _), one_smul]) (S0 ∪ (l * N).primeFactors)
        fun v B σ hv hB hσ => ⟨_, hrel v (fun h => hv (Finset.mem_union_left _ h))
          ((normV_prime v).coprime_iff_not_dvd.2 fun h => hv (Finset.mem_union_right _
            (Nat.mem_primeFactors.2 ⟨normV_prime v, h, (mul_pos hl.pos hN).ne'⟩))) B σ hB hσ⟩
      intro w _ hw0 hw
      have hnd := (normV_prime w).coprime_iff_not_dvd.1 hw
      refine ⟨ι.symm (gN.a (normV w)), δ (ZMod.unitOfCoprime _ hw.coprime_mul_left_right), fun b hb =>
        ⟨(hT _ (normV_prime w) hnd b hb).1, hδ _ _ (normV_prime w) hnd (ZMod.coe_unitOfCoprime _ _) b hb⟩, fun B σ hB hσ => ?_⟩
      rw [← hρ]
      refine ⟨trace_eq _ _ (by rw [hdet]; exact hrel w hw0 hw B σ hB hσ), ?_⟩
      rw [hdet, hχF w hw B σ hB hσ]
      congr 3
      exact Units.ext ((cls_frobAt N hw.coprime_mul_left_right.symm hB hσ).trans (ZMod.coe_unitOfCoprime _ _).symm)
    · push Not at hz
      intro w hwS _ hw
      have hnd := (normV_prime w).coprime_iff_not_dvd.1 hw
      have hnl := (normV_prime w).coprime_iff_not_dvd.1 hw.coprime_mul_right_right
      have hq : ((normV w : ℕ) : Qbar l) ^ (2 * e) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (normV_prime w).ne_zero)
      obtain ⟨B₀, σ₀, hB₀, hσ₀⟩ := exists_frobAt Ω w
      refine ⟨(rhoK W e ψ σ₀).trace, (((normV w : ℕ) : Qbar l) ^ (2 * e))⁻¹ * (rhoK W e ψ σ₀).det, fun b hb => ?_,
        fun B σ hB hσ => ?_⟩
      · rw [(hT _ (normV_prime w) hnd b hb).1, (hT _ (normV_prime w) hnd b hb).2, hz b hb]
        simp
      · have hm := fun h => hnl ((mem_place_iff w l).1 h)
        have h1 : cycZ ℚ Ω l σ = cycZ ℚ Ω l σ₀ := Units.ext ((cycZ_of_isFrob hm hB hσ).trans (cycZ_of_isFrob hm hB₀ hσ₀).symm)
        have h2 : thK l e ψ σ = thK l e ψ σ₀ := by
          simp only [thK, eps, cycBar, cycMod, MonoidHom.comp_apply, h1]
        obtain ⟨h3, h4⟩ := frobInv hNf hwS hB hσ hB₀ hσ₀
        rw [mul_inv_cancel_left₀ hq]
        simp only [rhoK, Matrix.trace_smul, Matrix.det_smul, h2, h3, h4, and_self]
  refine ⟨S ∪ ((finite_normV S0).union (finite_dvd hn0)).toFinset, Finset.subset_union_left, fun w hw => ?_⟩
  simp only [Finset.mem_union, Set.Finite.mem_toFinset, Set.mem_union, Set.mem_setOf_eq, not_or] at hw
  have hcop := (normV_prime w).coprime_iff_not_dvd.2 hw.2.2
  have hw' : Nat.Coprime (normV w) (l * N) := hcop.coprime_mul_right_right.coprime_mul_right_right
  obtain ⟨a, δ, h1, h2⟩ := key w hw.1 hw.2.1 hw'
  obtain ⟨B₀, σ₀, hB₀, hσ₀⟩ := exists_frobAt Ω w
  obtain ⟨h3, h4⟩ := h2 B₀ σ₀ hB₀ hσ₀
  have hq : ((normV w : ℕ) : Qbar l) ^ (2 * e) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (normV_prime w).ne_zero)
  refine ⟨normV_prime w, hcop, a, δ, ?_, ?_, h1, fun B σ hB hσ =>
    ⟨eps_frobAt l ((normV_prime w).coprime_iff_not_dvd.1 hw'.coprime_mul_right_right) hB hσ, h2 B σ hB hσ⟩⟩
  · rw [← h3, Matrix.trace_fin_two]
    exact add_mem (hO _ _ _) (hO _ _ _)
  · rw [← inv_mul_cancel_left₀ hq δ, ← h4, ← inv_pow, Matrix.det_fin_two]
    exact mul_mem (pow_mem (inv_mem cf hw'.coprime_mul_right_right) _)
      (sub_mem (mul_mem (hO _ _ _) (hO _ _ _)) (mul_mem (hO _ _ _) (hO _ _ _)))
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.STop0
section
open scoped MatrixGroups Matrix Classical
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Nb

theorem UpperTheory.V.Z.Kato.Nb.sTop0 :
    UpperTheory.V.Z.Kato.Nb.STop0 := by
  intro Ω _ _ _ ε X l _ N _ x c d w g hH hLw hLift n r
  obtain ⟨ws, hws⟩ := hLw
  have api := sApi Ω ε X l
  have inv := sInvApi Ω ε X l N w
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    exact ⟨fun σ _ => (inv 0).2.2.2.2.2.2.1 _, fun σ _ τ _ => (api 0).2.2.2.2.2.2.2.2.1 _ _,
      ⟨∅, fun σ _ τ _ _ => (api 0).2.2.2.2.2.2.2.2.1 _ _⟩⟩
  · have hlp : l.Prime := Fact.out
    have hL0 : r + n ≠ 0 := by omega
    have hM0 : N * l ^ (r + n) ≠ 0 := mul_ne_zero (NeZero.ne N) (pow_ne_zero _ hlp.ne_zero)
    haveI : NeZero (N * l ^ (r + n)) := ⟨hM0⟩
    have hMeq : topM l n r (N * N) = N * (N * l ^ (r + n)) := by
      unfold topM
      ring
    haveI : NeZero (topM l n r (N * N)) := ⟨by rw [hMeq]; exact mul_ne_zero (NeZero.ne N) hM0⟩
    have hLev : Lev l n N (N * l ^ (r + n)) (topM l n r (N * N)) g :=
      ⟨hMeq, ⟨l ^ (r + n), by ring⟩, ⟨N * l ^ r, by ring⟩, hn, hH.cop, hH.g0⟩
    have hLv : Lv c d (N * l ^ (r + n)) := hH.lv hlp.ne_zero (NeZero.ne N) rfl
    have hdvdl : l ∣ N * l ^ (r + n) := Dvd.dvd.mul_left (dvd_pow_self l hL0) N
    have hOk := ok_UV (M := N * l ^ (r + n)) (L := r + n) hlp hH.odd hH.cop (by omega) hdvdl x
    obtain ⟨β, hβ, hcg⟩ := sTopRel Ω ε X l n N (N * l ^ (r + n)) (topM l n r (N * N)) w g hLev hLift c d ws hws hLv
      _ _ hOk _ _ (ixU_toQ rfl x) (ixV_toQ rfl)
    exact sTopCocG Ω ε X l n N _ _ w g hLev hLift _ _ hOk (ws n _) (hws.coc n _ hLv) _ β hβ hcg
end

