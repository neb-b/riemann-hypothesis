module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.Bundle0006
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0236
public import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
public import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0009
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0007

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.ChiFixAlt
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.CyclotomicQExpansion GlobalTheory.KummerEisensteinGalois GlobalTheory.K4 GlobalTheory.LambdaValuationPowers
open scoped Matrix MatrixGroups TensorProduct

namespace UpperTheory.V.Z.Kato.Joint

def smZ {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime] (d₀ : ℕ) (hd₀ : Nat.Coprime d₀ l)
    (Z : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l) (r : ℕ) (s : G ℚ Ω) (y : (ZMod (l ^ r))ˣ) : Qbar l :=
  Z r s y - (d₀ : Qbar l) * Z r s (y * ZMod.unitOfCoprime d₀ (Nat.Coprime.pow_right r hd₀))

def SmSys : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : R2 Ω l) (c : Coef l) (y : G ℚ Ω → Fin 2 → Qbar l) (S' : Finset Pl)
    (A : ValuationSubring Ω) (ν : G ℚ Ω → (Qbar l)ˣ) (Z : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l) (e : ℕ) (ψ : ZMod l → Qbar l)
    (d₀ : ℕ) (hd₀ : Nat.Coprime d₀ l), (d₀ : ZMod l) = 1 → (∀ x, ‖ψ x‖ ≤ 1) → Sys W c y S' → IwSys2 c A ν Z →
    SpLink A e (chiK l ψ) Z y →
    Sys W c (fun s => (1 - (d₀ : Qbar l) ^ (e + 1)) • y s) S' ∧ IwSys2 c A ν (smZ d₀ hd₀ Z) ∧
      SpLink A e (chiK l ψ) (smZ d₀ hd₀ Z) fun s => (1 - (d₀ : Qbar l) ^ (e + 1)) • y s

def ChiFix : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (N : ℕ) (χ : DirichletCharacter ℂ N) (χd : ℕ → ℤ_[l]),
    (∀ d : ℕ, d.Coprime N → ι (algebraMap ℚ_[l] (Qbar l) (χd d : ℚ_[l])) = χ d) →
    ∃ χ' : ℕ → ℤ_[l], (∀ d : ℕ, d.Coprime N → χ' d = χd d) ∧ (∀ d : ℕ, Nat.Coprime d N → IsUnit (χ' d)) ∧
      (∀ a b : ℕ, χ' (a * b) = χ' a * χ' b) ∧ ∀ a b : ℕ, a % N = b % N → χ' a = χ' b

end UpperTheory.V.Z.Kato.Joint

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.ExplSmul
section
open UpperTheory.V.Z.Kato.Joint
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ

private theorem cg_mul_left {l : ℕ} [Fact l.Prime] {n : ℕ} {a b a' b' : Qbar l} (x : Qbar l) (hx : ‖x‖ ≤ 1)
    (h : Cg n a b) (ha : a' = x * a) (hb : b' = x * b) : Cg n a' b' := by
  unfold Cg at h ⊢
  rw [ha, hb, ← mul_sub, norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) hx).trans h

theorem UpperTheory.V.Z.Kato.Joint.explSmul :
    UpperTheory.V.Z.Kato.Joint.ExplSmul := by
  intro l _ Ω _ _ ι e A c Z j s u w α B cc n β t m ⟨κ, v, m₀, c₀, hκ, hv, ζ, hζ, H⟩
  have hl1 : ‖((l : ℕ) : Qbar l)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one (PadicAlgCl l) l
  have hx : ‖((l : ℕ) : Qbar l) ^ m‖ ≤ 1 := by
    rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hl1
  have hl0 : ((l : ℕ) : Qbar l) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero
  refine ⟨(l : Qbar l) ^ m * κ, v, m₀, c₀, mul_ne_zero (pow_ne_zero _ hl0) hκ, hv, ζ, hζ, fun k hk => ?_⟩
  obtain ⟨I, inst, P, o, ⟨p1, p2, p3, p4, q1, q2, q3, q4, q5⟩, hc⟩ := H k hk
  refine ⟨I, inst, P, fun i => (l : Qbar l) ^ m * o i,
    ⟨p1, p2, fun i => c.O.mul_mem (c.O.pow_mem (natCast_mem c.O l) m) (p3 i), p4, q1, q2, q3, fun i => ?_,
      fun s hs h1 h2 => ?_⟩, fun ψ hψ => ?_⟩
  · rw [norm_mul]
    exact mul_le_one₀ hx (norm_nonneg _) (q4 i)
  · obtain ⟨kk, a1, a2⟩ := q5 s hs h1 h2
    refine ⟨kk, a1, cg_mul_left _ hx a2 rfl ?_⟩
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => mul_assoc _ _ _
  · refine cg_mul_left _ hx (hc ψ hψ) ?_ ?_
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      unfold htv
      rw [mul_left_comm]
      congr 1
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => mul_assoc _ _ _
    · beta_reduce
      split_ifs
      · ring
      · rw [mul_zero]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.GmEx
section
open UpperTheory.V.Z.Kato.Joint
open scoped Matrix MatrixGroups

theorem UpperTheory.V.Z.Kato.Joint.gmEx :
    UpperTheory.V.Z.Kato.Joint.GmEx := by
  intro l _ N h
  have hN : (N : ZMod l) * (N : ZMod l)⁻¹ = 1 := ZMod.coe_mul_inv_eq_one N h.symm
  let m : (ZMod l)ˣ → ℤ := fun r => (((-(r : ZMod l)) * (N : ZMod l)⁻¹).val : ℤ)
  have hm : ∀ r : (ZMod l)ˣ, (N : ZMod l) * ((m r : ℤ) : ZMod l) = -(r : ZMod l) := by
    intro r
    simp only [m, Int.cast_natCast, ZMod.natCast_zmod_val]
    rw [mul_left_comm, hN, mul_one]
  refine ⟨fun r => ⟨!![1, 0; (N : ℤ) * m r, 1], by simp [Matrix.det_fin_two]⟩, fun r => ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine (CongruenceSubgroup.Gamma1_mem N _).2 ⟨?_, ?_, ?_⟩ <;> simp
  · simp
  · simp [hm r]
  · refine ⟨-1, ?_⟩
    ext i
    fin_cases i <;> simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, hm r]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.HtLawCongr
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.K4
open scoped Matrix MatrixGroups

namespace UpperTheory.V.Z.Kato.Joint

theorem htLaw_congr {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime] {A : ValuationSubring Ω} {c : Coef l}
    {Z : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l} {j : Ω →+* Qbar l} {m₀ c₀ : ℕ}
    {R R' : ∀ m : ℕ, DirichletCharacter (Qbar l) (l ^ m) → Qbar l → Qbar l} (h : HTLawCsOfCoef A c Z j m₀ c₀ R)
    (hR : ∀ m, 1 ≤ m → ∀ ψ z, R m ψ z = R' m ψ z) : HTLawCsOfCoef A c Z j (max m₀ 1) c₀ R' := by
  obtain ⟨ζ, hζ, hm⟩ := h
  refine ⟨ζ, hζ, fun m hm1 => ?_⟩
  obtain ⟨ι, x, P, o, hP, hψ⟩ := hm m (le_trans (le_max_left _ _) hm1)
  refine ⟨ι, x, P, o, hP, fun ψ hprim => ?_⟩
  rw [← hR m (le_trans (le_max_right _ _) hm1)]
  exact hψ ψ hprim

end UpperTheory.V.Z.Kato.Joint

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.LamEig2
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.CyclotomicQExpansion GlobalTheory.KummerEisensteinGalois GlobalTheory.K4 GlobalTheory.LambdaValuationPowers
open scoped Matrix MatrixGroups TensorProduct

namespace UpperTheory.V.Z.Kato.Joint

def LamEig2 : Prop := ThLin → ThOp → ChiStab → ThP →
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε)
    (A : ValuationSubring Ω) (N w : ℕ) (j : Ω →+* Qbar l) (χ : ℕ → ℤ_[l]) (ev : Letter → Qbar l), Std A N w j →
    (∃ k : ℕ, ∀ T, GlobalTheory.KZ.admitted N l T → ‖ev T‖ ≤ (l : ℝ) ^ k) → ∀ P ∈ admissibleLettersSubalgebra (Qbar l) N l,
    (∀ T, GlobalTheory.KZ.admitted N l T → ∀ b ∈ X.B N l w,
      FreeAlgebra.lift (Qbar l) (X.opV N l (Qbar l)) P ((1 : Qbar l) ⊗ₜ[ℤ_[l]] X.op N l T b) =
        ev T • FreeAlgebra.lift (Qbar l) (X.opV N l (Qbar l)) P ((1 : Qbar l) ⊗ₜ[ℤ_[l]] b)) →
    ∀ lam₀ lam : (ℕ → Qbar l) →ₗ[Qbar l] Qbar l, FinSupp lam₀ →
    (∀ a, lam a = lam₀ (FreeAlgebra.lift (Qbar l) (fop (w + 2) l fun d => ((χ d : ℤ_[l]) : Qbar l)) P a)) →
    ∃ c₂ : ℕ, ∀ n, c₂ ≤ n → ∀ (T : Letter) (b : X.Fn l), GlobalTheory.KZ.admitted N l T → InChi X N w χ b →
      Cg (n - c₂) (lam (th X A N j n (X.op N l T b))) (ev T * lam (th X A N j n b))

def AqBd : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ) (S : Finset Pl)
    (A : ValuationSubring Ω) (W : R2 Ω l) (g : Newform (2 * e + 1)) (χ : G ℚ Ω →* (Qbar l)ˣ), Nf e S A W → KillsMu l χ →
    g.Att ι (tw W (cycBar ℚ Ω l ^ (-(e : ℤ)) * (dt W)⁻¹ * χ)) → ∃ k : ℕ, ∀ q : ℕ, q.Prime → ‖ι.symm (g.a q)‖ ≤ (l : ℝ) ^ k

def AdmOf2 : Prop := AdmTop → NewformPartOfTowerModule → AdmRho → JEx → RhoFrob → Unif → FormP → FinP → CoefUb → ThLin → ThOp → ChiStab → ThP → LamEig2 →
  ChiQuad → AqBd → AdmFR

theorem lamEig2 : LamEig2 := by
  intro hLin hOp hStab hP l _ Ω _ _ _ ε X A N w j χ ev hS hev P hPm hEig lam₀ lam hfin hlam
  obtain ⟨k', hev⟩ := hev
  obtain ⟨c, hc⟩ := hP hOp hStab l Ω ε X A N w j χ hS P hPm
  obtain ⟨k, hk⟩ := hfin.exists_loss
  refine ⟨c + k' + k, fun n hn T b hT hb => ?_⟩
  obtain ⟨Θ, hΘ⟩ := hLin l Ω ε X A N w j hS n
  have hTb := hStab l Ω ε X N w χ hS.2.1 hS.2.2.1 hS.2.2.2.1 hS.2.2.2.2.1 T b hT hb
  have h1 := hc n (by omega) Θ hΘ _ hTb
  have h2 := hc n (by omega) Θ hΘ _ hb
  rw [hEig T hT b hb.1, map_smul] at h1
  rw [hlam, hlam, ← smul_eq_mul, ← map_smul, ← Nat.sub_sub, ← Nat.sub_sub]
  refine hk (n - c - k') (by omega) _ _ fun i => ?_
  have h3 := cg_mul_left (k := k') (by omega) (hev T hT) (h2 i)
  have h4 := cg_mono (Nat.sub_le (n - c) k') (h1 i)
  simp only [Pi.smul_apply, smul_eq_mul] at h4 ⊢
  unfold Cg at h3 h4 ⊢
  rw [← norm_neg, neg_sub] at h3
  rw [← sub_add_sub_cancel _ (ev T * Θ (FreeAlgebra.lift (Qbar l) (X.opV N l (Qbar l)) P ((1 : Qbar l) ⊗ₜ[ℤ_[l]] b)) i)]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h4 h3)

end UpperTheory.V.Z.Kato.Joint

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.SumUnits
section
open UpperTheory.V.Z.Kato.Joint

private noncomputable def avg {l : ℕ} [Fact l.Prime] (ι : PadicAlgCl l ≃+* ℂ) (N : ℕ) [NeZero N] (θ : DirichletCharacter ℂ N) (m k : ℕ)
    (ψ : DirichletCharacter (PadicAlgCl l) (l ^ m)) (δ : ℕ → PadicAlgCl l) (a b : ℤ) : ℕ → PadicAlgCl l :=
  fun i => ∑ u : (ZMod N)ˣ, δ (u : ZMod N).val * ser ι N θ m k ψ (((u : ZMod N).val : ℤ) * a) (((u : ZMod N).val : ℤ) * b) i

private theorem expand {l : ℕ} [Fact l.Prime] (ι : PadicAlgCl l ≃+* ℂ) (N : ℕ) [NeZero N] (θ : DirichletCharacter ℂ N) (m k : ℕ)
    (ψ : DirichletCharacter (PadicAlgCl l) (l ^ m)) (δ : ℕ → PadicAlgCl l) (c d : ℤ) :
    (GlobalTheory.KummerEisensteinGalois.up (l ^ m) fun i => ∑ x : ZMod N, ι.symm (GlobalTheory.EisM.hat θ (x.val : ℤ) / 2) *
                 GlobalTheory.LambdaValuationPowers.chiProj N l m k ψ δ c d (x.val : ℤ) i) =
      ((c : PadicAlgCl l) ^ 2 * (d : PadicAlgCl l) ^ 2) • avg ι N θ m k ψ δ 1 1
      - ((c : PadicAlgCl l) ^ ((3 : ℤ) - k) * ψ⁻¹ (c : ZMod (l ^ m)) * (d : PadicAlgCl l) ^ 2) • avg ι N θ m k ψ δ c 1
      - ((c : PadicAlgCl l) ^ 2 * (d : PadicAlgCl l) * ψ⁻¹ (d : ZMod (l ^ m))) • avg ι N θ m k ψ δ 1 d
      + ((c : PadicAlgCl l) ^ ((3 : ℤ) - k) * ψ⁻¹ (c : ZMod (l ^ m)) * (d : PadicAlgCl l) * ψ⁻¹ (d : ZMod (l ^ m))) •
          avg ι N θ m k ψ δ c d := by
  funext i
  simp only [GlobalTheory.KummerEisensteinGalois.up, avg, ser, GlobalTheory.LambdaValuationPowers.chiProj, GlobalTheory.LambdaValuationPowers.coPtSb, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum, mul_one]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun x _ => ?_
  rw [show c * ((x.val : ℤ) * ((u : ZMod N).val : ℤ)) = (x.val : ℤ) * (((u : ZMod N).val : ℤ) * c) by ring,
    mul_comm d ((u : ZMod N).val : ℤ)]
  ring

private theorem sum_units {K : Type} [Field K] (n : ℕ) [NeZero n] (ψ : DirichletCharacter K n) (f : ZMod n → K) :
    ∑ a : ZMod n, ψ a * f a = ∑ b : (ZMod n)ˣ, ψ b * f b := by
  classical
  symm
  refine Finset.sum_bij_ne_zero (fun b _ _ => (b : ZMod n)) (fun _ _ _ => Finset.mem_univ _)
    (fun a _ _ b _ _ h => Units.ext h) (fun a _ h => ?_) (fun _ _ _ => rfl)
  have ha : IsUnit a := by
    by_contra hn
    exact h (by rw [MulChar.map_nonunit _ hn, zero_mul])
  obtain ⟨b, rfl⟩ := ha
  exact ⟨b, Finset.mem_univ _, h, rfl⟩

private theorem cop_unit (N : ℕ) [NeZero N] (u : (ZMod N)ˣ) (a : ℤ) (ha : IsCoprime a N) :
    IsCoprime (((u : ZMod N).val : ℤ) * a) N :=
  (Nat.isCoprime_iff_coprime.2 (ZMod.val_coe_unit_coprime u)).mul_left ha

theorem UpperTheory.V.Z.Kato.Joint.rhsEq :
    UpperTheory.V.Z.Kato.Joint.RhsEq := by
  intro hE hM l _ ι e N _ θ χ t α B cc c d δ lam κ' κ v hl he hlN hχ hα hc hd hEig hδ hlam m hm ψ z
  have hk3 : 3 ≤ 2 * e + 1 := by omega
  have hodd : Odd (2 * e + 1) := ⟨e, rfl⟩
  have hc' : IsCoprime (c : ℤ) N := Nat.isCoprime_iff_coprime.2 hc
  have hd' : IsCoprime (d : ℤ) N := Nat.isCoprime_iff_coprime.2 hd
  have h1 : IsCoprime (1 : ℤ) N := isCoprime_one_left
  unfold rhs5
  rw [expand ι N θ m (2 * e + 1) ψ δ c d]
  split_ifs with hpar
  · have hpar' : ι (ψ (-1)) = θ (-1) := by rw [hpar, RingEquiv.apply_symm_apply]
    have hf : ∀ y : ZMod (l ^ m), ι (ψ (-y)) = θ (-1) * ι (ψ y) := fun y => by
      rw [← hpar', ← map_mul, ← map_mul, neg_one_mul]
    obtain ⟨hMF, hval⟩ := hM (2 * e + 1) l N m θ χ (fun y => ι (ψ y)) t α B cc Fact.out hk3 hodd (NeZero.pos N) hlN hm hχ hf hα hEig
    set F := frm l N m (2 * e + 1) θ (θ * χ) (fun y => ι (ψ y)) with hF
    set μ := GlobalTheory.EisM.mesMu (2 * e + 1) l (GlobalTheory.EisM.hat θ) (GlobalTheory.EisM.tw2 N (θ (-1))) α B cc m (fun y => ι (ψ y)) with hμ
    have hG : (fun i => ι ((fun i => ι.symm (F i)) i)) = F := by
      funext i; simp
    have hlG : 2 * lam (fun i => ι.symm (F i)) = κ' * (N.totient : PadicAlgCl l) * ι.symm α ^ m * ι.symm μ := by
      have h2 := congrArg ι.symm hval
      rw [map_mul, map_mul, map_mul, map_pow, map_natCast, map_ofNat] at h2
      rw [hlam _ (by rw [hG]; exact hMF), hG]
      linear_combination κ' * h2
    have hav : ∀ a b : ℤ, IsCoprime a N → IsCoprime b N → lam (avg ι N θ m (2 * e + 1) ψ δ a b) =
        ι.symm (θ (a : ZMod N)) * ι.symm ((θ * χ)⁻¹ (b : ZMod N)) *
          (κ' * (N.totient : PadicAlgCl l) * ι.symm α ^ m * ι.symm μ) := by
      intro a b ha hb
      have h3 := (hE l ι N θ χ m (2 * e + 1) ψ a b hl hm hk3 hodd hχ ha hb).2.2 hpar'
      have : avg ι N θ m (2 * e + 1) ψ δ a b =
          (2 * ι.symm (θ (a : ZMod N)) * ι.symm ((θ * χ)⁻¹ (b : ZMod N))) • fun i => ι.symm (F i) := by
        funext i
        apply ι.injective
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [avg, Pi.smul_apply, smul_eq_mul, map_mul, map_sum, RingEquiv.apply_symm_apply, map_ofNat]
        rw [← h3 i]
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [hδ _ (ZMod.val_coe_unit_coprime u), ZMod.natCast_zmod_val]
      rw [this, map_smul, smul_eq_mul, ← hlG]
      ring
    haveI : NeZero (l ^ m) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
    rw [sum_units (l ^ m) ψ (fun a => z ^ a.val)]
    simp only [map_add (f := _), map_sub, map_smul, smul_eq_mul, hav _ _ h1 h1, hav _ _ hc' h1, hav _ _ h1 hd', hav _ _ hc' hd',
      Fin.sum_univ_four, smB, smT, Int.cast_natCast, Int.cast_one, map_one]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
      Matrix.tail_cons, Nat.cast_mul, map_mul]
    ring
  · have hpar' : ι (ψ (-1)) ≠ θ (-1) := fun h => hpar (by rw [← h, RingEquiv.symm_apply_apply])
    have hav : ∀ a b : ℤ, IsCoprime a N → IsCoprime b N → avg ι N θ m (2 * e + 1) ψ δ a b = 0 := by
      intro a b ha hb
      funext i
      refine Finset.sum_eq_zero fun u _ => ?_
      rw [(hE l ι N θ χ m (2 * e + 1) ψ _ _ hl hm hk3 hodd hχ (cop_unit N u a ha) (cop_unit N u b hb)).1 hpar']
      simp
    rw [hav _ _ h1 h1, hav _ _ hc' h1, hav _ _ h1 hd', hav _ _ hc' hd']
    simp
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.TowerEx
section
open UpperTheory.V.Z.Kato.Joint

theorem UpperTheory.V.Z.Kato.Joint.towerEx :
    UpperTheory.V.Z.Kato.Joint.TowerEx := by
  intro Ω _ _ _ ε
  obtain ⟨T, -⟩ := _root_.GlobalTheory.FN.tower_exists Ω ε
  exact ⟨T⟩
end

