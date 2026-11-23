module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ResPlaneSmulEqZero
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0355
public import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0347
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0351
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0009

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ReducedSelmerCochainMemContinuousCocyclesOfCont
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

noncomputable section

namespace GlobalTheory.Ord2.ResidualCocycleReduction

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]

theorem redL_add_l_mul (c : Coef l) {x d : Qbar l} (hx : x ∈ c.O) (hd : d ∈ c.O) :
    redL c (x + (l : Qbar l) * d) = redL c x := by
  rw [redL_add c hx (c.O.mul_mem (c.O.natCast_mem l) hd),
    (redL_eq_zero_iff c (c.O.mul_mem (c.O.natCast_mem l) hd)).2 ⟨d, hd, rfl⟩, add_zero]

theorem redL_mulVec (c : Coef l) (M : Matrix (Fin 2) (Fin 2) (Qbar l)) (v : Fin 2 → Qbar l)
    (hM : ∀ i j, M i j ∈ c.O) (hv : ∀ j, v j ∈ c.O) (i : Fin 2) :
    redL c ((M *ᵥ v) i) = ((fun i j => redL c (M i j)) *ᵥ (fun j => redL c (v j))) i := by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  rw [redL_add c (c.O.mul_mem (hM _ _) (hv _)) (c.O.mul_mem (hM _ _) (hv _)),
    redL_mul c (hM _ _) (hv _), redL_mul c (hM _ _) (hv _)]

theorem mulVec_mem (c : Coef l) (M : Matrix (Fin 2) (Fin 2) (Qbar l)) (v : Fin 2 → Qbar l)
    (hM : ∀ i j, M i j ∈ c.O) (hv : ∀ j, v j ∈ c.O) (i : Fin 2) : (M *ᵥ v) i ∈ c.O := by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  exact c.O.add_mem (c.O.mul_mem (hM _ _) (hv _)) (c.O.mul_mem (hM _ _) (hv _))

theorem resCoc_mul (c : Coef l) (W : R2 Ω l) (S : Finset Pl) (A : ValuationSubring Ω)
    (hO : ∀ s i j, mat W s i j ∈ c.O)
    {z : G ℚ Ω → Fin 2 → Qbar l} (hz : z ∈ divSelCoc c W S A) (y : Fin 2 → Qbar l)
    (hzy : ∀ s i, (l : Qbar l) * z s i - (mat W s *ᵥ y - y) i ∈ c.O) (s t : G ℚ Ω) :
    resCoc c W z y (s * t) = resCoc c W z y s + resAct c W hO s (resCoc c W z y t) := by
  obtain ⟨-, h2, -, -, -, -⟩ := hz
  funext i
  have hM : mat W (s * t) = mat W s * mat W t := by simp only [mat, map_mul, Units.val_mul]
  set a : G ℚ Ω → Fin 2 → Qbar l := fun s i => (l : Qbar l) * z s i - (mat W s *ᵥ y - y) i with ha
  have e : (l : Qbar l) * z (s * t) i - (mat W (s * t) *ᵥ y - y) i =
      (a s i + (mat W s *ᵥ a t) i) + (l : Qbar l) * (z (s * t) i - z s i - (mat W s *ᵥ z t) i) := by
    have ea : a t = (l : Qbar l) • z t - (mat W t *ᵥ y - y) := by
      funext j; simp only [ha, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [hM, ea, ← Matrix.mulVec_mulVec]
    simp only [ha, Matrix.mulVec_sub, Matrix.mulVec_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hat : ∀ j, a t j ∈ c.O := fun j => hzy t j
  show redL c _ = redL c (a s i) + (wRed c W s *ᵥ (fun j => redL c (a t j))) i
  rw [e, redL_add_l_mul c (c.O.add_mem (hzy s i) (mulVec_mem c _ _ (hO s) hat i)) (h2 s t i),
    redL_add c (hzy s i) (mulVec_mem c _ _ (hO s) hat i), redL_mulVec c _ _ (hO s) hat i]
  rfl

theorem resCoc_locConst (c : Coef l) (W : R2 Ω l) (S : Finset Pl) (A : ValuationSubring Ω)
    (hlc : ∀ (n : ℕ) (s : G ℚ Ω), ∀ᶠ t in nhds s, ∀ i j, ∃ o ∈ c.O, mat W t i j - mat W s i j = (l : Qbar l) ^ n * o)
    {z : G ℚ Ω → Fin 2 → Qbar l} (hz : z ∈ divSelCoc c W S A) {y : Fin 2 → Qbar l} (hy : VecE c y)
    (hzy : ∀ s i, (l : Qbar l) * z s i - (mat W s *ᵥ y - y) i ∈ c.O) :
    IsLocallyConstant (resCoc c W z y) := by
  obtain ⟨-, -, h3, -, -, -⟩ := hz
  obtain ⟨k, hk⟩ := hy
  refine (IsLocallyConstant.iff_eventually_eq _).2 fun s => ?_
  filter_upwards [h3 s, hlc (k + 1) s] with t ht hW
  funext i
  choose o ho he using hW
  have e : (l : Qbar l) * z t i - (mat W t *ᵥ y - y) i =
      ((l : Qbar l) * z s i - (mat W s *ᵥ y - y) i) + (l : Qbar l) *
        ((z t i - z s i) - (o i 0 * ((l : Qbar l) ^ k * y 0) + o i 1 * ((l : Qbar l) ^ k * y 1))) := by
    have h0 : mat W t i 0 = mat W s i 0 + (l : Qbar l) ^ (k + 1) * o i 0 := by rw [← he i 0]; ring
    have h1 : mat W t i 1 = mat W s i 1 + (l : Qbar l) ^ (k + 1) * o i 1 := by rw [← he i 1]; ring
    simp only [Pi.sub_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    rw [h0, h1]; ring
  show redL c _ = redL c _
  rw [e, redL_add_l_mul c (hzy s i) (c.O.sub_mem (ht i) (c.O.add_mem (c.O.mul_mem (ho i 0) (hk 0))
    (c.O.mul_mem (ho i 1) (hk 1))))]

theorem reduced_selmer_cochain_mem_continuous_cocycles_S (c : Coef l) (W : R2 Ω l) (S : Finset Pl) (A : ValuationSubring Ω)
    (hO : ∀ s i j, mat W s i j ∈ c.O) (hN : ∀ a ∈ (toGS Ω (S : Set Pl)).ker, W a = 1)
    (hlc : ∀ (n : ℕ) (s : G ℚ Ω), ∀ᶠ t in nhds s, ∀ i j, ∃ o ∈ c.O, mat W t i j - mat W s i j = (l : Qbar l) ^ n * o)
    {z : G ℚ Ω → Fin 2 → Qbar l} (hz : z ∈ divSelCoc c W S A) {y : Fin 2 → Qbar l} (hy : VecE c y)
    (hzy : ∀ s i, (l : Qbar l) * z s i - (mat W s *ᵥ y - y) i ∈ c.O) :
    descS S (resCoc c W z y) ∈ Z1 (resRep c W hO S hN) := by
  have hd : ∀ s, descS S (resCoc c W z y) (toGS Ω (S : Set Pl) s) = resCoc c W z y s :=
    descS_resCoc_toGS c W S A hO hN hz y hzy
  refine ⟨?_, fun g h => ?_⟩
  · rw [(QuotientGroup.isQuotientMap_mk (NS Ω (S : Set Pl))).continuous_iff]
    have : descS S (resCoc c W z y) ∘ (QuotientGroup.mk : G ℚ Ω → GS Ω (S : Set Pl)) = resCoc c W z y :=
      funext fun s => hd s
    rw [this]
    exact (resCoc_locConst c W S A hlc hz hy hzy).continuous
  · obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective g
    obtain ⟨t, rfl⟩ := QuotientGroup.mk_surjective h
    have e1 : ((s : GS Ω (S : Set Pl)) * (t : GS Ω (S : Set Pl))) = toGS Ω (S : Set Pl) (s * t) := rfl
    have e2 : (s : GS Ω (S : Set Pl)) = toGS Ω (S : Set Pl) s := rfl
    have e3 : (t : GS Ω (S : Set Pl)) = toGS Ω (S : Set Pl) t := rfl
    rw [e1, e2, e3, hd, hd, hd, resRep_toGS]
    exact resCoc_mul c W S A hO hz y hzy s t

theorem _root_.GlobalTheory.Ord2.descS_resCoc_mem_z1_of_continuous : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (S : Finset Pl)
    (A : ValuationSubring Ω) (W : R2 Ω l) (c : Coef l) (hO : ∀ s i j, mat W s i j ∈ c.O)
    (hN : ∀ a ∈ (toGS Ω (S : Set Pl)).ker, W a = 1), Continuous W → ∀ z ∈ divSelCoc c W S A,
    ∀ y : Fin 2 → Qbar l, VecE c y → (∀ s i, (l : Qbar l) * z s i - (mat W s *ᵥ y - y) i ∈ c.O) →
    descS S (resCoc c W z y) ∈ Z1 (resRep c W hO S hN) := by
  intro l _ Ω _ _ S A W c hO hN hW z hz y hy hzy
  exact GlobalTheory.Ord2.ResidualCocycleReduction.reduced_selmer_cochain_mem_continuous_cocycles_S c W S A hO hN (_root_.GlobalTheory.Ord2.locConst_mod_pow l Ω c W hW hO) hz hy hzy

end GlobalTheory.Ord2.ResidualCocycleReduction
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TameCochainCocycleExtension
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.BrTame

variable {l : ℕ} [Fact l.Prime]

def ballSub (r : ℝ) (hr : 0 ≤ r) : AddSubgroup (PadicAlgCl l) where
  carrier := {x | ‖x‖ ≤ r}
  zero_mem' := by simpa using hr
  add_mem' := fun {a b} ha hb => (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
  neg_mem' := fun {a} ha => by simpa [Set.mem_setOf_eq, norm_neg] using ha

theorem mem_ballSub {r : ℝ} {hr : 0 ≤ r} {x : PadicAlgCl l} : x ∈ ballSub r hr ↔ ‖x‖ ≤ r := Iff.rfl

theorem cg_iff {n : ℕ} {a b : Qbar l} : Cg n a b ↔ a - b ∈ ballSub (l := l) ‖((l : ℕ) : Qbar l) ^ n‖ (norm_nonneg _) := Iff.rfl

theorem mul_mem_ballSub {r : ℝ} {hr : 0 ≤ r} {k x : PadicAlgCl l} (hk : ‖k‖ ≤ 1) (hx : x ∈ ballSub r hr) :
    k * x ∈ ballSub r hr := by
  rw [mem_ballSub, norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) hk).trans hx

theorem norm_le_one_of_int (x : PadicAlgCl l) (hx : IsIntegral ℤ_[l] x) : ‖x‖ ≤ 1 := by
  first
  | exact @_root_.GlobalTheory.IntegralNormLeOne.norm_le_one_of_isIntegral
  | exact _root_.GlobalTheory.IntegralNormLeOne.norm_le_one_of_isIntegral
  | (apply _root_.GlobalTheory.IntegralNormLeOne.norm_le_one_of_isIntegral <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntegralNormLeOne.norm_le_one_of_isIntegral <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntegralNormLeOne.norm_le_one_of_isIntegral <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntegralNormLeOne.norm_le_one_of_isIntegral ..)

theorem norm_le_one_of_mem (c : Coef l) {x : Qbar l} (hx : x ∈ c.O) : ‖x‖ ≤ 1 :=
  norm_le_one_of_int x ((Algebra.IsIntegral.isIntegral (R := ℤ_[l]) (⟨x, hx⟩ : c.O)).map c.O.val)

end GlobalTheory.BrTame


open GlobalTheory.BrTame in
theorem GlobalTheory.br_tame : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (c : Coef l) (n : ℕ) (w : Pl) (B : ValuationSubring Ω) (ψ : G ℚ Ω →* Multiplicative (ZMod (l ^ n))) (h : G ℚ Ω → Qbar l) (σ : G ℚ Ω), 1 ≤ n → IsPlaceOver B w → l ^ n ∣ normV w - 1 → (∃ τ ∈ Ine (F := ℚ) B, (ψ τ).toAdd = 1) → (∀ s, h s ∈ c.O) → (∀ s ∈ Dec (F := ℚ) B, ∀ t ∈ Dec (F := ℚ) B, Cg n (h (s * t)) (h s + h t)) → (∀ s ∈ Ine (F := ℚ) B, Cg n (h s) 0) → Cob2 c n (Dec (F := ℚ) B) (fun s t => (((ψ s).toAdd.val : ℕ) : Qbar l) * h t) → σ ∈ Dec (F := ℚ) B → Cg n (h σ) 0 := by
  intro l _ Ω _ _ _ c n w B ψ h σ hn hB hdiv ⟨τ, hτ, hψτ⟩ hO _ hIne ⟨u, hucont, huO, hu⟩ hσ
  set S := ballSub (l := l) ‖((l : ℕ) : Qbar l) ^ n‖ (norm_nonneg _) with hS
  have hu1 : ∀ s, ‖u s‖ ≤ 1 := fun s => norm_le_one_of_mem c (huO s)
  have heps : ∀ s ∈ Dec (F := ℚ) B, eps l s - 1 ∈ S := fun s hs => GlobalTheory.T.cyclotomicChar_congruent_one_on_decompositionGroup l Ω n w B hB hdiv hn s hs
  have hnat : ∀ k : ℕ, ‖((k : ℕ) : Qbar l)‖ ≤ 1 := fun k => IsUltrametricDist.norm_natCast_le_one _ k
  have hmul : ∀ k x : Qbar l, ‖k‖ ≤ 1 → x ∈ S → k * x ∈ S := fun k x hk hx => mul_mem_ballSub hk hx
  have hIne' : ∀ s ∈ Ine (F := ℚ) B, h s ∈ S := fun s hs => by
    have := cg_iff.1 (hIne s hs)
    rwa [sub_zero] at this
  have hIneDec : ∀ s ∈ Ine (F := ℚ) B, s ∈ Dec (F := ℚ) B := fun s hs => Ine_le_Dec B hs

  set T := ballSub (l := l) 1 zero_le_one with hT
  let M := T ⧸ S.comap T.subtype
  let f : G ℚ Ω → M := fun s => QuotientAddGroup.mk ⟨u s, hu1 s⟩
  have hf : ∀ s t, f s = f t ↔ u s - u t ∈ S := fun s t => by
    show (QuotientAddGroup.mk _ : M) = QuotientAddGroup.mk _ ↔ _
    rw [QuotientAddGroup.eq, AddSubgroup.mem_comap]
    change -u s + u t ∈ S ↔ _
    have e : -u s + u t = -(u s - u t) := by ring
    rw [e, S.neg_mem_iff]
  have hlpos : 0 < ‖((l : ℕ) : Qbar l) ^ n‖ := norm_pos_iff.2 (pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero))
  have htors : ∀ x : M, l ^ n • x = 0 := by
    intro x
    induction x using QuotientAddGroup.induction_on with
    | H y =>
      rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_comap, AddSubgroup.coe_subtype,
        AddSubgroup.coe_nsmul, nsmul_eq_mul, mem_ballSub, norm_mul, Nat.cast_pow]
      exact mul_le_of_le_one_right (norm_nonneg _) y.2
  have hloc : IsLocallyConstant (fun s : Ine (F := ℚ) B => f s) := by
    rw [IsLocallyConstant.iff_exists_open]
    intro x
    have hc : Continuous (fun s : Ine (F := ℚ) B => u s) :=
      (hucont.mono (fun s hs => hIneDec s hs)).comp_continuous continuous_subtype_val (fun s => s.2)
    refine ⟨(fun s : Ine (F := ℚ) B => u s) ⁻¹' Metric.ball (u x) ‖((l : ℕ) : Qbar l) ^ n‖,
      Metric.isOpen_ball.preimage hc, Metric.mem_ball_self hlpos, fun y hy => ?_⟩
    rw [hf, mem_ballSub]
    have := Metric.mem_ball.1 hy
    rw [dist_eq_norm] at this
    exact this.le
  have hadd : ∀ s ∈ Ine (F := ℚ) B, ∀ t ∈ Ine (F := ℚ) B, f (s * t) = f s + f t := by
    intro s hs t ht
    have e : f s + f t = QuotientAddGroup.mk (⟨u s, hu1 s⟩ + ⟨u t, hu1 t⟩ : T) := rfl
    rw [e]
    show (QuotientAddGroup.mk _ : M) = QuotientAddGroup.mk _
    rw [QuotientAddGroup.eq, AddSubgroup.mem_comap]
    change -u (s * t) + (u s + u t) ∈ S
    have h1 := hu s (hIneDec s hs) t (hIneDec t ht)
    have h2 := hmul _ _ (hnat ((ψ s).toAdd.val)) (hIne' t ht)
    have h3 := hmul _ _ (hu1 t) (heps s (hIneDec s hs))
    rw [cg_iff] at h1
    have e2 : -u (s * t) + (u s + u t) =
        -((((ψ s).toAdd.val : ℕ) : Qbar l) * h t - (eps l s * u t - u (s * t) + u s))
          + (((ψ s).toAdd.val : ℕ) : Qbar l) * h t - u t * (eps l s - 1) := by ring
    rw [e2]
    exact S.sub_mem (S.add_mem (S.neg_mem h1) h2) h3
  have hconj := GlobalTheory.T.inertiaTorsionQuotient_conj_invariant_decomposition l Ω n w B M f hB hdiv hn htors hloc hadd σ hσ τ hτ
  rw [hf] at hconj
  set τ' := σ * τ * σ⁻¹ with hτ'
  have hτ'I : τ' ∈ Ine (F := ℚ) B := conj_mem_Ine hσ hτ
  have hprod : τ' * σ = σ * τ := by rw [hτ']; group
  have hψ' : ((ψ τ').toAdd.val : Qbar l) = 1 := by
    have e : ψ τ' = ψ τ := by rw [hτ', map_mul, map_mul, mul_comm (ψ σ), mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]
    have hl1 : 1 < l ^ n := Nat.one_lt_pow (by omega) (Fact.out : l.Prime).one_lt
    rw [e, hψτ, ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt hl1, Nat.cast_one]
  have hA := hu τ' (hIneDec τ' hτ'I) σ hσ
  have hB' := hu σ hσ τ (hIneDec τ hτ)
  dsimp only at hA hB'
  rw [cg_iff, hprod, hψ', one_mul] at hA
  rw [cg_iff] at hB'
  have hC := hmul _ _ (hnat ((ψ σ).toAdd.val)) (hIne' τ hτ)
  have hD := hmul _ _ (hu1 σ) (heps τ' (hIneDec τ' hτ'I))
  have hF := hmul _ _ (hu1 τ) (heps σ hσ)
  rw [cg_iff, sub_zero]
  have e : h σ = (h σ - (eps l τ' * u σ - u (σ * τ) + u τ')) + u σ * (eps l τ' - 1) + (u τ' - u τ)
      - ((((ψ σ).toAdd.val : ℕ) : Qbar l) * h τ - (eps l σ * u τ - u (σ * τ) + u σ))
      + (((ψ σ).toAdd.val : ℕ) : Qbar l) * h τ - u τ * (eps l σ - 1) := by ring
  rw [e]
  exact S.sub_mem (S.add_mem (S.sub_mem (S.add_mem (S.add_mem hA hD) hconj) hB') hC) hF
end

