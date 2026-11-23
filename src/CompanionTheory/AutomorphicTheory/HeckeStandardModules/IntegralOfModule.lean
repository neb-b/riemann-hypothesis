module

public import CompanionTheory.AutomorphicTheory.HeckeStandardModules.ExistsDenFin
public import CompanionTheory.AutomorphicTheory.HeckeStandardModules.HeckeA
public import CompanionTheory.AutomorphicTheory.HeckeStandardModules.HeckeStdStatement
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob

@[expose] public section

open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.UG Formalism.L2 CompanionTheory.Split CompanionTheory.HeckeA

noncomputable section

namespace CompanionTheory.L3H

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]

local notation3 "L⁺" => maximalRealSubfield L

section Loc

variable (s : SplitPlace L) (n)

def dg {ϖ : s.v.adicCompletion L⁺} (h0 : ϖ ≠ 0) (k : ℕ) : GL (Fin n) (s.v.adicCompletion L⁺) :=
  ⟨diagJ n ϖ k, Matrix.diagonal fun i => if (i : ℕ) < k then ϖ⁻¹ else 1,
    by rw [diagJ, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext i; split_ifs <;> simp [h0],
    by rw [diagJ, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext i; split_ifs <;> simp [h0]⟩

variable {n}

theorem tSet_iff {ϖ : s.v.adicCompletion L⁺} (h0 : ϖ ≠ 0) (k : ℕ) (x : Formalism.AUTREP.GAf L n) :
    x ∈ Formalism.AUTREP.tSet L n s ϖ k ↔ ∃ h ∈ DoubleCoset.doubleCoset (dg n s h0 k) (KL s n : Set _) (KL s n), emb s n h = x := by
  constructor
  · rintro ⟨hx, a, ha, b, hb, e⟩
    refine ⟨SplitPlace.loc (L := L) s n x, DoubleCoset.mem_doubleCoset.2 ⟨a, ha, b, hb, Units.ext ?_⟩,
      emb_loc s hx⟩
    rw [Units.val_mul, Units.val_mul]
    exact e
  · rintro ⟨h, hh, rfl⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := DoubleCoset.mem_doubleCoset.1 hh
    exact ⟨emb_triv s _, a, ha, b, hb, by rw [loc_emb]; rfl⟩

theorem triv_compl {B : Set (HeightOneSpectrum (𝓞 L⁺))} (hs : s.v ∉ B) {x : Formalism.AUTREP.GAf L n}
    (hx : TrivOutside (L := L) {s.v} x) : TrivOutside (L := L) Bᶜ x :=
  fun w hw => hx w fun h => hw (by rw [Set.mem_singleton_iff.1 h]; exact hs)

variable {s}

theorem emb_mem_J {J : Subgroup (Formalism.AUTREP.GAf L n)} {χ : J →* ℂˣ} {B : Set (HeightOneSpectrum (𝓞 L⁺))}
    (hJ : NG.HypOutside J χ B) (hs : s.v ∉ B) (h : GL (Fin n) (s.v.adicCompletion L⁺)) :
    emb s n h ∈ J ↔ h ∈ KL s n := by
  rw [(hJ _ (triv_compl s hs (emb_triv s h))).1, mem_Umax_iff s (emb_triv s h), loc_emb]

theorem chi_emb {J : Subgroup (Formalism.AUTREP.GAf L n)} {χ : J →* ℂˣ} {B : Set (HeightOneSpectrum (𝓞 L⁺))}
    (hJ : NG.HypOutside J χ B) (hs : s.v ∉ B) {h : GL (Fin n) (s.v.adicCompletion L⁺)} (hm : emb s n h ∈ J) :
    χ ⟨_, hm⟩ = 1 := (hJ _ (triv_compl s hs (emb_triv s h))).2 hm

end Loc

section TypeSp

variable {ρ : Representation ℂ (GQ L n) W} {J : Subgroup (Formalism.AUTREP.GAf L n)} {χ : J →* ℂˣ}
  {B : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))} {s : SplitPlace L}

theorem inv_of_mem (hJ : NG.HypOutside J χ B) (hs : s.v ∉ B) {f : Formalism.AUTREP.GAf L n → W} (hf : f ∈ NG.TypeSp ρ J χ) :
    Inv (emb s n) (KL s n) f := fun g k hk => by
  have hm := (emb_mem_J hJ hs k).2 hk
  have h2 := congrFun (hf.2 ⟨_, hm⟩) g
  rw [chi_emb hJ hs hm, Units.val_one, one_smul] at h2
  exact h2

theorem heckeD_eq (hJ : NG.HypOutside J χ B) (hs : s.v ∉ B) {f : Formalism.AUTREP.GAf L n → W} (hf : Inv (emb s n) (KL s n) f)
    (d : GL (Fin n) (s.v.adicCompletion L⁺)) {D : Set (Formalism.AUTREP.GAf L n)}
    (hD : ∀ x, x ∈ D ↔ ∃ h ∈ DoubleCoset.doubleCoset d (KL s n : Set _) (KL s n), emb s n h = x) :
    NG.heckeD J D f = op (emb s n) (KL s n) (dosetInd ℂ (KL s n) d) f :=
  funext fun g => coset_sum_eq (emb s n) (KL s n) J (emb_mem_J hJ hs) d hf g hD

theorem comm_KL (s : SplitPlace L) : IsCommensurated (KL s n) := Final.GLintComm L⁺ s.v n

theorem dosetInd_mem (s : SplitPlace L) (d : GL (Fin n) (s.v.adicCompletion L⁺)) : dosetInd ℂ (KL s n) d ∈ Hecke ℂ (KL s n) :=
  Final.DosetIndMem _ _ ℂ d

theorem op_equiv (hJ : NG.HypOutside J χ B) (hs : s.v ∉ B) (hϖ : ∃ ϖ : s.v.adicCompletion L⁺, Valued.v ϖ = WithZero.exp (-1 : ℤ))
    {f : Formalism.AUTREP.GAf L n → W} (hf : f ∈ NG.TypeSp ρ J χ) (d : GL (Fin n) (s.v.adicCompletion L⁺)) (κ : J) (g) :
    op (emb s n) (KL s n) (dosetInd ℂ (KL s n) d) f (g * κ) = ((χ κ : ℂˣ) : ℂ) • op (emb s n) (KL s n) (dosetInd ℂ (KL s n) d) f g := by
  obtain ⟨ϖ, hϖ⟩ := hϖ
  let t := SplitPlace.loc (L := L) s n κ
  have hk : ∀ k ∈ KL s n, t * k * t⁻¹ ∈ KL s n := fun k hk => by
    refine (emb_mem_J hJ hs _).1 ?_
    rw [show t = SplitPlace.loc (L := L) s n κ from rfl, ← conj_emb]
    exact J.mul_mem (J.mul_mem κ.2 ((emb_mem_J hJ hs k).2 hk)) (J.inv_mem κ.2)
  have hconj : ∃ u ∈ KL s n, ∀ h, t * h * t⁻¹ = u * h * u⁻¹ := by
    have hϖO : ϖ ∈ Ov L⁺ s.v := by
      change Valued.v ϖ ≤ 1
      rw [hϖ, ← WithZero.exp_zero, WithZero.exp_le_exp]
      norm_num
    obtain ⟨a, -, k₁, h₁, k₂, h₂, e⟩ := Final.CartanDecomp L⁺ s.v n ϖ hϖO hϖ t
    obtain ⟨D, ht⟩ : ∃ D, t = k₁ * D * k₂ := ⟨k₁⁻¹ * t * k₂⁻¹, by group⟩
    rw [ht] at e hk ⊢
    have hD : (D : Matrix (Fin n) (Fin n) (s.v.adicCompletion L⁺)) = diagPow L⁺ s.v ϖ a := by
      rw [Units.val_mul, Units.val_mul] at e
      exact (Units.mul_right_inj k₁).1 ((Units.mul_left_inj k₂).1 e)
    have hle : ∀ i j, a j ≤ a i := fun i j => by
      rcases eq_or_ne i j with rfl | hij
      · exact le_rfl
      let E : GL (Fin n) (s.v.adicCompletion L⁺) := ⟨Matrix.transvection i j 1, Matrix.transvection i j (-1),
        by rw [Matrix.transvection_mul_transvection_same i j hij, add_neg_cancel, Matrix.transvection_zero],
        by rw [Matrix.transvection_mul_transvection_same i j hij, neg_add_cancel, Matrix.transvection_zero]⟩
      have hE (c : s.v.adicCompletion L⁺) (hc : Valued.v c ≤ 1) (p q : Fin n) :
          Valued.v (Matrix.transvection i j c p q) ≤ 1 := by
        rw [Matrix.transvection, Matrix.add_apply]
        refine (Valuation.map_add _ _ _).trans (max_le ?_ ?_)
        · rw [Matrix.one_apply]; split_ifs <;> simp
        · rw [Matrix.single_apply]; split_ifs <;> simp [hc]
      have hEK : E ∈ KL s n := (mem_KL s).2 ⟨hE 1 (by simp), hE (-1) (by simp)⟩
      have hM : D * E * D⁻¹ ∈ KL s n := by
        have hm := (KL s n).mul_mem ((KL s n).mul_mem ((KL s n).inv_mem h₁)
          (hk _ ((KL s n).mul_mem ((KL s n).mul_mem ((KL s n).inv_mem h₂) hEK) h₂))) h₁
        rwa [show k₁⁻¹ * (k₁ * D * k₂ * (k₂⁻¹ * E * k₂) * (k₁ * D * k₂)⁻¹) * k₁ =
          D * E * D⁻¹ by group] at hm
      have hval := ((mem_KL s).1 hM).1 i j
      have hmul : (D * E * D⁻¹).val * D.val = D.val * E.val :=
        congrArg Units.val (show D * E * D⁻¹ * D = D * E by group)
      have hentry := congrArg (fun M : Matrix (Fin n) (Fin n) (s.v.adicCompletion L⁺) => M i j) hmul
      simp only [hD, diagPow, Matrix.mul_diagonal, Matrix.diagonal_mul] at hentry
      have hEij : (E : Matrix (Fin n) (Fin n) (s.v.adicCompletion L⁺)) i j = 1 := by
        simp [E, Matrix.transvection, hij]
      have hpow := mul_le_mul_left hval (Valued.v (ϖ ^ a j))
      rw [← map_mul, hentry, hEij, mul_one, one_mul, map_zpow₀, map_zpow₀, hϖ,
        ← WithZero.exp_zsmul, ← WithZero.exp_zsmul, WithZero.exp_le_exp] at hpow
      simpa using hpow
    have hcentral : ∀ h, D * h = h * D := fun h => Units.ext (Matrix.ext fun i j => by
      rw [Units.val_mul, Units.val_mul, hD, diagPow, Matrix.mul_diagonal, Matrix.diagonal_mul,
        le_antisymm (hle j i) (hle i j), mul_comm])
    refine ⟨k₁ * k₂, (KL s n).mul_mem h₁ h₂, fun h => ?_⟩
    rw [show k₁ * D * k₂ * h * (k₁ * D * k₂)⁻¹ =
      k₁ * (D * (k₂ * h * k₂⁻¹)) * D⁻¹ * k₁⁻¹ by group, hcentral]
    group
  obtain ⟨u, hu, hcu⟩ := hconj
  exact op_conj (emb s n) (dosetInd_mem s d).1 (inv_of_mem hJ hs hf) hu
    (fun h => by rw [conj_emb]; exact congrArg (emb s n) (hcu h))
    (fun g => congrFun (hf.2 κ) g) (comm_KL s) (dosetInd_mem s d) g

theorem op_mem (hJ : NG.HypOutside J χ B) (hs : s.v ∉ B) (hϖ : ∃ ϖ : s.v.adicCompletion L⁺, Valued.v ϖ = WithZero.exp (-1 : ℤ))
    (hN : ∃ N : ℕ, 0 < N ∧ ∀ κ, NG.Cong L n N κ → ∃ h : κ ∈ J, χ ⟨κ, h⟩ = 1)
    {f : Formalism.AUTREP.GAf L n → W} (hf : f ∈ NG.TypeSp ρ J χ) (d : GL (Fin n) (s.v.adicCompletion L⁺)) :
    op (emb s n) (KL s n) (dosetInd ℂ (KL s n) d) f ∈ NG.TypeSp ρ J χ := by
  obtain ⟨S, hS⟩ := exists_sum (W := W) (emb s n) (comm_KL s) (dosetInd_mem s d)
  obtain ⟨N, hN0, hN⟩ := hN
  refine ⟨⟨fun γ g => ?_, N, hN0, fun κ hκ g => ?_⟩, fun κ => funext fun g => op_equiv hJ hs hϖ hf d κ g⟩
  · set_option synthInstance.maxHeartbeats 100000 in
    rw [hS, hS, map_sum]
    exact Finset.sum_congr rfl fun c _ => by rw [mul_assoc, hf.1.1, map_smul]
  · obtain ⟨hm, h1⟩ := hN κ hκ
    have := op_equiv hJ hs hϖ hf d ⟨κ, hm⟩ g
    rwa [h1, Units.val_one, one_smul] at this

end TypeSp

section Same

variable {J : Subgroup (Formalism.AUTREP.GAf L n)} {χ : J →* ℂˣ} {B : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))}

theorem tSet_same (s s' : SplitPlace L) (hv : s'.v = s.v) {ϖ' : s'.v.adicCompletion L⁺} (h0 : ϖ' ≠ 0) (k : ℕ) :
    ∃ d : GL (Fin n) (s.v.adicCompletion L⁺), ∀ x, x ∈ Formalism.AUTREP.tSet L n s' ϖ' k ↔
      ∃ h ∈ DoubleCoset.doubleCoset d (KL s n : Set _) (KL s n), emb s n h = x := by
  obtain ⟨v, i⟩ := s'
  obtain rfl : v = s.v := hv
  let s' : SplitPlace L := ⟨s.v, i⟩
  have hK : ∀ a ∈ KL s' n, SplitPlace.loc (L := L) s n (emb s' n a) ∈ KL s n := fun a ha =>
    (mem_Umax_iff s (emb_triv s' a)).1 ((mem_Umax_iff s' (emb_triv s' a)).2 (by rwa [loc_emb]))
  have hK' : ∀ a ∈ KL s n, SplitPlace.loc (L := L) s' n (emb s n a) ∈ KL s' n := fun a ha =>
    (mem_Umax_iff s' (emb_triv s a)).1 ((mem_Umax_iff s (emb_triv s a)).2 (by rwa [loc_emb]))
  refine ⟨SplitPlace.loc (L := L) s n (emb s' n (dg n s' h0 k)), fun x => ?_⟩
  rw [tSet_iff s' h0]
  constructor
  · rintro ⟨h, hh, rfl⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := DoubleCoset.mem_doubleCoset.1 hh
    refine ⟨_, DoubleCoset.mem_doubleCoset.2 ⟨_, hK a ha, _, hK b hb, rfl⟩, ?_⟩
    rw [map_mul, map_mul, map_mul, map_mul, emb_loc s (emb_triv s' a), emb_loc s (emb_triv s' _),
      emb_loc s (emb_triv s' b)]
  · rintro ⟨h, hh, rfl⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := DoubleCoset.mem_doubleCoset.1 hh
    refine ⟨SplitPlace.loc (L := L) s' n (emb s n a) * dg n s' h0 k *
        SplitPlace.loc (L := L) s' n (emb s n b),
      DoubleCoset.mem_doubleCoset.2 ⟨_, hK' a ha, _, hK' b hb, rfl⟩, ?_⟩
    rw [map_mul, map_mul, map_mul, map_mul, emb_loc s' (emb_triv s a), emb_loc s' (emb_triv s b),
      emb_loc s (emb_triv s' _)]

end Same

section Int

variable {R : Type} [CommRing R] [Algebra R ℂ]

end Int

end CompanionTheory.L3H
