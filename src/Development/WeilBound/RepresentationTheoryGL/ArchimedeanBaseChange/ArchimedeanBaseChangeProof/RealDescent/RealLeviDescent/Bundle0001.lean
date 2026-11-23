module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.ConeWeightsNotSecondType
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.IsLevPairA
public import Formalism.RealPlaceAnalysis.Bundle0003

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.ExpansionTerms
section
noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate

namespace PositivityTheory.RgBcC.RealD

open PositivityTheory.RgBcC.Real

variable {n : ℕ}

def domC (x : Fin n → ℝ) : Fin n → ℝ := x ∘ Tuple.sort (fun a => -x a)

def spinSq (ν : Fin n → ℝ) : ℝ := nsq (domC (ν - rhoV n) + rhoV n)

def LSq (lam : Fin n → ℤ) : ℝ := nsq fun a => 2 * ((lam a : ℝ) + rhoV n a)


open Classical in
def topTypes (lam : Fin n → ℤ) : Finset (Fin n → ℝ) :=
  (((univ : Finset (Finset (Fin n × Fin n))).filter fun B => ∀ p ∈ B, p.1 < p.2).image fun B =>
    domC ((fun a => 2 * (lam a : ℝ) + 2 * rhoV n a) + rhoV n - wtB B) - rhoV n).filter fun ν => StrictAnti (ν + rhoV n)

def LemmaHT : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℤ), Antitone lam → harmSet lam ⊆ topTypes lam ∧
    ∀ ν ∈ topTypes lam, spinSq ν ≤ LSq lam ∧ (spinSq ν = LSq lam → ν ∈ harmSet lam)

def SecondTypeWeightsShorter : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℤ), Antitone lam → ∀ lev : Fin n → ℕ, IsLev lam lev → ∀ ν, IsSecondTypeWeight lam lev ν →
    ν ∈ topTypes lam ∧ nsq (ν + rhoV n) < nsq (muQ lam lev + rhoV n)

end PositivityTheory.RgBcC.RealD
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.InjectiveDecompositionAction
section
noncomputable section

open Finset

namespace PositivityTheory.RgBcC.RealD

variable {n : ℕ}

def BdSqL : Prop :=
  ∀ (n : ℕ) (S : Lt n → Prop), (∀ l m k : Lt n, S l → S m → l.2.1.2 = m.2.1.1 → k.1 = xor l.1 m.1 →
      k.2.1 = (l.2.1.1, m.2.1.2) → S k) →
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V), IsPairA E1 E2 →
      bdL S E1 E2 * bdL S E1 E2 = 0

def VanKL : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℤ), Antitone lam → ∀ lev : Fin n → ℕ, IsLev lam lev →
    ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V),
      AdmFor lam lev E1 E2 → ∀ (B : Finset (Lt n)) (j : ℕ) (z : Cq n V), B.Nonempty →
        (∀ l ∈ B, l.1 = true ∧ inUU lev l) → PartL B z → DegL j z →
        WtL E1 E2 (muQ lam lev + (2 : ℝ) • rhoV n) z → bdL isK E1 E2 z = 0 →
        ∃ t : Cq n V, PartL B t ∧ DegL (j + 1) t ∧ WtL E1 E2 (muQ lam lev + (2 : ℝ) • rhoV n) t ∧ bdL isK E1 E2 t = z

def InjRL : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℤ), Antitone lam → ∀ lev : Fin n → ℕ, IsLev lam lev →
    ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V),
      AdmFor lam lev E1 E2 → ∀ (u : V) (y : Cq n V), u ∈ hwSp E1 E2 (muQ lam lev) → SuppL (inRR lev) y →
        DegL ((omN n).card + 1) y → bdL (inRR lev) E1 E2 y = Pi.single (omN n) u → u = 0

def InjUU : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℤ), Antitone lam → ∀ lev : Fin n → ℕ, IsLev lam lev →
    ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V),
      AdmFor lam lev E1 E2 → ∀ (u : V) (y : Cq n V), u ∈ hwSp E1 E2 (muQ lam lev) → SuppL (inUU lev) y →
        DegL ((omU lev).card + 1) y → bdL (inUU lev) E1 E2 y = Pi.single (omU lev) u → u = 0

def HCdecL : Prop :=
  ∀ (n : ℕ) (lev : Fin n → ℕ), Monotone lev → ∀ a : FreeAlgebra ℂ (Bool × Fin n × Fin n),
    (∀ (V : Type) [AddCommGroup V] [Module ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V), IsPairA E1 E2 →
      ∀ c d, Commute (kA E1 E2 c d) (evKP E1 E2 a)) →
    ∃ b : FreeAlgebra ℂ (Bool × Fin n × Fin n),
      (∀ (V : Type) [AddCommGroup V] [Module ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V), IsPairA E1 E2 →
        ∀ c d, lev c = lev d → Commute (kA E1 E2 c d) (evLv lev E1 E2 b)) ∧
      ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V), IsPairA E1 E2 →
        ∀ x : V, ∃ w : Lt n → V, evKP E1 E2 a x - evLv lev E1 E2 b x = ∑ l : Lt n, if inUU lev l then xL E1 E2 l (w l) else 0

def HCdecLv : Prop :=
  ∀ (n : ℕ) (lev : Fin n → ℕ), Monotone lev → ∀ a : FreeAlgebra ℂ (Bool × Fin n × Fin n),
    (∀ (V : Type) [AddCommGroup V] [Module ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V), IsPairA E1 E2 →
      ∀ c d, Commute (kA E1 E2 c d) (evKP E1 E2 a)) →
    ∃ b : FreeAlgebra ℂ (Bool × Fin n × Fin n),
      (∀ (H : Type) [AddCommGroup H] [Module ℂ H] (F1 F2 : Fin n → Fin n → Module.End ℂ H), IsLevPairA lev F1 F2 →
        ∀ c d, lev c = lev d → Commute (kA F1 F2 c d) (evLv lev F1 F2 b)) ∧
      ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V), IsPairA E1 E2 →
        ∀ x : V, ∃ w : Lt n → V, evKP E1 E2 a x - evLv lev E1 E2 b x = ∑ l : Lt n, if inUU lev l then xL E1 E2 l (w l) else 0

theorem isLevPairA_of {V : Type} [AddCommGroup V] [Module ℂ V] {E1 E2 : Fin n → Fin n → Module.End ℂ V}
    (h : IsPairA E1 E2) (lev : Fin n → ℕ) : IsLevPairA lev E1 E2 :=
  fun a b c d _ _ => ⟨h.1 a b c d, h.2.1 a b c d, h.2.2 a b c d⟩

theorem hcdecL_of (h : HCdecLv) : HCdecL := by
  intro n lev hlev a ha
  obtain ⟨b, hb, hb'⟩ := h n lev hlev a ha
  exact ⟨b, fun V _ _ E1 E2 hE c d hcd => hb V E1 E2 (isLevPairA_of hE lev) c d hcd, hb'⟩

def ActUU : Prop :=
  ∀ (n : ℕ) (lev : Fin n → ℕ), Monotone lev → ∀ a b : FreeAlgebra ℂ (Bool × Fin n × Fin n),
    (∀ (V : Type) [AddCommGroup V] [Module ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V), IsPairA E1 E2 →
      ∀ c d, Commute (kA E1 E2 c d) (evKP E1 E2 a)) →
    (∀ (V : Type) [AddCommGroup V] [Module ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V), IsPairA E1 E2 →
      ∀ x : V, ∃ w : Lt n → V, evKP E1 E2 a x - evLv lev E1 E2 b x = ∑ l : Lt n, if inUU lev l then xL E1 E2 l (w l) else 0) →
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V), IsPairA E1 E2 →
      ∀ v : V, (∀ l : Lt n, l.1 = false → inUU lev l → xL E1 E2 l v = 0) →
        ∃ w : Cq n V, SuppL (inUU lev) w ∧ DegL ((omU lev).card + 1) w ∧
          Pi.single (omU lev) (evKP E1 E2 a v) - evLc lev E1 E2 b (Pi.single (omU lev) v) = bdL (inUU lev) E1 E2 w

def InjectiveDecompositionAction : Prop := InjUU ∧ HCdecL ∧ ActUU

theorem injective_decomposition_action_of (hB : BdSqL) (hV : VanKL) (hR : BdSqL → VanKL → InjRL) (hU : InjRL → InjUU) (hH : HCdecL) (hA : ActUU) :
    InjectiveDecompositionAction :=
  ⟨hU (hR hB hV), hH, hA⟩

end PositivityTheory.RgBcC.RealD
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.MuQMemHarmSet
section
noncomputable section

open Matrix Finset

namespace PositivityTheory.RgBcC.RealD

open PositivityTheory.RgBcC.Real

variable {n : ℕ}

theorem isLev_id (lam : Fin n → ℤ) : IsLev lam fun a => ((a : Fin n) : ℕ) := ⟨fun _ _ h => h, fun _ _ h => congrArg lam (Fin.ext h)⟩

theorem mem_harmSet {lam : Fin n → ℤ} {μ : Fin n → ℝ} (h : μ ∈ harmSet lam) :
    ∃ l : Fin n → Fin n, IsLev lam (fun a => (l a : ℕ)) ∧ μ = muQ lam fun a => (l a : ℕ) := by
  simp only [harmSet, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at h
  obtain ⟨l, hl, rfl⟩ := h
  exact ⟨l, hl, rfl⟩

theorem muQ_mem_harmSet {lam : Fin n → ℤ} (lev : Fin n → Fin n) (h : IsLev lam fun a => (lev a : ℕ)) :
    muQ lam (fun a => (lev a : ℕ)) ∈ harmSet lam := by
  simp only [harmSet, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨lev, h, rfl⟩

def Compress : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℤ) (lev : Fin n → ℕ), IsLev lam lev →
    ∃ l : Fin n → Fin n, IsLev lam (fun a => (l a : ℕ)) ∧ muQ lam (fun a => (l a : ℕ)) = muQ lam lev

theorem multG_of (hCp : Compress) (hM : MultFor) (hA : AdmLeast) (h1 : N1) (hC : ConeWeightsNotSecondType) (hE : ModelEx) (h7 : KTypeGenerationHighest) : MultG := by
  intro n lam hl V _ _ E1 E2 σ A hc
  classical
  have hne_h : (harmSet lam).Nonempty := ⟨_, muQ_mem_harmSet (fun a => a) (isLev_id lam)⟩
  by_cases hex : ∃ μ ∈ harmSet lam, hwSp E1 E2 μ ≠ ⊥
  swap
  · push_neg at hex
    obtain ⟨μ₀, hμ₀⟩ := hne_h
    refine ⟨μ₀, hμ₀, fun μ hμ _ => hex μ hμ, ?_⟩
    intro v w hv _ hv0
    rw [hex μ₀ hμ₀, Submodule.mem_bot] at hv
    exact absurd hv hv0
  obtain ⟨μ₁, hμ₁, hne₁⟩ := hex
  let S := (harmSet lam).filter (fun μ => hwSp E1 E2 μ ≠ ⊥)
  have hSne : S.Nonempty := ⟨μ₁, Finset.mem_filter.mpr ⟨hμ₁, hne₁⟩⟩
  obtain ⟨μ₀, hμ₀S, hmin⟩ := S.exists_min_image (fun μ => nsq (μ + rhoV n)) hSne
  obtain ⟨hμ₀, hne₀⟩ := Finset.mem_filter.mp hμ₀S
  obtain ⟨l0, hl0, rfl⟩ := mem_harmSet hμ₀
  have hadm : AdmFor lam (fun a => (l0 a : ℕ)) E1 E2 := by
    refine hA n lam hl V E1 E2 σ A hc _ hl0 hne₀ ?_
    intro lev' hlev' hne'
    obtain ⟨l', hl', heq⟩ := hCp n lam lev' hlev'
    have hmem : muQ lam lev' ∈ S := by
      refine Finset.mem_filter.mpr ⟨?_, hne'⟩
      rw [← heq]
      exact muQ_mem_harmSet l' hl'
    exact hmin _ hmem
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne₀
  refine ⟨_, hμ₀, ?_, ?_⟩
  · intro μ hμ hμne
    by_contra hb
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hb
    obtain ⟨M⟩ := hE n lam hl _ hl0
    have hMn2 : ∀ ν, IsSecondTypeWeight lam (fun a => (l0 a : ℕ)) ν → hwSp M.F1 M.F2 ν = ⊥ := by
      intro ν hν
      letI := M.nacg
      letI := M.ips
      rw [Submodule.eq_bot_iff]
      intro y hy
      by_contra hy0
      exact hC n lam hl _ hl0 ν (M.cone ν y hy hy0) hν
    obtain ⟨a, ha, hav⟩ := hc.irr v x hv0
    have hcone := h7 hM n lam hl _ hl0 V E1 E2 hc.pair hadm M hMn2 v hv hv0 μ x hx hx0 ⟨a, ha, hav⟩
    obtain ⟨l', hl', rfl⟩ := mem_harmSet hμ
    exact hμne (h1 n lam hl _ _ hl0 hl' hcone)
  · intro v' w hv' hw hv'0
    obtain ⟨a, ha, hav⟩ := hc.irr v' w hv'0
    exact hM n lam hl _ hl0 V E1 E2 hadm v' w hv' hw hv'0 ⟨a, ha, hav⟩

end PositivityTheory.RgBcC.RealD
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.SecondLeviFamily
section
noncomputable section

open Finset

namespace PositivityTheory.RgBcC.RealD

open Formalism.REAL (GlRel)
open CompanionTheory.D.LK (Pos)

variable {n : ℕ}

def InvKP (n : ℕ) (a : FreeAlgebra ℂ (Bool × Fin n × Fin n)) : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V), IsPairA E1 E2 →
    ∀ c d, Commute (kA E1 E2 c d) (evKP E1 E2 a)

def InvLv (lev : Fin n → ℕ) (b : FreeAlgebra ℂ (Bool × Fin n × Fin n)) : Prop :=
  ∀ (H : Type) [AddCommGroup H] [Module ℂ H] (F1 F2 : Fin n → Fin n → Module.End ℂ H), IsLevPairA lev F1 F2 →
    ∀ c d, lev c = lev d → Commute (kA F1 F2 c d) (evLv lev F1 F2 b)

section Ops

variable {V : Type} [AddCommGroup V] [Module ℂ V]

def blk (lev : Fin n → ℕ) (j : ℕ) : Finset (Fin n) := univ.filter fun a => lev a = j

def blkE (lev : Fin n → ℕ) (j : ℕ) : Fin (blk lev j).card → Fin n := fun i => (blk lev j).orderEmbOfFin rfl i

def capS (F : Fin n → Fin n → Module.End ℂ V) (lev : Fin n → ℕ) (j : ℕ) (u : ℂ) : Module.End ℂ V :=
  Formalism.REAL.qminor F (blkE lev j) (blkE lev j) (u + (((blk lev j).card : ℂ) - 1) / 2)

def levs (lev : Fin n → ℕ) : List ℕ := (univ.image lev).sort (· ≤ ·)

def capProd (F : Fin n → Fin n → Module.End ℂ V) (lev : Fin n → ℕ) (σ : ℕ → ℂ) (u : ℂ) : Module.End ℂ V :=
  ((levs lev).map fun j => capS F lev j (u - σ j)).prod

def evCap (lev : Fin n → ℕ) (F : Fin n → Fin n → Module.End ℂ V) : FreeAlgebra ℂ (ℕ × ℂ) →ₐ[ℂ] Module.End ℂ V :=
  FreeAlgebra.lift ℂ fun p => capS F lev p.1 p.2

def chU (lev : Fin n → ℕ) (j : ℕ) : Submodule ℂ (Cq n V) where
  carrier := {y | SuppL (inUU lev) y ∧ DegL j y}
  add_mem' {x y} hx hy := ⟨fun A hA l hl => by
      by_cases h : x A = 0
      · exact hy.1 A (by simpa [h] using hA) l hl
      · exact hx.1 A h l hl,
    fun A hA => by
      by_cases h : x A = 0
      · exact hy.2 A (by simpa [h] using hA)
      · exact hx.2 A h⟩
  zero_mem' := ⟨fun A hA => absurd rfl hA, fun A hA => absurd rfl hA⟩
  smul_mem' c x hx := ⟨fun A hA l hl => hx.1 A (fun h => hA (by simp [h])) l hl,
    fun A hA => hx.2 A (fun h => hA (by simp [h]))⟩

def bdSub (lev : Fin n → ℕ) (E1 E2 : Fin n → Fin n → Module.End ℂ V) : Submodule ℂ (Cq n V) :=
  (chU lev ((omU lev).card + 1)).map (bdL (inUU lev) E1 E2)

def firstLeviFamily (lev : Fin n → ℕ) (E1 E2 : Fin n → Fin n → Module.End ℂ V) (p q : Fin n) : Module.End ℂ (Cq n V) :=
  (1 / 2 : ℂ) • (evLc lev E1 E2 (FreeAlgebra.ι ℂ (false, p, q)) + evLc lev E1 E2 (FreeAlgebra.ι ℂ (true, p, q)))

def secondLeviFamily (lev : Fin n → ℕ) (E1 E2 : Fin n → Fin n → Module.End ℂ V) (p q : Fin n) : Module.End ℂ (Cq n V) :=
  (1 / 2 : ℂ) • (evLc lev E1 E2 (FreeAlgebra.ι ℂ (false, p, q)) - evLc lev E1 E2 (FreeAlgebra.ι ℂ (true, p, q)))

end Ops

def Lr (lam : Fin n → ℤ) : Fin n → ℝ := fun a => (lam a : ℝ) + ((n : ℝ) - 1) / 2 - (a : ℕ)

end PositivityTheory.RgBcC.RealD
end
end

