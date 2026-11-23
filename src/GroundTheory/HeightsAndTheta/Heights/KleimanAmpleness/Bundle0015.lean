module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0009
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.GenericPointSectionHypotheses
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0002
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0008

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SnapperSectionObj
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}


variable (S x) in
def spanBundle (s : Ω) (hs : s ≠ 0) : LineBundle S x where
  sub I := Submodule.span (chartRing S x I) {s}
  mono I J h y hy := by
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hy
    exact Submodule.mem_span_singleton.mpr ⟨chartIncl h a, rfl⟩
  mem_iff I J h y := by
    constructor
    · intro hy
      obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hy
      obtain ⟨a, ha, hab⟩ := exists_isUnit_mul_mem h b
      refine ⟨a, ha, Submodule.mem_span_singleton.mpr ⟨⟨_, hab⟩, ?_⟩⟩
      rw [chartRing_smul_def, chartRing_smul_def, smul_eq_mul, mul_assoc]
    · rintro ⟨a, ⟨u, hu⟩, hay⟩
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hay
      have hinv : ((↑u⁻¹ : chartRing S x J) : Ω) * (a : Ω) = 1 := by
        have := congrArg Subtype.val (Units.inv_mul u)
        rw [hu] at this
        exact this
      refine Submodule.mem_span_singleton.mpr ⟨(↑u⁻¹ : chartRing S x J) * chartIncl h c, ?_⟩
      rw [chartRing_smul_def, Subalgebra.coe_mul, mul_assoc]
      change (↑u⁻¹ : chartRing S x J).1 * ((c : Ω) * s) = y
      rw [← chartRing_smul_def c s, hc, smul_eq_mul, ← mul_assoc, hinv, one_mul]
  fg _ := Submodule.fg_span_singleton s
  invertible I := ⟨Submodule.span (chartRing S x I) {s⁻¹}, by
    rw [Submodule.span_mul_span, Set.singleton_mul_singleton, mul_inv_cancel₀ hs, ← Submodule.one_eq_span]⟩

variable {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]

def SubFamily.sup (F G : SubFamily S x E) : SubFamily S x E where
  sub I := F.sub I ⊔ G.sub I
  mono I J h y hy := by
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hy
    exact Submodule.mem_sup.mpr ⟨a, F.mono I J h a ha, b, G.mono I J h b hb, rfl⟩
  mem_iff I J h y := by
    constructor
    · intro hy
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hy
      obtain ⟨u, hu, hua⟩ := (F.mem_iff I J h a).mp ha
      obtain ⟨v, hv, hvb⟩ := (G.mem_iff I J h b).mp hb
      refine ⟨u * v, by rw [map_mul]; exact hu.mul hv, ?_⟩
      have : ((u * v : chartRing S x I) : Ω) • (a + b) = v • ((u : Ω) • a) + u • ((v : Ω) • b) := by
        rw [Subalgebra.smul_def, Subalgebra.smul_def, smul_smul, smul_smul, Subalgebra.coe_mul, smul_add,
          mul_comm (v : Ω) (u : Ω)]
      rw [this]
      exact Submodule.add_mem _ (Submodule.mem_sup_left (Submodule.smul_mem _ v hua))
        (Submodule.mem_sup_right (Submodule.smul_mem _ u hvb))
    · rintro ⟨a, ⟨u, hu⟩, hay⟩
      have hJ : (a : Ω) • y ∈ F.sub J ⊔ G.sub J := by
        obtain ⟨c, hc, d, hd, hcd⟩ := Submodule.mem_sup.mp hay
        exact Submodule.mem_sup.mpr ⟨c, F.mono I J h c hc, d, G.mono I J h d hd, hcd⟩
      have hinv : ((↑u⁻¹ : chartRing S x J) : Ω) * (a : Ω) = 1 := by
        have := congrArg Subtype.val (Units.inv_mul u)
        rw [hu] at this
        exact this
      have hy : y = (↑u⁻¹ : chartRing S x J) • ((a : Ω) • y) := by
        rw [Subalgebra.smul_def, smul_smul, hinv, one_smul]
      rw [hy]
      exact Submodule.smul_mem _ _ hJ

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsClaimSeq
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

def ClaimSeq.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (T : StepData k x),
    ∃ Jg : FinGradedSub (S := k) (x := x) Ω,
      (∀ c : ℤ, Jg.piece c = Submodule.span k {z | ∃ (f : Poly k N) (e : ℕ), f ∈ T.J ∧
        f.IsHomogeneous e ∧ (e : ℤ) = c ∧ z = aeval x f}) ∧
      ∀ (b : ℕ) (c : ℤ) (I : Chart x) (z : Ω),
        z ∈ ((Jg.tildeSys 0).twist ((T.L.pow (b + 1)).twist (twistSys k x c))).sub I ↔
          ∃ y ∈ ((T.L.pow b).twist (twistSys k x (c + T.c₁))).sub I, z = T.si * y

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsCycleSplit
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u w


open Classical in
def CycleSplit.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (M : LineBundle S x) (𝔪 : Ideal S), 𝔪.IsMaximal →
    ∀ J : Ideal (Poly S N), (∀ p ∈ J, ∀ d : ℕ, homogeneousComponent d p ∈ J) →
    primeOf (S := S) x ≤ J → 𝔪.map (C : S →+* Poly S N) ≤ J →
    (∀ G ∈ J.minimalPrimes, ringKrullDim (Poly S N ⧸ G) ≤ 2) →
    ∀ᶠ c : ℕ in atTop,
      interSum J ![M.toSubSystem] c =
        ∑ᶠ G : Ideal (Poly S N),
          if h : G ∈ J.minimalPrimes ∧ IsSubvar x G 1 then
            haveI : G.IsPrime := h.1.1.1
            ((cutMult J G).toNat : ℤ) * interNum G ![M.toSubSystem]
          else 0

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsStepThreeAway
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

def StepThree.Away.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (T : StepData k x) (b : ℕ) (c : ℤ), 0 ≤ c → ∀ I : Chart x,
      ((idealMod (x := x) T.J I).comap (Algebra.linearMap (chartRing k x I) Ω)) ^ b •
          ((T.L.pow b).twist (twistSys k x c)).sub I ≤
        Submodule.span (chartRing k x I) (((T.L.pow b).twist (twistSys k x c)).secs : Set Ω)

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsStepThreeOnW
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

def StepThree.OnW.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (T : StepData k x), (∀ e ≤ T.d, VeryAmpleNefPlusAmple.InDim.{u, w} k e) →
    ∀ pp ∈ T.J.minimalPrimes, ∃ c₀ : ℤ, ∀ (b : ℕ) (c : ℤ), 1 ≤ b → c₀ ≤ c → ∀ I : Chart x,
      ((T.L.pow b).twist (twistSys k x c)).sub I ≤
        Submodule.span (chartRing k x I) (((T.L.pow b).twist (twistSys k x c)).secs : Set Ω) ⊔
          (((T.L.pow b).twist (twistSys k x c)).twist (idealSys x pp)).sub I

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsStepTwo
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

def LineTwist.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (Q₁ Q₂ : LineBundle S x), ∃ Q : LineBundle S x, Q.toSubSystem = Q₁.toSubSystem.twist Q₂.toSubSystem

def TwistAlg.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (M : SubSystem S x Ω) (p q : ℕ) (m m' : ℤ) (b₁ b₂ : ℕ), (q : ℤ) * m = p * m' →
    (twistMul M p m).pow (q * b₁ + b₂) =
      ((twistMul M p m).pow b₂).twist ((twistMul M q m').pow (p * b₁))

def RestrictTwist.Statement : Prop :=
  (∀ (S : Type u) [CommRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (K' : Type w) [Field K'] [Algebra S K'] (y : Fin (N + 1) → K') (hxy : ∀ i, y i ≠ 0 → x i ≠ 0),
    primeOf (S := S) x ≤ primeOf (S := S) y → ∀ c : ℤ,
      ∃ r : Ω → K', RestrictData (twistSys S x c) hxy (twistSys S y c) r) ∧
  ∀ (S : Type u) [CommRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (K' : Type w) [Field K'] [Algebra S K'] (y : Fin (N + 1) → K') (hxy : ∀ i, y i ≠ 0 → x i ≠ 0)
    (Q₁ Q₂ : LineBundle S x) (Q₁' Q₂' : LineBundle S y) (r₁ r₂ : Ω → K'),
    RestrictData Q₁.toSubSystem hxy Q₁'.toSubSystem r₁ →
    RestrictData Q₂.toSubSystem hxy Q₂'.toSubSystem r₂ →
    ∃ r : Ω → K', RestrictData (Q₁.toSubSystem.twist Q₂.toSubSystem) hxy
      (Q₁'.toSubSystem.twist Q₂'.toSubSystem) r

def NefRestrict.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (K' : Type w) [Field K'] [Algebra k K'] (y : Fin (N + 1) → K') (hxy : ∀ i, y i ≠ 0 → x i ≠ 0),
    primeOf (S := k) x ≤ primeOf (S := k) y →
    ∀ (M : LineBundle k x) (M' : LineBundle k y) (r : Ω → K'),
      RestrictData M.toSubSystem hxy M'.toSubSystem r → Nef M.toSubSystem → Nef M'.toSubSystem

def StepData.JProper.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (T : StepData k x), ∃ (f : Poly k N) (e : ℕ), f ∈ T.J ∧ f.IsHomogeneous e ∧ f ∉ primeOf (S := k) x

def SubvarDrop.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (d : ℕ) (pp : Ideal (Poly k N)), IsSubvar x (primeOf (S := k) x) (d + 1) → pp.IsPrime →
    (∀ p ∈ pp, ∀ n : ℕ, homogeneousComponent n p ∈ pp) → primeOf (S := k) x ≤ pp →
    (∃ j, (X j : Poly k N) ∉ pp) → (∃ f ∈ pp, f ∉ primeOf (S := k) x) → ∃ e ≤ d, IsSubvar x pp e

def StepTwo.Reduce.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (E : Type v) [AddCommGroup E] [Module Ω E] [Module S E]
    [IsScalarTower S Ω E] (M₁ M₂ : FinGradedSub (S := S) (x := x) E), (∀ c, M₂.piece c ≤ M₁.piece c) →
    ∀ J : Ideal (Poly S N), (∀ (f : Poly S N) (e : ℕ), f ∈ J → f.IsHomogeneous e → ∀ (a : ℤ),
      ∀ z ∈ M₁.piece a, aeval x f • z ∈ M₂.piece (a + e)) →
    ∃ (n : ℕ) (pr : Fin n → Ideal (Poly S N)) (sh : Fin n → ℤ),
      (∀ i, (pr i).IsPrime ∧ (∀ p ∈ pr i, ∀ d : ℕ, homogeneousComponent d p ∈ pr i) ∧
        primeOf (S := S) x ≤ pr i ∧
        ∀ (f : Poly S N) (e : ℕ), f ∈ J → f.IsHomogeneous e → f ∈ pr i) ∧
      ∀ (Q : LineBundle S x) (c : ℤ),
        (∀ i, (∃ j, (X j : Poly S N) ∉ pr i) →
          Subsingleton (SubSystem.quotH (Q.twist (twistSys S x (c + sh i)))
            ((Q.twist (twistSys S x (c + sh i))).twist (idealSys x (pr i))) 1)) →
        Subsingleton (SubSystem.quotH ((M₁.tildeSys 0).twist (Q.twist (twistSys S x c)))
          ((M₂.tildeSys 0).twist (Q.twist (twistSys S x c))) 1)

section Hypotheses

variable (k : Type u) [Field k]

end Hypotheses

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsTildeTail
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

def TildeTail.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (M : FinGradedSub (S := S) (x := x) Ω), x ≠ 0 →
    ∀ c₁ : ℤ, ∃ (n : ℕ) (deg : Fin n → ℤ) (gen : Fin n → Ω),
      (∀ j, c₁ ≤ deg j ∧ gen j ∈ (M.tildeSys (deg j)).secs) ∧
      ∀ c : ℤ, c₁ ≤ c → (M.tildeSys c).secs ≤ Submodule.span S {z | ∃ (j : Fin n)
        (f : Poly S N) (e : ℕ), f.IsHomogeneous e ∧ (e : ℤ) + deg j = c ∧ z = aeval x f * gen j}

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsZeroIdealChart
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

def ZeroIdealChart.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (T : StepData k x) (I : Chart x) (y : Ω),
    (∀ δ ∈ T.D.sub I, y * δ ∈ chartRing k x I) → T.si * y ∈ idealMod (x := x) T.J I

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.TildeFiniteSt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

def TildeFinite.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (M : FinGradedSub (S := S) (x := x) Ω) (i : ℕ) (c : ℤ),
    Module.Finite S ((M.tildeSys c).H i)

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.VeryAmpleCechSt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u v w

def VeryAmpleCech.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (E : Type v) [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
    (F : SubFamily S x E), (∀ I, (F.sub I).FG) → ∀ (H : LineBundle S x) (r : ℕ) (h : Fin (r + 1) → Ω),
    IsVeryAmpleBy H.toSubSystem h →
    ∃ F' : SubFamily S h E, (∀ J, (F'.sub J).FG) ∧ ∀ a i : ℕ,
      Nonempty ((F.twist (H.pow a)).H i ≃ₗ[S] (F'.twist (twistSys S h (a : ℤ))).H i)

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.VeryAmpleEmbedNumbersSt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u v w

def VeryAmpleEmbed.Numbers.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (y : Fin (N + 1) → Ω)
    (Q : LineBundle k y) (r : ℕ) (h : Fin (r + 1) → Ω), IsVeryAmpleBy Q.toSubSystem h →
    ∀ n : ℕ, IsSubvar y (primeOf (S := k) y) n →
      IsSubvar h (primeOf (S := k) h) n ∧
        interNum (primeOf (S := k) y) (fun _ : Fin n => Q.toSubSystem) =
          interNum (primeOf (S := k) h) (fun _ : Fin n => twistSys k h 1)

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.VeryAmpleEmbedSectionsSt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u v w

def VeryAmpleEmbed.Sections.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (y : Fin (N + 1) → Ω)
    (Q : LineBundle k y) (r : ℕ) (h : Fin (r + 1) → Ω), y ≠ 0 → IsVeryAmpleBy Q.toSubSystem h →
    ∀ m : ℕ, (Q.toSubSystem.pow m).secs = (twistSys k h (m : ℤ)).secs

end

end GroundTheory.Heights₂.Heights.Kleiman
end

