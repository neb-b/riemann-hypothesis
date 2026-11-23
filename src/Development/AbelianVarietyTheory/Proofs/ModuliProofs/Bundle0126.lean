module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0116
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0117
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0069
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0072
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0102
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0113
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0114
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsLocalOnBaseOfOpenCover
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0073
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0098
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0107

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsTateIsoOfPeriodMapGenus
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory


open PeriodTate in
theorem exists_tateIso_of_periodMap_genus : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (D' : Datum H) (f : ℕ → D.La →ₗ[𝓞 E] D'.La) (ν : ℕ → ℤ) (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ) (act : OAct (𝓞 E) P.A) (Q : D'.La →+ (Fin P.g → ℂ)), 1 ≤ D.p + D.q → (D'.p = D.p ∧ D'.q = D.q ∧ (∀ n m : ℕ, 0 < n → 0 < m → ∀ x, ∃ y, f (n * m) x = f n x + n • y) ∧ (∀ n : ℕ, 0 < n → (∀ x, (∃ y, f n x = n • y) ↔ ∃ y, x = n • y) ∧ ∀ x', ∃ x y, x' = f n x + n • y) ∧ ∀ n : ℕ, 0 < n → ∀ x x', (n : ℤ) ∣ D'.EF (f n x) (f n x') - ν n * D.EF x x') → u.IsAH Hm χ → Function.Injective Q → (∀ z, z ∈ u.Λ ↔ z ∈ Q.range) → (∀ x y, (hermForm Hm (Q x) (Q y)).im = D'.EF x y) → (∀ (a : 𝓞 E) (n : ℕ) x, u.ex ((n : ℂ)⁻¹ • Q (a • x)) = u.ex ((n : ℂ)⁻¹ • Q x) ≫ act.act a) → ∀ (K : Type) [Field K] [IsAlgClosed K] (β : ℂ →+* K), ∃ I : TateIso D K (Over.mk (spMap β) ⟶ P.A) (fun c y => y ≫ act.act c) (fun n y y' c => Out.WeilIs P.A P.L n y y' (unitOn c)), ∀ n : ℕ, 0 < n → (I.ζ n : K) = β (Complex.exp (-(2 * Real.pi * Complex.I) * (ν n : ℂ) / n)) ∧ ∀ x, (I.ev n x).left = spMap β ≫ (u.ex ((n : ℂ)⁻¹ • Q (f n x))).left := by
  intro hL hL2 hT hU E _ _ _ H D D' f ν Q u Hm χ act P hpq ⟨_, _, htow, hmod, hν⟩ hAH hinj hΛ hE hact k _ _ β
  obtain ⟨Ef, hEf, -, -, -, -, -, -, hW₀⟩ := _root_.GlobalTheory.AnyAppellHumbert.isAH_properties hL hL2 hT hU Q u Hm χ hAH
  have hadd := u.ex_add
  have hsurj := u.ex_onto
  have hker : ∀ z, u.ex z = 1 ↔ z ∈ P.range := fun z => (u.ker z).trans (hΛ z)
  have hW : ∀ (n : ℕ) (a b : D'.La), 0 < n →
      Out.WeilIs Q.A Q.L n (u.ex ((n : ℂ)⁻¹ • P a)) (u.ex ((n : ℂ)⁻¹ • P b)) (unitOn (rt n (D'.EF a b))) := by
    intro n a b hn
    have h : Ef ⟨P a, (hΛ _).2 ⟨a, rfl⟩⟩ ⟨P b, (hΛ _).2 ⟨b, rfl⟩⟩ = D'.EF a b := by
      have := (hEf ⟨P a, (hΛ _).2 ⟨a, rfl⟩⟩ ⟨P b, (hΛ _).2 ⟨b, rfl⟩⟩).trans (hE a b)
      exact_mod_cast this
    exact hW₀ n ⟨P a, (hΛ _).2 ⟨a, rfl⟩⟩ ⟨P b, (hΛ _).2 ⟨b, rfl⟩⟩ _ hn (by rw [h, rt_val])
  generalize u.ex = e at hadd hsurj hker hW hact ⊢
  have : Nontrivial D.La := Module.nontrivial_of_finrank_pos (R := 𝓞 E) (by rw [D.rank]; omega)
  obtain ⟨a₀, b₀, h₀⟩ := exists_pairing_one D
  have : Nontrivial D'.La := by
    refine ⟨f 2 a₀, 0, fun h => ?_⟩
    obtain ⟨c, hc⟩ := ((hmod 2 two_pos).1 a₀).1 ⟨0, by rw [h, smul_zero]⟩
    rw [hc, map_nsmul, LinearMap.smul_apply, nsmul_eq_mul] at h₀
    omega
  obtain ⟨a₁, b₁, h₁⟩ := exists_pairing_one D'
  have hcong : ∀ (n : ℕ) (a b c d : D'.La), (n : ℤ) ∣ D'.EF (a + n • c) (b + n • d) - D'.EF a b := by
    intro n a b c d
    refine ⟨D'.EF a d + D'.EF c b + n * D'.EF c d, ?_⟩
    simp only [map_add (f := _), map_nsmul, LinearMap.add_apply, LinearMap.smul_apply, nsmul_eq_mul]
    ring
  have hcop : ∀ n : ℕ, 0 < n → IsCoprime (ν n) n := by
    intro n hn
    obtain ⟨a, c, ha⟩ := (hmod n hn).2 a₁
    obtain ⟨b, d, hb⟩ := (hmod n hn).2 b₁
    obtain ⟨s, hs⟩ := hcong n (f n a) (f n b) c d
    obtain ⟨v, hv⟩ := hν n hn a b
    rw [← ha, ← hb, h₁] at hs
    exact ⟨D.EF a b, s + v, by linear_combination -hs - hv⟩
  have hνt : ∀ n m : ℕ, 0 < n → 0 < m → (n : ℤ) ∣ ν (n * m) - ν n := by
    intro n m hn hm
    obtain ⟨c, hc⟩ := htow n m hn hm a₀
    obtain ⟨d, hd⟩ := htow n m hn hm b₀
    obtain ⟨s, hs⟩ := hcong n (f n a₀) (f n b₀) c d
    obtain ⟨v, hv⟩ := hν n hn a₀ b₀
    obtain ⟨w, hw⟩ := hν (n * m) (Nat.mul_pos hn hm) a₀ b₀
    rw [← hc, ← hd] at hs
    rw [h₀] at hv hw
    push_cast at hw
    exact ⟨s + v - m * w, by linear_combination hs + hv - hw⟩
  let e' : Multiplicative (Fin Q.g → ℂ) →* (𝟙_ (Over (Sp ℂ)) ⟶ Q.A) :=
    MonoidHom.mk' (fun z => e z.toAdd) fun z w => hadd _ _
  have hpow : ∀ (n : ℕ) z, e z ^ n = e (n • z) := fun n z => (map_pow e' (Multiplicative.ofAdd z) n).symm
  let ρ := preHom (G := Q.A) (toUnit (Over.mk (spMap β)))
  have hρ : Function.Injective ρ := pre_injective β Q.A
  have hl : (toUnit (Over.mk (spMap β))).left = spMap β := by
    simpa using Over.w (toUnit (Over.mk (spMap β)))
  have hsm : ∀ n : ℕ, 0 < n → ∀ z : Fin Q.g → ℂ, n • (n : ℂ)⁻¹ • z = z := fun n hn z => by
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_inv_cancel₀ (by exact_mod_cast hn.ne'), one_smul]
  have hsm' : ∀ n : ℕ, 0 < n → ∀ z : Fin Q.g → ℂ, (n : ℂ)⁻¹ • n • z = z := fun n hn z => by
    rw [smul_comm, hsm n hn]
  have hshift : ∀ n : ℕ, 0 < n → ∀ a c : D'.La, e ((n : ℂ)⁻¹ • P (a + n • c)) = e ((n : ℂ)⁻¹ • P a) := by
    intro n hn a c
    rw [map_add (f := _), smul_add, hadd, map_nsmul, hsm' n hn, (hker _).2 ⟨c, rfl⟩, _root_.mul_one]
  refine ⟨{ ζ := fun n => Units.map β.toMonoidHom (rt n (ν n))
            ζ_prim := fun n hn => (rt_prim hn (hcop n hn)).map_of_injective (Units.map_injective β.injective)
            ζ_pow := fun n m hn hm => by rw [← map_pow, rt_pow hm, rt_congr hn (hνt n m hn hm)]
            ev := fun n a => ρ (e ((n : ℂ)⁻¹ • P (f n a)))
            add := fun n a b => by rw [map_add (f := _), map_add (f := _), smul_add, hadd, map_mul]
            lin := fun n c a => ?_
            ker := fun n hn a => ?_
            onto := fun n hn x => ?_
            tower := fun n m hn hm a => ?_
            isom := fun n hn a b => ?_ }, fun n _ => ⟨rfl, fun a => ?_⟩⟩
  · show toUnit (Over.mk (spMap β)) ≫ _ = (toUnit (Over.mk (spMap β)) ≫ _) ≫ _
    rw [Category.assoc, ← hact, map_smul]
  · rw [map_eq_one_iff ρ hρ, hker, ← (hmod n hn).1 a]
    constructor
    · rintro ⟨c, hc⟩
      exact ⟨c, hinj (by rw [map_nsmul, hc, hsm n hn])⟩
    · rintro ⟨c, hc⟩
      exact ⟨c, by rw [hc, map_nsmul, hsm' n hn]⟩
  · constructor
    · intro hx
      obtain ⟨y, hy, rfl⟩ := pre_onto hL.mulN β Q hn x hx
      obtain ⟨z, rfl⟩ := hsurj y
      rw [hpow, hker] at hy
      obtain ⟨a', ha'⟩ := hy
      obtain ⟨a, c, rfl⟩ := (hmod n hn).2 a'
      refine ⟨a, congrArg ρ ?_⟩
      rw [← hshift n hn _ c, ha', hsm' n hn]
    · rintro ⟨a, rfl⟩
      rw [← map_pow, hpow, hsm n hn, (hker _).2 ⟨_, rfl⟩, map_one]
  · obtain ⟨c, hc⟩ := htow n m hn hm a
    rw [← map_pow, hpow, Nat.cast_mul, mul_inv_rev, mul_smul, hsm m hm, hc, hshift n hn]
  · have h := CommPairing.weilIs_pull hL.globalFns Q.isAb Q.isLB (toUnit (Over.mk (spMap β)))
      (hW n (f n a) (f n b) hn)
    rw [unitOn_pull, rt_congr hn (hν n hn a b), rt_mul, map_zpow] at h
    exact h
  · exact congrArg (· ≫ (e ((n : ℂ)⁻¹ • P (f n a))).left) hl

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaFrameOfPreconnected
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.ThetaFamily

theorem thetaChar_family {g m : ℕ} {B : Set (Fin m → ℂ)} {p q : Fin g → (Fin m → ℂ) → (Fin g → ℂ)}
    {h τ : (Fin m → ℂ) → Matrix (Fin g) (Fin g) ℂ} (hp : ∀ k, DifferentiableOn ℂ (p k) B)
    (hq : ∀ k, DifferentiableOn ℂ (q k) B)
    (hh : ∀ b ∈ B, ((τ b).map Complex.im).PosDef ∧ ∀ k, (h b).mulVec (p k b) = Pi.single k 1 ∧
      (h b).mulVec (q k b) = (τ b).mulVec (Pi.single k 1))
    {c₁ c₂ : Fin g → ℂ} (h₁ : ∀ k, c₁ k = 0 ∨ c₁ k = 1 / 2) (h₂ : ∀ k, c₂ k = 0 ∨ c₂ k = 1 / 2) :
    DifferentiableOn ℂ (fun bz : (Fin m → ℂ) × (Fin g → ℂ) => thetaChar (τ bz.1) c₁ c₂ ((h bz.1).mulVec bz.2))
      (B ×ˢ Set.univ) ∧ ∀ b ∈ B, ∀ z, ∃ᶠ w in nhds z, thetaChar (τ b) c₁ c₂ ((h b).mulVec w) ≠ 0 := by
  have re : ∀ {c : Fin g → ℂ}, (∀ k, c k = 0 ∨ c k = 1 / 2) → ∃ a : Fin g → ℝ, c = fun i => (a i : ℂ) := fun {c} hc =>
    ⟨fun i => (c i).re, funext fun i => by rcases hc i with e | e <;> simp [e]⟩
  obtain ⟨a₁, rfl⟩ := re h₁
  obtain ⟨a₂, rfl⟩ := re h₂
  have hinv : ∀ b ∈ B, h b * Matrix.of (fun i k => p k b i) = 1 := fun b hb => by
    ext i k
    have := congrFun ((hh b hb).2 k).1 i
    rw [Matrix.one_apply, ← Pi.single_apply k (1 : ℂ) i, ← this]
    rfl
  have dh : ∀ i j, DifferentiableOn ℂ (fun b => h b i j) B :=
    differentiableOn_left_inverse (fun i k => differentiableOn_pi.1 (hp k) i) hinv
  have dτ : ∀ i k, DifferentiableOn ℂ (fun b => τ b i k) B := fun i k => by
    refine (DifferentiableOn.fun_sum (u := Finset.univ) fun j _ =>
      (dh i j).mul (differentiableOn_pi.1 (hq k) j)).congr fun b hb => ?_
    have := congrFun ((hh b hb).2 k).2 i
    rw [Matrix.mulVec_single_one] at this
    exact this.symm
  have fst : ∀ {f : (Fin m → ℂ) → ℂ}, DifferentiableOn ℂ f B →
      DifferentiableOn ℂ (fun bz : (Fin m → ℂ) × (Fin g → ℂ) => f bz.1) (B ×ˢ Set.univ) := fun hf =>
    hf.comp differentiableOn_fst fun _ h => h.1
  refine ⟨CanTh.differentiableOn_thetaChar (T := fun bz : (Fin m → ℂ) × (Fin g → ℂ) => τ bz.1)
    (Z := fun bz => (h bz.1).mulVec bz.2) (fun i k => fst (dτ i k)) (differentiableOn_pi.2 fun i => ?_)
    (fun w hw => CanTh.mem_thetaDomain (hh _ hw.1).1) a₁ a₂, fun b hb => ?_⟩
  · simp only [Matrix.mulVec, dotProduct]
    exact DifferentiableOn.fun_sum fun j _ => (fst (dh i j)).mul (by fun_prop)
  · have dl : Differentiable ℂ (fun w : Fin g → ℂ => (h b).mulVec w) :=
      (LinearMap.toContinuousLinearMap (Matrix.mulVecLin (h b))).differentiable
    refine frequently_ne_zero_of_entire
      (θ := fun w => thetaChar (τ b) (fun i => (a₁ i : ℂ)) (fun i => (a₂ i : ℂ)) ((h b).mulVec w))
      ((CanTh.differentiable_thetaChar (CanTh.mem_thetaDomain (hh b hb).1) a₁ a₂).comp dl) fun h0 => ?_
    refine thetaChar_ne_zero (hh b hb).1 a₁ a₂ (funext fun w => ?_)
    have := congrFun h0 ((Matrix.of (fun i k => p k b i)).mulVec w)
    rwa [Matrix.mulVec_mulVec, hinv b hb, Matrix.one_mulVec] at this

theorem exists_thetaFrame_of_preconnected : Out.Laws → (∀ (k : Type) [Field k] (X : Scheme.{0}) (s
    : X ⟶ Sp k), Smooth s → IsReduced X ∧ IsNormalScheme X ∧ IsLocallyNoetherian X) → (∀ (E
    : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B
    : Type) [CommRing B] (b : Base l B) (S : Scheme.{0}) (s : S ⟶ Sp B) (o
    : Obj D l b s), IsAbelianScheme o.t.G ∧ SmoothOfRelativeDimension (Module.finrank ℚ E / 2 * (D.p
    + D.q)) o.t.G.hom ∧ Out.Rigidified o.t.G o.t.PP.L ∧ Out.Sym o.t.G o.t.PP.L) → (∀ (E
    : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo
    : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)), 1 ≤ D.p + D.q → σ (baseKA
    l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → ∀ (D' : Datum H) (t : D.La →ₗ[𝓞 E] D'.La) (m : ℕ) (B
    : Set (Fin m → ℂ)) (P : (Fin m → ℂ) → (D'.La →+ (Fin g → ℂ))) (y : (Fin m → ℂ) → (Sp ℂ ⟶
    Xo.X)) (e : ∀ b, (Fin g → ℂ) → (Over.mk (y b) ⟶ Xo.univ.t.G)) (bas : (Fin g ⊕ Fin g →
    ℤ) ≃ₗ[ℤ] D'.La) (sgn : ℤˣ) (h τ : (Fin m → ℂ) → Matrix (Fin g) (Fin g) ℂ), (∀ b ∈ B, ((y b) ≫
    Xo.s = spMap σ ∧ IsPeriod D' ty (P b) ∧ ((∀ z w, (e b) (z + w) = (e b) z * (e b) w) ∧
    Function.Surjective (e b) ∧ IsHolTo Set.univ (fun z => ((e b) z).left) ∧ (∀ w, ∃! v : epsPt (y
    b) ⟶ Xo.univ.t.G, IsDerivAt0 (fun z => ((e b) z).left) w v.left) ∧ (∀ v : epsPt (y
    b) ⟶ Xo.univ.t.G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = ((e b)
    0).left → ∃! w, IsDerivAt0 (fun z => ((e b) z).left) w v.left)) ∧ (∀ z, (e b) z = 1 ↔ z ∈ ((P
    b)).range) ∧ (∀ (a : 𝓞 E) z, (e b) (fun k => ty k (a : E) * z k) = (e
    b) z ≫ Xo.univ.t.act.act a) ∧ (∀ (k : ℕ) (a a₂ : D'.La) (c : ℂˣ), 0 < k → (c
    : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a a₂ : ℂ) /
    k) → Out.WeilIs Xo.univ.t.G Xo.univ.t.PP.L k ((e b) ((k : ℂ)⁻¹ • (P b) a)) ((e b) ((k : ℂ)⁻¹ •
    (P b) a₂)) (unitOn c)) ∧ (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞
    E) D.La), toUnit _ ≫ Xo.univ.eta a = (e b) ((l.M : ℂ)⁻¹ • (P b) (t a))) ∧
    ∀ a, toUnit _ ≫ Xo.univ.etaA a = (e b) ((l.A : ℂ)⁻¹ • (P b) (t a)))) → (∀ a b, D'.EF (bas
    a) (bas b) = sgn * omegaStd a b) → (∀ b ∈ B, ((τ b).map Complex.im).PosDef ∧ ∀ k, (h
    b).mulVec (P b (bas (Pi.single (.inl k) 1))) = Pi.single k 1 ∧ (h b).mulVec (P b (bas (Pi.single
    (.inr k) 1))) = (τ b).mulVec (Pi.single k 1)) → ∀ b₀ ∈ B, ∃! cc : (Fin g → ℂ) × (Fin g →
    ℂ), ∃ c₁ c₂, cc = (c₁,
    c₂) ∧ (∀ k, c₁ k = 0 ∨ c₁ k = 1 / 2) ∧ (∀ k, c₂ k = 0 ∨ c₂ k = 1 / 2) ∧ IsThetaFrame Xo.univ.t.PP {b₀} y (fun b z => (e
    b z).left) (fun b z => thetaChar (τ b) c₁ c₂ ((h b).mulVec z))) → (∀ (X
    : Scheme.{0}) [IsLocallyNoetherian X] (P : Out.PolAV X) (x : X), ∃ (V : X.Opens) (θ
    : ∀ i, Γ(P.A.left, P.A.hom ⁻¹ᵁ V ⊓ P.L.U i)), x ∈ V ∧ θ ∈ secOn P.L (P.A.hom ⁻¹ᵁ
    V) ∧ (∀ y ∈ V, ∃ (a : P.A.left) (i : P.L.ι), P.A.hom a = y ∧ a ∈ P.A.left.basicOpen (θ
    i))) → (∀ (V V' : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ
    V] [NormedAddCommGroup V'] [NormedSpace ℂ V'] [FiniteDimensional ℂ V'] (W : Set (V × V')) (f θ F
    : V × V' → ℂ), IsOpen W → DifferentiableOn ℂ f W → DifferentiableOn ℂ θ W → (∀ w ∈ W, F w * θ w = f w) → (∀ b, DifferentiableOn ℂ (fun z => F (b,
    z)) {z | (b, z) ∈ W}) → (∀ w ∈ W, ∃ᶠ z in nhds w.2, θ (w.1,
    z) ≠ 0) → DifferentiableOn ℂ F W) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H
    : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty
    : Fin g → (E →+* ℂ)), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → ∀ (D'
    : Datum H) (t : D.La →ₗ[𝓞 E] D'.La) (m : ℕ) (B : Set (Fin m → ℂ)) (P : (Fin m → ℂ) → (D'.La →+
    (Fin g → ℂ))) (y : (Fin m → ℂ) → (Sp ℂ ⟶ Xo.X)) (e : ∀ b, (Fin g → ℂ) → (Over.mk (y b) ⟶
    Xo.univ.t.G)) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] D'.La) (sgn : ℤˣ) (h τ : (Fin m →
    ℂ) → Matrix (Fin g) (Fin g) ℂ), (∀ b ∈ B, ((y b) ≫ Xo.s = spMap σ ∧ IsPeriod D' ty (P b) ∧
    ((∀ z w, (e b) (z + w) = (e b) z * (e b) w) ∧ Function.Surjective (e b) ∧ IsHolTo Set.univ
    (fun z => ((e b) z).left) ∧ (∀ w, ∃! v : epsPt (y b) ⟶ Xo.univ.t.G, IsDerivAt0 (fun z => ((e b)
    z).left) w v.left) ∧ (∀ v : epsPt (y b) ⟶ Xo.univ.t.G, spMap (TrivSqZeroExt.fstHom ℂ ℂ
    ℂ).toRingHom ≫ v.left = ((e b) 0).left → ∃! w, IsDerivAt0 (fun z => ((e b) z).left) w v.left)) ∧
    (∀ z, (e b) z = 1 ↔ z ∈ ((P b)).range) ∧ (∀ (a : 𝓞 E) z, (e b) (fun k => ty k (a
    : E) * z k) = (e b) z ≫ Xo.univ.t.act.act a) ∧ (∀ (k : ℕ) (a a₂ : D'.La) (c : ℂˣ), 0 < k → (c
    : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a a₂ : ℂ) /
    k) → Out.WeilIs Xo.univ.t.G Xo.univ.t.PP.L k ((e b) ((k : ℂ)⁻¹ • (P b) a)) ((e b) ((k : ℂ)⁻¹ •
    (P b) a₂)) (unitOn c)) ∧ (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞
    E) D.La), toUnit _ ≫ Xo.univ.eta a = (e b) ((l.M : ℂ)⁻¹ • (P b) (t a))) ∧
    ∀ a, toUnit _ ≫ Xo.univ.etaA a = (e b) ((l.A : ℂ)⁻¹ • (P b) (t a)))) → (∀ a b, D'.EF (bas
    a) (bas b) = sgn * omegaStd a b) → (∀ b ∈ B, ((τ b).map Complex.im).PosDef ∧ ∀ k, (h
    b).mulVec (P b (bas (Pi.single (.inl k) 1))) = Pi.single k 1 ∧ (h b).mulVec (P b (bas (Pi.single
    (.inr k) 1))) = (τ b).mulVec (Pi.single k
    1)) → IsOpen B → IsPreconnected B → IsHolPeriods D' ty B P → IsHolTo B y → IsHolTo (B ×ˢ
    Set.univ) (fun bz : (Fin m → ℂ) × (Fin g → ℂ) => (e bz.1
    bz.2).left) → ∃ c₁ c₂ : Fin g → ℂ, (∀ k, c₁ k = 0 ∨ c₁ k = 1 / 2) ∧ (∀ k, c₂ k = 0 ∨ c₂ k = 1 / 2) ∧ IsThetaFrame Xo.univ.t.PP B y (fun b z => (e
    b z).left) (fun b z => thetaChar (τ b) c₁ c₂ ((h b).mulVec z)) := by
  intro laws hsm hobj hpt hsec _ E _ _ _ H D l Xo σ g ty h1 h2 h3 D' t m B P y e bas sgn h τ hU hbas hh _ hc hP hy hol
  have pt := hpt E H D l Xo σ g ty h1 h2 h3 D' t m B P y e bas sgn h τ hU hbas hh
  have th := fun (c₁ c₂ : Fin g → ℂ) h₁ h₂ => thetaChar_family (c₁ := c₁) (c₂ := c₂)
    (p := fun k b => P b (bas (Pi.single (.inl k) 1))) (q := fun k b => P b (bas (Pi.single (.inr k) 1)))
    (fun k => hP.2 _) (fun k => hP.2 _) hh h₁ h₂
  have he : ∀ b ∈ B, ∀ z, (e b z).left ≫ Xo.univ.t.G.hom = y b := fun b _ z => Over.w (e b z)
  have he0 : ∀ b ∈ B, (e b 0).left = y b ≫ eSec Xo.univ.t.G := fun b hb => by
    rw [((hU b hb).2.2.2.1 0).2 (zero_mem _)]
    rfl
  have := Xo.smooth
  have := (hsm _ _ Xo.s (SmoothOfRelativeDimension.smooth D.dim Xo.s)).2.2
  obtain ⟨o₁, o₂, o₃, o₄⟩ := hobj E H D l _ _ _ _ Xo.univ
  have sec : ∀ b₀ ∈ B, ∃ (V : Xo.X.Opens) (θ₀ : ∀ j, Γ(Xo.univ.t.G.left, Xo.univ.t.G.hom ⁻¹ᵁ V ⊓ Xo.univ.t.PP.L.U j)),
      ⊤ ≤ y b₀ ⁻¹ᵁ V ∧ ∀ b ∈ B, ⊤ ≤ y b ⁻¹ᵁ V → SpansFibre Xo.univ.t.PP (y b) V θ₀ := fun b₀ _ => by
    obtain ⟨V, θ₀, m₀, s₀, n₀⟩ := hsec Xo.X
      { A := Xo.univ.t.G, isAb := o₁, g := _, smoothDim := o₂, L := Xo.univ.t.PP.L, isLB := Xo.univ.t.PP.isLB
        rigid := o₃, sym := o₄, ample := Xo.univ.ample, ktriv := Xo.univ.ktriv } (y b₀ (default : PrimeSpectrum ℂ))
    exact ⟨V, θ₀, (top_le_preimage_iff_mem _ _).2 m₀, fun b _ hb =>
      exists_ratio_fibre laws.globalSectionsRank Xo.univ (y b) V θ₀ s₀ n₀ hb⟩
  choose! c hc₁ hc₂ using pt
  let C₀ : Set (Fin g → ℂ) := Set.pi Set.univ fun _ => {0, 1 / 2}
  have fin : (C₀ ×ˢ C₀).Finite := (Set.Finite.pi fun _ => Set.toFinite _).prod (Set.Finite.pi fun _ => Set.toFinite _)
  have hc₃ : ∀ b ∈ B, (∀ k, (c b).1 k = 0 ∨ (c b).1 k = 1 / 2) ∧ (∀ k, (c b).2 k = 0 ∨ (c b).2 k = 1 / 2) ∧
      ∃ fr, IsFibreFrame Xo.univ.t.PP (y b) (fun z => (e b z).left)
        (fun z => thetaChar (τ b) (c b).1 (c b).2 ((h b).mulVec z)) fr := fun b hb => by
    obtain ⟨c₁, c₂, e₀, r₁, r₂, r₃⟩ := hc₁ b hb
    have r := isThetaFrame_singleton_iff.1 r₃
    rw [e₀]
    exact ⟨r₁, r₂, r⟩
  have const := eq_of_finite_of_closed_fibres hc fin c
    (fun b hb => ⟨fun k _ => (hc₃ b hb).1 k, fun k _ => (hc₃ b hb).2.1 k⟩) (fun k hk b hb hcl => by
      have k₁ := fun i => hk.1 i trivial
      have k₂ := fun i => hk.2 i trivial
      obtain ⟨V, θ₀, hV₀, hV⟩ := sec b hb
      obtain ⟨fr', h'⟩ := (hc₃ b hb).2.2
      have r := exists_fibreFrame_of_mem_closure (e := fun b z => (e b z).left)
        (θ := fun b z => thetaChar (τ b) k.1 k.2 ((h b).mulVec z)) he hol (th _ _ k₁ k₂).1 (th _ _ k₁ k₂).2 hb hV₀ hV
        (T := {b' ∈ B | c b' = k}) (fun b' hb' => by have r := (hc₃ b' hb'.1).2.2; rw [hb'.2] at r; exact r) hcl
        ((th _ _ (hc₃ b hb).1 (hc₃ b hb).2.1).2 b hb) h'
      exact (hc₂ b hb k ⟨k.1, k.2, rfl, k₁, k₂, (isThetaFrame_singleton_iff (y := y) (e := fun b z => (e b z).left)
        (θ := fun b z => thetaChar (τ b) k.1 k.2 ((h b).mulVec z))).2 r⟩).symm)
  obtain ⟨k, k₁, k₂, hk⟩ : ∃ k : (Fin g → ℂ) × (Fin g → ℂ), (∀ i, k.1 i = 0 ∨ k.1 i = 1 / 2) ∧
      (∀ i, k.2 i = 0 ∨ k.2 i = 1 / 2) ∧ ∀ b ∈ B, c b = k := by
    rcases B.eq_empty_or_nonempty with h0 | ⟨b₀, hb₀⟩
    · exact ⟨0, fun _ => Or.inl rfl, fun _ => Or.inl rfl, fun b hb => absurd (h0 ▸ hb) (Set.notMem_empty b)⟩
    · exact ⟨c b₀, (hc₃ b₀ hb₀).1, (hc₃ b₀ hb₀).2.1, fun b hb => const b hb b₀ hb₀⟩
  exact ⟨k.1, k.2, k₁, k₂, isThetaFrame_of_fibreFrames (e := fun b z => (e b z).left)
    (θ := fun b z => thetaChar (τ b) k.1 k.2 ((h b).mulVec z)) he he0 hy hol (th _ _ k₁ k₂).1 (th _ _ k₁ k₂).2 sec
    fun b hb => by have r := (hc₃ b hb).2.2; rw [hk b hb] at r; exact r⟩

end GlobalTheory.ThetaFamily
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaLevelAbelianSchemeGlueOpenCover
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory

open CoverGlue

private theorem exists_section_of_compatible_local_sections {S : Scheme.{0}} {I : Type} {U : I → S.Opens} (hU : iSup U = ⊤) {A : Over S}
    {G : ∀ i, Over (U i).toScheme} {ψ : ∀ i, (G i).left ⟶ A.left}
    (hp : ∀ i, IsPullback (ψ i) (G i).hom A.hom (U i).ι)
    (σ : ∀ i, Out.baseOver (U i).toScheme ⟶ G i)
    (hσ : ∀ i j, S.homOfLE (inf_le_left : U i ⊓ U j ≤ U i) ≫ (σ i).left ≫ ψ i =
      S.homOfLE (inf_le_right : U i ⊓ U j ≤ U j) ≫ (σ j).left ≫ ψ j) :
    ∃ x : Out.baseOver S ⟶ A, ∀ i, (σ i).left ≫ ψ i = (U i).ι ≫ x.left := by
  have hc : ∀ p : S, ∃ i, p ∈ Set.range (U i).ι := fun p => by
    obtain ⟨i, hi⟩ := exists_mem hU p
    exact ⟨i, by simpa using hi⟩
  obtain ⟨F, hF⟩ := exists_hom (fun i => (U i).ι) (fun i => inferInstance) hc
    (fun i => (σ i).left ≫ ψ i) (fun i j => AlgebraicGeometry.isPullback_opens_inf (U i) (U j)) hσ
  have hw : F ≫ A.hom = 𝟙 S := by
    refine hom_ext (fun i => (U i).ι) (fun i => inferInstance) hc (fun i => ?_)
    have h1 := Over.w (σ i)
    rw [reassoc_of% (hF i), (hp i).w, reassoc_of% h1]
    simp
  refine ⟨Over.homMk F (by simpa using hw), fun i => ?_⟩
  simpa using (hF i).symm

private theorem exists_endo_of_compatible_local_endos {S : Scheme.{0}} {I : Type} {U : I → S.Opens} (hU : iSup U = ⊤) {A : Over S}
    {G : ∀ i, Over (U i).toScheme} {ψ : ∀ i, (G i).left ⟶ A.left}
    (hp : ∀ i, IsPullback (ψ i) (G i).hom A.hom (U i).ι)
    {B : I → I → Scheme.{0}} {a : ∀ i j, B i j ⟶ (G i).left} {a' : ∀ i j, B i j ⟶ (G j).left}
    (hB : ∀ i j, IsPullback (a i j) (a' i j) (ψ i) (ψ j)) (e : ∀ i, G i ⟶ G i)
    (he : ∀ i j, a i j ≫ (e i).left ≫ ψ i = a' i j ≫ (e j).left ≫ ψ j) :
    ∃ f : A ⟶ A, ∀ i, (e i).left ≫ ψ i = ψ i ≫ f.left := by
  have hψ : ∀ i, IsOpenImmersion (ψ i) := fun i => isOpenImmersion (hp i)
  have hc := covers hU hp
  obtain ⟨F, hF⟩ := exists_hom ψ hψ hc (fun i => (e i).left ≫ ψ i) hB he
  have hw : F ≫ A.hom = A.hom := by
    refine hom_ext ψ hψ hc (fun i => ?_)
    rw [reassoc_of% (hF i), (hp i).w, reassoc_of% (Over.w (e i))]
  exact ⟨Over.homMk F hw, fun i => (hF i).symm⟩

private theorem hcompl_unit_property_of_isPrime {o : Type} [CommRing o] {S S' : Scheme.{0}} (f : S' ⟶ S) (s : S ⟶ Sp o) (u : oˣ) :
    Units.map f.appTop.hom.toMonoidHom (unitS s u) = unitS (f ≫ s) u := by
  ext
  simp [unitS]
  rfl

theorem exists_tobj_of_cover : ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (S : Scheme.{0}) (s : S ⟶ Sp o) (I : Type) (U : I → S.Opens) (t : ∀ i, TObj g k J b ((U i).ι ≫ s)), iSup U = ⊤ → (∀ i j, ∃ u : TObj g k J b ((U i ⊓ U j).ι ≫ s), TMap u (t i) (S.homOfLE inf_le_left) ∧ TMap u (t j) (S.homOfLE inf_le_right)) → (∀ (T : Scheme.{0}) (i : I) (f : T ⟶ (U i).toScheme) (u : TObj g k J b (f ≫ (U i).ι ≫ s)) (φ φ' : u.A.left ⟶ (t i).A.left), IsOpenImmersion f → IsGrpPullback u.A (t i).A f φ → IsGrpPullback u.A (t i).A f φ' → LBIso u.L ((t i).L.pull φ) → LBIso u.L ((t i).L.pull φ') → (∀ a, (u.pt a).left ≫ φ = (u.pt a).left ≫ φ') → φ = φ') → ∃ t₀ : TObj g k J b s, ∀ i, TMap (t i) t₀ (U i).ι := by
  intro o _ g k J b S s I U t hU hov hrig
  choose u hl hr using hov
  simp only [TMap] at hl hr
  choose a ha using hl
  choose a' ha' using hr
  have hcoc := _root_.GlobalTheory.ThetaCocycle.cocycle tObj_pull o g k J b S s I U t u a a'
    (fun i j => ⟨(ha i j).1, (ha i j).2.1, (ha i j).2.2.1⟩)
    (fun i j => ⟨(ha' i j).1, (ha' i j).2.1, (ha' i j).2.2.1⟩) hrig
  obtain ⟨A, ψ, hp, hB⟩ := _root_.GlobalTheory.CocycleGlue.glue_over_opens S I U (fun i => (t i).A) (fun i j => (u i j).A) a a'
    (fun i j => (ha i j).1.1) (fun i j => (ha' i j).1.1) hcoc
  have hgl := _root_.GlobalTheory.CoverOpCompat.opCompat S I U A (fun i => (t i).A) ψ (fun i j => (u i j).A) a a' hp
    (fun i j => (ha i j).1) (fun i j => (ha' i j).1) hB
  obtain ⟨m, hm⟩ := _root_.GlobalTheory.CoverGlue.exists_binary_op S I U A (fun i => (t i).A) ψ (fun i => μ) hU hp
    (fun i j T r r' x y x' y' hx hy => by
      simpa only [Hom.mul_def] using (hgl.1 i j T r r' x y x' y' hx hy).1)
  obtain ⟨n, hn⟩ := _root_.GlobalTheory.CoverGlue.exists_binary_op S I U A (fun i => (t i).A) ψ (fun i => fst _ _ ≫ ι) hU hp
    (fun i j T r r' x y x' y' hx hy => by
      simpa only [lift_fst_assoc, Hom.inv_def] using (hgl.1 i j T r r' x y x' y' hx hy).2)
  obtain ⟨e, he⟩ := exists_section_of_compatible_local_sections hU hp (fun i => (1 : Out.baseOver (U i).toScheme ⟶ (t i).A)) hgl.2
  obtain ⟨inst, hgp⟩ := _root_.GlobalTheory.CoverGlue.exists_grpObj_of_cover S I U A (fun i => (t i).A) ψ m n e hU hp
    (fun i T x y x₀ y₀ hx hy => ⟨by simpa only [Hom.mul_def] using hm i T x y x₀ y₀ hx hy,
      by simpa only [lift_fst_assoc, Hom.inv_def] using hn i T x y x₀ y₀ hx hy⟩) he
  have hab := _root_.GlobalTheory.CoverGlue.isAbelianScheme_and_relDim_of_cover S I U A (fun i => (t i).A) ψ hU hgp
  have hA : IsAbelianScheme A := hab.1 (fun i => (t i).ab)
  obtain ⟨L, hL, hrigL, hLi⟩ := _root_.GlobalTheory.RigidBundleGlue.exists_glue S I U A (fun i => (t i).A) ψ hU hgp hA (fun i => (t i).ab)
    (fun i => (t i).L) (fun i j => (u i j).A.left) a a' hB (fun i => (t i).isLB) (fun i => (t i).rigid)
    (fun i j => LBIso.trans (pull_isLB (t i).isLB _) (u i j).isLB (pull_isLB (t j).isLB _)
      (ha i j).2.1.symm (ha' i j).2.1)
  choose P hP using fun l => exists_section_of_compatible_local_sections hU hp (fun i => (t i).pt l) (fun i j => by
    rw [← Category.assoc, ← (ha i j).2.2.1 l, Category.assoc, (hB i j).w, ← Category.assoc,
      (ha' i j).2.2.1 l, Category.assoc])
  choose F hF using fun w => exists_endo_of_compatible_local_endos hU hp hB (fun i => (t i).act w) (fun i j => by
    rw [← Category.assoc, ← (ha i j).2.2.2 w, Category.assoc, (hB i j).w, ← Category.assoc,
      (ha' i j).2.2.2 w, Category.assoc])
  have h82 := _root_.GlobalTheory.CoverGlue.tors_and_isMonHom_of_cover S I U A (fun i => (t i).A) ψ hU hgp hA (fun i => (t i).ab)
  have hsym := GlobalTheory.T.symmetric_local_on_base_cover S I U A (fun i => (t i).A) ψ hU hgp L (fun i => (t i).L) hL
    (fun i => (t i).isLB) hLi (fun i => (t i).sym)
  have hamp := _root_.GlobalTheory.CoverGlue.relAmple_of_cover S I U A (fun i => (t i).A) ψ hU hgp L (fun i => (t i).L) hL
    (fun i => (t i).isLB) hLi hA (fun i => (t i).ab) (fun i => (t i).ample)
  have hkt := _root_.GlobalTheory.CoverGlue.kTriv_of_cover S I U A (fun i => (t i).A) ψ hU hgp L (fun i => (t i).L) hL
    (fun i => (t i).isLB) hLi hA (fun i => (t i).ab) (fun i => (t i).ktriv)
  have htor : ∀ l, P l ^ k = 1 := fun l =>
    h82.1 k (P l) (fun i => (t i).pt l) (fun i => hP l i) (fun i => (t i).torsion l)
  have hbij := _root_.GlobalTheory.CoverGlue.torsionBasis_of_cover S I U A (fun i => (t i).A) ψ hU hgp hA (fun i => (t i).ab) g k P
    (fun i => (t i).pt) (fun i l => hP l i) (fun i => (t i).bij)
  have hunit : ∀ i, Units.map (U i).ι.appTop.hom.toMonoidHom (unitS s b.ζ) = unitS ((U i).ι ≫ s) b.ζ :=
    fun i => hcompl_unit_property_of_isPrime (U i).ι s b.ζ
  have hpair : ∀ l l', Out.WeilIs A L k (P l) (P l') (unitS s b.ζ ^ Out.stdSymp g l l') := fun l l' =>
    _root_.GlobalTheory.weilIs_of_openCover S I U A (fun i => (t i).A) ψ hU hgp L (fun i => (t i).L) hL
      (fun i => (t i).isLB) hLi hA (fun i => (t i).ab) k (P l) (P l') (fun i => (t i).pt l)
      (fun i => (t i).pt l') _ (fun i => hP l i) (fun i => hP l' i) (fun i => by
        rw [map_zpow, hunit i]
        exact (t i).pairing l l')
  have hhom : ∀ w, IsMonHom (F w) := fun w =>
    h82.2 (F w) (fun i => (t i).act w) (fun i => hF w i) (fun i => (t i).hom w)
  let t₀ : TObj g k J b s :=
    { A := A
      grp := inst
      ab := hA
      dim := hab.2 g (fun i => (t i).dim)
      L := L
      isLB := hL
      rigid := hrigL
      sym := hsym
      ample := hamp
      ktriv := hkt
      pt := P
      torsion := htor
      bij := hbij
      pairing := hpair
      act := F
      hom := hhom }
  exact ⟨t₀, fun i => ⟨ψ i, hgp i, hLi i, fun l => hP l i, fun w => hF w i⟩⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.PowLeftCompOfGrpPullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.ZM.NearBuild

noncomputable section
namespace GlobalTheory.ZM.NearBuild

open GlobalTheory.ThetaObjPull

theorem pow_left_comp_of_grpPullback {S S' : Scheme.{0}} {f : S' ⟶ S} {A : Over S} {A' : Over S'} [GrpObj A]
    [GrpObj A'] {φ : A'.left ⟶ A.left} (h : IsGrpPullback A' A f φ) (x' : Out.baseOver S' ⟶ A')
    (x : Out.baseOver S ⟶ A) (e : x'.left ≫ φ = f ≫ x.left) (n : ℕ) :
    (x' ^ n).left ≫ φ = f ≫ (x ^ n).left := by
  have e₁ : pushHom h _ x' = toBase f ≫ x := Over.OverMorphism.ext e
  have e₂ : pushHom h _ (x' ^ n) = toBase f ≫ (x ^ n) := by
    rw [map_pow, e₁]
    exact (map_pow (preHom (toBase f)) _ _).symm
  exact congrArg (fun z => z.left) e₂

theorem gLies_pull : ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (S S₁ S₂ : Scheme.{0}) (A : Over S) [GrpObj A] (L : LB A.left) (act : J → (A ⟶ A)) (Q : Fin (2 * g) → (Out.baseOver S ⟶ A)) (c : S₁ ⟶ S) (s₁ : S₁ ⟶ Sp o) (t₁ : TObj g (N' ^ 2) J b s₁) (ψ₁ : t₁.A.left ⟶ A.left) (y : S₂ ⟶ S₁) (s₂ : S₂ ⟶ Sp o), L.IsLB → GLies A act Q c t₁ ψ₁ → LBIso t₁.L (L.pull ψ₁) → y ≫ s₁ = s₂ → ∃ (u : TObj g (N' ^ 2) J b s₂) (ψ : u.A.left ⟶ A.left), TMap u t₁ y ∧ GLies A act Q (y ≫ c) u ψ ∧ LBIso u.L (L.pull ψ) ∧ ∀ i, (u.pt i).left ≫ ψ = y ≫ (t₁.pt i).left ≫ ψ₁ := by
  intro o _ g N' J b S S₁ S₂ A _ L act Q c s₁ t₁ ψ₁ y s₂ hL ⟨h₁, h₂, h₃⟩ hI hs
  obtain ⟨u, φ, k₁, k₂, k₃, k₄⟩ := GlobalTheory.tObj_pull o g (N' ^ 2) J b S₁ S₂ s₁ s₂ y t₁ hs
  refine ⟨u, φ ≫ ψ₁, ⟨φ, k₁, k₂, k₃, k₄⟩, ⟨k₁.comp h₁, fun i => ?_, fun i => ?_⟩, ?_, fun i => ?_⟩
  · rw [← Category.assoc, k₄, Category.assoc, h₂, Category.assoc]
  · rw [← Category.assoc, pow_left_comp_of_grpPullback k₁ _ _ (k₃ i), Category.assoc, h₃, Category.assoc]
  · exact LBIso.trans u.isLB (pull_isLB t₁.isLB _) (pull_isLB hL _) k₂ (lbIso_pull_comp hI φ)
  · rw [← Category.assoc, k₃, Category.assoc]

end GlobalTheory.ZM.NearBuild
end
end

