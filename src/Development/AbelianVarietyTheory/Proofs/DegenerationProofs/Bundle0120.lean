module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsCoprimeTwoSubRtTwoAddRt
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
public import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0111
public import Development.AbelianVarietyTheory.Definitions.Degenerations.LocTheta
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
public import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0073
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSecImageNonzeroLocus
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
public import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsDescentSubring
section
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Ex
open scoped BigOperators

namespace GlobalTheory.Ex

theorem NumD.exists_descent_subring : ∀ (O F : Type) [CommRing O] [CommRing F] (io : O →+* F), Function.Injective io → ∀ (N : NumD F) (A₀ : Subgroup N.A), (∀ χ, N.c χ ∈ A₀) → (∀ x ∈ A₀, ∀ y ∈ A₀, ∀ u ∈ A₀, ∃ a : Oˣ, io a = N.θ x y u) → (∀ x ∈ A₀, ∃ a : Oˣ, io a = N.σ x) → (∀ x ∈ A₀, ∃ a : O, io a = N.th x) → (∀ χ, ∃ a : Oˣ, io a = N.ψ χ) → ∃ (N₀ : NumD O) (I : NumD.Hom io N₀ N), I.lam = 1 ∧ ∀ (k : ℕ) (p : N.QT k), p.1.2.b ∈ A₀ → (∀ χ, ∃ a : Oˣ, io a = p.1.2.s χ) → ∃ p₀ : N₀.QT k, p.1.1.toAdd = I.e p₀.1.1.toAdd ∧ I.Rel p₀.1.2 p.1.2 := by
  intro O F _ _ io hio N A₀ hc hθ hσ hth hψ
  have hθ' : ∀ x y u : A₀, ∃ a : Oˣ, Units.map io.toMonoidHom a = N.θ x y u := fun x y u =>
    (hθ x x.2 y y.2 u u.2).imp fun a h => Units.ext h
  have hσ' : ∀ x : A₀, ∃ a : Oˣ, Units.map io.toMonoidHom a = N.σ x := fun x =>
    (hσ x x.2).imp fun a h => Units.ext h
  have hth' : ∀ x : A₀, ∃ a : O, io a = N.th x := fun x => hth x x.2
  have hψ' : ∀ χ, ∃ a : Oˣ, Units.map io.toMonoidHom a = N.ψ χ := fun χ =>
    (hψ χ).imp fun a h => Units.ext h
  choose θ eθ using hθ'
  choose σ eσ using hσ'
  choose th eth using hth'
  choose ψ eψ using hψ'
  have inj : Function.Injective (Units.map io.toMonoidHom) := Units.map_injective hio
  let B₀ : NumB O :=
    { A := A₀
      θ := θ
      cub :=
        { face := fun x y => inj (by rw [eθ, map_one]; exact N.cub.face _ _)
          s01 := fun x y z => inj (by rw [eθ, eθ]; exact N.cub.s01 _ _ _)
          s12 := fun x y z => inj (by rw [eθ, eθ]; exact N.cub.s12 _ _ _)
          coc := fun x x' x'' y => inj (by simp only [map_mul, eθ]; exact N.cub.coc _ _ _ _) }
      σ := σ
      σ_one := inj (by rw [eσ, map_one]; exact N.σ_one)
      σ_mul := fun x y => inj (by simp only [map_mul, eθ, eσ]; exact N.σ_mul _ _)
      th := th }
  let N₀ : NumD O :=
    { toNumB := B₀
      X := N.X
      c := fun χ => (⟨N.c χ, hc χ⟩ : A₀)
      c_add := fun a b => Subtype.ext (N.c_add a b)
      ψ := ψ
      even := fun χ => inj (by
        change Units.map io.toMonoidHom (ψ (-χ) * σ ⟨N.c χ, hc χ⟩) = _
        simp only [map_mul, eψ, eσ]; exact N.even χ)
      bimult := fun a a' b => inj (by
        change Units.map io.toMonoidHom (_ * θ ⟨N.c a, hc a⟩ ⟨N.c a', hc a'⟩ ⟨N.c b, hc b⟩) = _
        simp only [map_mul, map_div, eψ, eθ]; exact N.bimult a a' b) }
  let I : NumD.Hom io N₀ N :=
    { φ := A₀.subtype
      h := fun _ => 1
      h_one := rfl
      θ_eq := fun (x y u : A₀) => by
        simp only [mul_one]; exact (eθ x y u).symm
      σ_eq := fun (x : A₀) => by
        simp only [mul_one]; exact (eσ x).symm
      lam := 1
      th_eq := fun (x : A₀) => by
        simp only [mul_one, Units.val_one, one_mul]; exact (eth x).symm
      e := AddEquiv.refl N.X
      c_eq := fun _ => rfl
      ψ_eq := fun (χ : N.X) => by
        simp only [mul_one]; exact (eψ χ).symm }
  let Φ : N₀.Gt →* N.Gt := MonoidHom.mk'
    (fun g => ⟨((show A₀ from g.b) : N.A), fun (χ : N.X) => Units.map io.toMonoidHom (g.s χ), fun (χ χ' : N.X) => by
      have := congrArg (Units.map io.toMonoidHom) (g.mult χ χ')
      rw [map_mul, map_mul] at this
      rw [← this]
      exact congrArg _ (eθ ⟨N.c χ, hc χ⟩ ⟨N.c χ', hc χ'⟩ g.b).symm⟩)
    (fun g g' => NumD.Gt.ext rfl (funext fun (χ : N.X) => by
      change Units.map io.toMonoidHom (g.s χ * g'.s χ / θ ⟨N.c χ, hc χ⟩ g.b g'.b) = _
      rw [map_div, map_mul, eθ]; rfl))
  have Φinj : Function.Injective Φ := fun g g' h =>
    NumD.Gt.ext (Subtype.ext (congrArg NumD.Gt.b h))
      (funext fun (χ : N.X) => inj (congrArg (fun z : N.Gt => z.s χ) h))
  have Φio : ∀ y : N.X, Φ (N₀.io y) = N.io y := fun y =>
    NumD.Gt.ext rfl (funext fun (χ : N.X) => by
      change Units.map io.toMonoidHom (ψ (y + χ) / ψ y / ψ χ) = _
      rw [map_div, map_div, eψ, eψ, eψ]; rfl)
  refine ⟨N₀, I, rfl, fun k p hb hs => ?_⟩
  have hs' : ∀ χ, ∃ a : Oˣ, Units.map io.toMonoidHom a = p.1.2.s χ := fun χ =>
    (hs χ).imp fun a h => Units.ext h
  choose s es using hs'
  let g₀ : N₀.Gt := ⟨(⟨p.1.2.b, hb⟩ : A₀), s, fun (χ χ' : N.X) => inj (by
    change Units.map io.toMonoidHom (s (χ + χ') * θ ⟨N.c χ, hc χ⟩ ⟨N.c χ', hc χ'⟩ ⟨p.1.2.b, hb⟩) = _
    simp only [map_mul, es, eθ]; exact p.1.2.mult χ χ')⟩
  have hg : Φ g₀ = p.1.2 := NumD.Gt.ext rfl (funext fun χ => es χ)
  refine ⟨⟨(p.1.1, g₀), Φinj ?_⟩, rfl, rfl, fun (χ : N.X) => ?_⟩
  · change Φ (g₀ ^ k) = Φ (N₀.io (show N.X from p.1.1.toAdd))
    rw [map_pow, hg, Φio]; exact p.2
  · change p.1.2.s χ * 1 = Units.map io.toMonoidHom (s χ) * 1 * 1
    rw [es, mul_one, mul_one]

end GlobalTheory.Ex
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFullZetaEq
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ReZeta

theorem exists_exponent {K : Type} [Field K] (ξ ζ : ℕ → Kˣ) (hξ : ∀ n, 0 < n → IsPrimitiveRoot (ξ n) n)
    (hξ' : ∀ n m, 0 < n → 0 < m → ξ (n * m) ^ m = ξ n) (hζ : ∀ n, 0 < n → IsPrimitiveRoot (ζ n) n)
    (hζ' : ∀ n m, 0 < n → 0 < m → ζ (n * m) ^ m = ζ n) :
    ∃ ν : ℕ → ℤ, (∀ n, 0 < n → ξ n ^ ν n = ζ n) ∧ (∀ n : ℕ, 0 < n → IsCoprime (ν n) (n : ℤ)) ∧
      ∀ n m : ℕ, 0 < n → 0 < m → (n : ℤ) ∣ ν (n * m) - ν n := by
  have h : ∀ n : ℕ, ∃ i : ℕ, 0 < n → ξ n ^ i = ζ n := fun n => by
    by_cases hn : 0 < n
    · haveI : NeZero n := ⟨hn.ne'⟩
      obtain ⟨i, -, hi⟩ := (hξ n hn).eq_pow_of_mem_rootsOfUnity
        ((mem_rootsOfUnity n (ζ n)).2 (hζ n hn).pow_eq_one)
      exact ⟨i, fun _ => hi⟩
    · exact ⟨0, fun h => absurd h hn⟩
  choose i hi using h
  refine ⟨fun n => i n, fun n hn => by rw [zpow_natCast, hi n hn], fun n hn => ?_, fun n m hn hm => ?_⟩
  · exact Nat.isCoprime_iff_coprime.2 (((hξ n hn).pow_iff_coprime hn _).1 (hi n hn ▸ hζ n hn))
  · rw [← (hξ n hn).zpow_eq_one_iff_dvd, zpow_sub, zpow_natCast, zpow_natCast, hi n hn, mul_inv_eq_one,
      ← hξ' n m hn hm, ← pow_mul, mul_comm m, pow_mul, hi _ (Nat.mul_pos hn hm), hζ' n m hn hm]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem modN_smul (D : Datum H) {n : ℕ} {c : 𝓞 E} (h : (n : 𝓞 E) ∣ c) (a : D.La) : D.ModN n (c • a) := by
  obtain ⟨b, rfl⟩ := h
  exact ⟨b • a, by rw [mul_smul, Nat.cast_smul_eq_nsmul]⟩

theorem exists_sim (D : Datum H) (ν : ℕ → ℤ) (h₁ : ∀ n : ℕ, 0 < n → IsCoprime (ν n) (n : ℤ))
    (h₂ : ∀ n m : ℕ, 0 < n → 0 < m → (n : ℤ) ∣ ν (n * m) - ν n) : ∃ g : Sim D, g.ν = ν := by
  obtain ⟨t, ht₁, ht₂, -⟩ := GlobalTheory.NormTower.exists_norm_tower E H (GlobalTheory.HostModel.level H 1 one_pos) ν h₁ h₂
  refine ⟨⟨fun n => t n • LinearMap.id, ν, fun n m hn hm a => ?_, fun n hn => ?_, fun n hn a b => ?_⟩, rfl⟩
  · simp only [LinearMap.smul_apply, LinearMap.id_apply]
    rw [← sub_smul]
    exact modN_smul D (ht₂ n m hn hm) a
  · obtain ⟨u, v, huv⟩ := h₁ n hn
    obtain ⟨c, hc⟩ := ht₁ n hn
    have huv' : (u : 𝓞 E) * (ν n : 𝓞 E) + (v : 𝓞 E) * (n : 𝓞 E) = 1 := by
      exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 E) huv
    have hd : (n : 𝓞 E) ∣ (u : 𝓞 E) * H.bar (t n) * t n - 1 :=
      ⟨u * c - v, by linear_combination (u : 𝓞 E) * hc + huv'⟩
    refine ⟨((u : 𝓞 E) * H.bar (t n)) • LinearMap.id, fun a => ?_⟩
    simp only [LinearMap.smul_apply, LinearMap.id_apply]
    have := modN_smul D hd a
    rw [sub_smul, one_smul] at this
    exact ⟨by rwa [← mul_smul], by rwa [← mul_smul, mul_comm]⟩
  · simp only [LinearMap.smul_apply, LinearMap.id_apply]
    obtain ⟨c, hc⟩ := ht₁ n hn
    have e : H.bar (t n) * t n = (ν n : 𝓞 E) + (n : 𝓞 E) * c := by linear_combination hc
    refine ⟨D.EF a (c • b), ?_⟩
    rw [D.adj, ← mul_smul, e, add_smul, mul_smul, Int.cast_smul_eq_zsmul, Nat.cast_smul_eq_nsmul, map_add (f := _),
      map_zsmul, map_nsmul, smul_eq_mul, nsmul_eq_mul, add_sub_cancel_left]

end GlobalTheory.ReZeta
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLevelOfFull
section
set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

noncomputable section

namespace GlobalTheory.FullLevel

section Abstract

variable {G L : Type} [CommGroup G] [AddCommGroup L] {r n : ℕ} {ev : L → G}

theorem ev_basis (add : ∀ a b, ev (a + b) = ev a * ev b) (bas : (Fin r → ℤ) ≃ₗ[ℤ] L) (c : Fin r → ℤ) :
    ev (bas c) = ∏ i, ev (bas (Pi.single i 1)) ^ c i := by
  let f : L →+ Additive G := AddMonoidHom.mk' (fun a => Additive.ofMul (ev a)) fun a b => by rw [add, ofMul_mul]
  have hc : c = ∑ i, c i • (Pi.single i 1 : Fin r → ℤ) := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  have h : f (bas c) = ∑ i, c i • f (bas (Pi.single i 1)) := by
    conv_lhs => rw [hc]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_zsmul]
  have h' := congrArg Additive.toMul h
  rw [toMul_sum] at h'
  simp only [toMul_zsmul] at h'
  exact h'

theorem card_torsion (hn : 0 < n) (add : ∀ a b, ev (a + b) = ev a * ev b) (ker : ∀ a, ev a = 1 ↔ ∃ b, a = n • b)
    (onto : ∀ x, x ^ n = 1 ↔ ∃ a, ev a = x) (bas : (Fin r → ℤ) ≃ₗ[ℤ] L) :
    Nat.card {x : G // x ^ n = 1} = n ^ r := by
  let f : (Fin r → Fin n) → {x : G // x ^ n = 1} := fun c => ⟨ev (bas fun i => (c i : ℕ)), (onto _).2 ⟨_, rfl⟩⟩
  have hn' : (0 : ℤ) < n := by exact_mod_cast hn
  have hb : Function.Bijective f := by
    refine ⟨fun c c' h => ?_, fun x => ?_⟩
    · have h₁ : ev (bas fun i => (c i : ℕ)) = ev (bas fun i => (c' i : ℕ)) := congrArg Subtype.val h
      have h₂ := add (bas (fun i => (c i : ℕ)) - bas fun i => (c' i : ℕ)) (bas fun i => (c' i : ℕ))
      rw [sub_add_cancel, h₁] at h₂
      obtain ⟨b, hb⟩ := (ker _).1 (mul_eq_right.1 h₂.symm)
      obtain ⟨b, rfl⟩ := bas.surjective b
      rw [← map_sub, ← map_nsmul] at hb
      funext i
      have h₃ : ((c i : ℕ) : ℤ) - (c' i : ℕ) = n * b i := by simpa using congrFun (bas.injective hb) i
      have h₄ : ((c' i : ℕ) : ℤ) ≡ (c i : ℕ) [ZMOD n] := (Int.modEq_iff_dvd).2 ⟨_, h₃⟩
      exact Fin.ext (Nat.ModEq.eq_of_lt_of_lt (Int.natCast_modEq_iff.1 h₄) (c' i).2 (c i).2).symm
    · obtain ⟨a, ha⟩ := (onto _).1 x.2
      obtain ⟨a, rfl⟩ := bas.surjective a
      have h₀ : ∀ i, 0 ≤ a i % n := fun i => Int.emod_nonneg _ hn'.ne'
      refine ⟨fun i => ⟨(a i % n).toNat, by have := Int.emod_lt_of_pos (a i) hn'; have := h₀ i; omega⟩,
        Subtype.ext ?_⟩
      have e : a = (fun i => (((a i % n).toNat : ℕ) : ℤ)) + n • fun i => a i / n := by
        funext i
        simp only [Pi.add_apply, Pi.smul_apply, nsmul_eq_mul, Int.toNat_of_nonneg (h₀ i)]
        exact (Int.emod_add_mul_ediv _ _).symm
      rw [← ha]
      conv_rhs => rw [e, map_add (f := _), add, map_nsmul, (ker _).2 ⟨_, rfl⟩, _root_.mul_one]
  rw [← Nat.card_eq_of_bijective f hb]
  simp

end Abstract

end GlobalTheory.FullLevel

namespace GlobalTheory


open FullLevel in
theorem exists_level_of_full : Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), ∀ (g : ℕ) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La), (∀ i j, D.EF (bas (Pi.single i 1)) (bas (Pi.single j 1)) = stdSymp g i j) → ∀ (K : Type) [Field K] [IsAlgClosed K] (o : Full D K) (M : ℕ), 0 < M → ∃ (hg : o.P.g = g) (lev : Out.Level o.P M (unitOn (o.I.ζ M))), (∀ i, levelBasis lev hg i = o.I.ev M (bas (Pi.single i 1))) ∧ ∀ c : Fin (2 * g) → ℤ, levelPoint lev hg (fun i => (c i : ZMod M)) = o.I.ev M (bas c) := by
  intro hL E _ _ _ H D g bas hb K _ _ o M hM
  have := o.charZero
  have := o.P.isAb.comm
  have : NeZero M := ⟨hM.ne'⟩
  have hg : o.P.g = g := by
    have h₁ := (hL.mulN _ o.P 2 one_le_two).2.2.2.2 K (𝟙 _) (by norm_num)
    have h₂ := card_torsion (G := baseOver (Sp K) ⟶ o.P.A) two_pos (o.I.add 2) (o.I.ker 2 two_pos)
      (o.I.onto 2 two_pos) bas
    have h₃ := Nat.pow_right_injective le_rfl (h₁.symm.trans h₂)
    omega
  subst hg
  have prim : ∀ {R : Type} [CommRing R] [Nontrivial R] (φ : K →+* R),
      IsPrimitiveRoot (Units.map φ.toMonoidHom (o.I.ζ M)) M := fun φ =>
    (o.I.ζ_prim M hM).map_of_injective (f := Units.map φ.toMonoidHom) (Units.map_injective φ.injective)
  have nt : ∀ (F : Type) [Field F], Nontrivial Γ(Spec (CommRingCat.of F), ⊤) := fun F _ =>
    (Scheme.ΓSpecIso (CommRingCat.of F)).commRingCatIsoToRingEquiv.toEquiv.nontrivial
  have tor : ∀ a, o.I.ev M a ^ M = 1 := fun a => (o.I.onto M hM _).2 ⟨a, rfl⟩
  obtain ⟨lev, hlev⟩ := exists_level_of_pairing hL.globalFns hL.weil hL.mulN (Sp K) o.P M (unitOn (o.I.ζ M))
    (by have := nt K; exact prim (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)
    (fun F _ s => by
      have := nt F
      refine ⟨?_, prim (s.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)⟩
      have : CharZero F := charZero_of_injective_ringHom (Spec.preimage s).hom.injective
      exact Nat.cast_ne_zero.2 hM.ne')
    (fun i => o.I.ev M (bas (Pi.single i 1))) (fun i => tor _)
    (fun i j => by
      have h := o.I.isom M hM (bas (Pi.single i 1)) (bas (Pi.single j 1))
      rw [hb] at h
      have e : unitOn (o.I.ζ M ^ stdSymp o.P.g i j) = unitOn (o.I.ζ M) ^ stdSymp o.P.g i j := map_zpow _ _ _
      exact e ▸ h)
  refine ⟨rfl, lev, fun i => congrFun hlev i, fun c => ?_⟩
  rw [levelPoint_rfl, Level.toPt, hlev, ev_basis (G := baseOver (Sp K) ⟶ o.P.A) (o.I.add M) bas c, linComb,
    List.prod_ofFn]
  exact Finset.prod_congr rfl fun i _ => by rw [← zpow_natCast, ZMod.val_intCast, ← zpow_eq_zpow_emod' _ (tor _)]

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLimitPointTateIsoSequence
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

namespace GlobalTheory.Ex.TateLimit

theorem exists_finite_reps (L : Type) [AddCommGroup L] [Module.Finite ℤ L] {M : ℕ} (hM : 0 < M) :
    ∃ (A : Type) (_ : Finite A) (r : A → L), ∀ a, ∃ x b, a = r x + M • b := by
  let N : Submodule ℤ L := LinearMap.range ((M : ℤ) • (LinearMap.id : L →ₗ[ℤ] L))
  have hfin : Finite (L ⧸ N) := by
    refine Module.finite_of_fg_torsion _ fun x => ⟨⟨(M : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hM.ne')⟩, ?_⟩
    obtain ⟨y, rfl⟩ := N.mkQ_surjective x
    change (M : ℤ) • N.mkQ y = 0
    rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact ⟨y, rfl⟩
  refine ⟨L ⧸ N, hfin, Quotient.out, fun a => ⟨Submodule.Quotient.mk a, ?_⟩⟩
  have h : a - Quotient.out (Submodule.Quotient.mk a : L ⧸ N) ∈ N :=
    (Submodule.Quotient.eq N).1 (Quotient.out_eq (Submodule.Quotient.mk a : L ⧸ N)).symm
  obtain ⟨b, hb⟩ := h
  refine ⟨b, ?_⟩
  have : M • b = a - Quotient.out (Submodule.Quotient.mk a : L ⧸ N) := by
    rw [← hb]; simp
  rw [this]; abel

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
  {k : Type} [Field k] {Q : Type} [Group Q] {act : 𝓞 E → Q → Q} {e : ℕ → Q → Q → kˣ → Prop}

theorem ev_add_nsmul (I : TateIso D k Q act e) {M : ℕ} (hM : 0 < M) (a b : D.La) : I.ev M (a + M • b) = I.ev M a := by
  rw [I.add, (I.ker M hM _).2 ⟨b, rfl⟩, _root_.mul_one]

theorem finite_level {M : ℕ} (hM : 0 < M) :
    (Set.range fun I : TateIso D k Q act e => (I.ev M, I.ζ M)).Finite := by
  rcases isEmpty_or_nonempty (TateIso D k Q act e) with h | ⟨⟨I₀⟩⟩
  · exact Set.finite_range _
  haveI := D.fin
  haveI : Module.Finite ℤ D.La := Module.Finite.trans (𝓞 E) D.La
  obtain ⟨A, hA, r, hr⟩ := exists_finite_reps D.La hM
  have hT : {x : Q | x ^ M = 1}.Finite := by
    refine (Set.finite_range fun x => I₀.ev M (r x)).subset fun x hx => ?_
    obtain ⟨a, rfl⟩ := (I₀.onto M hM x).1 hx
    obtain ⟨y, b, rfl⟩ := hr a
    exact ⟨y, (ev_add_nsmul I₀ hM _ _).symm⟩
  have h₁ : (Set.range fun I : TateIso D k Q act e => I.ev M).Finite := by
    refine Set.Finite.of_finite_image (f := fun f => f ∘ r) ?_ ?_
    · refine (Set.Finite.pi' fun _ : A => hT).subset ?_
      rintro _ ⟨_, ⟨I, rfl⟩, rfl⟩ x
      exact (I.onto M hM _).2 ⟨_, rfl⟩
    · rintro _ ⟨I, rfl⟩ _ ⟨J, rfl⟩ h
      funext a
      obtain ⟨y, b, rfl⟩ := hr a
      simp only [ev_add_nsmul _ hM]
      exact congrFun h y
  have h₂ : (Set.range fun I : TateIso D k Q act e => I.ζ M).Finite := by
    haveI : NeZero M := ⟨hM.ne'⟩
    have hfin : Finite (rootsOfUnity M k) := inferInstance
    refine Set.Finite.subset (s := (rootsOfUnity M k : Set kˣ)) hfin ?_
    rintro _ ⟨I, rfl⟩
    exact (I.ζ_prim M hM).pow_eq_one
  refine (h₁.prod h₂).subset ?_
  rintro _ ⟨I, rfl⟩
  exact ⟨⟨I, rfl⟩, ⟨I, rfl⟩⟩

theorem exists_limit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), ∀ (k : Type) [Field k] (Q : Type) [Group Q] (act : 𝓞 E → Q → Q) (e : ℕ → Q → Q → kˣ → Prop) (I : ℕ → TateIso D k Q act e), ∃ I' : TateIso D k Q act e, ∀ M, 0 < M → ∀ j₀, ∃ j, j₀ ≤ j ∧ I'.ev M = (I j).ev M ∧ I'.ζ M = (I j).ζ M := by
  intro E _ _ _ H D k _ Q _ act e I
  let U : Ultrafilter ℕ := Filter.hyperfilter ℕ
  have key : ∀ M, ∃ p : (D.La → Q) × kˣ, (∃ j, p.1 = (I j).ev M) ∧
      (0 < M → ∀ᶠ j in (U : Filter ℕ), p.1 = (I j).ev M ∧ p.2 = (I j).ζ M) := by
    intro M
    rcases Nat.eq_zero_or_pos M with rfl | hM
    · exact ⟨((I 0).ev 0, 1), ⟨0, rfl⟩, fun h => absurd h (lt_irrefl _)⟩
    obtain ⟨p, -, hp⟩ := Ultrafilter.eq_pure_of_finite_mem (f := U.map fun j => ((I j).ev M, (I j).ζ M))
      (finite_level (D := D) (act := act) (e := e) hM)
      (Ultrafilter.mem_map.2 (Filter.univ_mem' fun j => ⟨I j, rfl⟩))
    have h : ∀ᶠ j in (U : Filter ℕ), p.1 = (I j).ev M ∧ p.2 = (I j).ζ M := by
      have : {p} ∈ U.map fun j => ((I j).ev M, (I j).ζ M) := by rw [hp]; exact Ultrafilter.mem_pure.2 rfl
      filter_upwards [Ultrafilter.mem_coe.2 (Ultrafilter.mem_map.1 this)] with j hj
      have hj' : ((I j).ev M, (I j).ζ M) = p := hj
      rw [← hj']; exact ⟨rfl, rfl⟩
    exact ⟨p, h.exists.imp fun _ h => h.1, fun _ => h⟩
  choose p hp₀ hp using key
  have one : ∀ n, 0 < n → ∃ j, (p n).1 = (I j).ev n ∧ (p n).2 = (I j).ζ n := fun n hn => (hp n hn).exists
  have two : ∀ n m, 0 < n → 0 < m → ∃ j, ((p n).1 = (I j).ev n ∧ (p n).2 = (I j).ζ n) ∧
      (p (n * m)).1 = (I j).ev (n * m) ∧ (p (n * m)).2 = (I j).ζ (n * m) := fun n m hn hm =>
    ((hp n hn).and (hp _ (Nat.mul_pos hn hm))).exists
  refine ⟨{ ζ := fun n => (p n).2
            ev := fun n => (p n).1
            ζ_prim := fun n hn => ?_
            ζ_pow := fun n m hn hm => ?_
            add := fun n a b => ?_
            lin := fun n c a => ?_
            ker := fun n hn a => ?_
            onto := fun n hn x => ?_
            tower := fun n m hn hm a => ?_
            isom := fun n hn a b => ?_ }, fun M hM j₀ => ?_⟩
  · obtain ⟨j, -, h⟩ := one n hn
    rw [h]; exact (I j).ζ_prim n hn
  · obtain ⟨j, ⟨-, h⟩, -, h'⟩ := two n m hn hm
    rw [h, h']; exact (I j).ζ_pow n m hn hm
  · obtain ⟨j, h⟩ := hp₀ n
    rw [h]; exact (I j).add n a b
  · obtain ⟨j, h⟩ := hp₀ n
    rw [h]; exact (I j).lin n c a
  · obtain ⟨j, h⟩ := hp₀ n
    rw [h]; exact (I j).ker n hn a
  · obtain ⟨j, h⟩ := hp₀ n
    rw [h]; exact (I j).onto n hn x
  · obtain ⟨j, ⟨h, -⟩, h', -⟩ := two n m hn hm
    rw [h, h']; exact (I j).tower n m hn hm a
  · obtain ⟨j, h, h'⟩ := one n hn
    rw [h, h']; exact (I j).isom n hn a b
  · have h : ∀ᶠ j in (U : Filter ℕ), j₀ ≤ j := Nat.hyperfilter_le_atTop (Filter.eventually_ge_atTop j₀)
    exact (h.and (hp M hM)).exists

end GlobalTheory.Ex.TateLimit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsRigidificationSpreadFromGenericFibre
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GenSpread

theorem exists_rigidified : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K] [IsFractionRing R K] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A] (φ : A.left ⟶ G.left) (L : LB G.left) (L₀ : LB A.left), IsAbelianScheme G → IsGrpPullback A G (spMap (algebraMap R K)) φ → L.IsLB → L₀.IsLB → LBIso L₀ (L.pull φ) → Rigidified A L₀ → ∃ a : R, a ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (g : R →+* R'), IsUnit (g a) → ∀ (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'] (π : G'.left ⟶ G.left) (L' : LB G'.left), IsGrpPullback G' G (spMap g) π → L'.IsLB → LBIso L' (L.pull π) → Rigidified G' L' := by
  intro R K _ _ _ _ _ _ G _ _ A _ _ φ L L₀ _ _ hL _ _ _
  obtain ⟨i, hi⟩ := exists_chart hL (eSec G (genericPoint (Sp R)))
  obtain ⟨a, ha, H⟩ := exists_forall_mem (R := R) (V := eSec G ⁻¹ᵁ L.U i) hi
  refine ⟨a, ha, fun R' _ g hg G' _ _ π L' h hL' ⟨w, hw⟩ => ?_⟩
  obtain ⟨t, ht⟩ := AbSquare.exists_gen_of_mem_chart hL (K := PUnit) (fun _ => eSec G' ≫ π) (fun _ => 1)
    (fun _ => i) (fun _ y => (congrArg (fun q => q y ∈ L.U i) (PolBaseChange.eSec_comm h)).mpr (H R' g hg y))
  exact exists_down ((isGen_iff w).1 hw) hL hL' t ht

end GlobalTheory.GenSpread
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTorsionPointSpecialFibreSectionNeZeroStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_torsionPoint_specialFibre_section_ne_zero : Laws → Laws2 → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (Q : ZHPre ρ M U₀), S.Big → ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (jV : u.V →+* OO p) (yV : Sp u.V ⟶ M.Z) (yK : Sp (FractionRing u.V) ⟶ U₀.toScheme), Q.TestFac y u jV yV yK → ∀ (F : u.G.left ⟶ Q.G.left) (ψ : pullback u.G.hom (jK u.V) ⟶ pullback ρ.P.A.hom Q.u₀), Q.TestMap u yV yK F ψ → LBIso (Q.L.L.pull F) u.U.LG.L → ∀ (N : M.Z.Opens) (σ : Q.SecFam N), σ ∈ secOn Q.LOne (Q.G.hom ⁻¹ᵁ N) → Q.FibNe N σ → y (cPt p) ∈ N → ∃ t : Over.mk (spMap (IsLocalRing.residue (OO p)) ≫ spMap jV) ⟶ u.G, t ^ (S.r * S.N) = 1 ∧ ∃ j, valF (X := Q.G.left) (t.left ≫ F) _ (σ j) ≠ 0 := by
  first | exact @GlobalTheory.ZH.TorsionNonzero.exists_torsion_valF_ne_zero | exact GlobalTheory.ZH.TorsionNonzero.exists_torsion_valF_ne_zero | (intros; apply GlobalTheory.ZH.TorsionNonzero.exists_torsion_valF_ne_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.RelAmpleOfFiniteEtaleIsogeny
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS

theorem relAmple_of_finite_etale_isogeny : ∀ (k : Type) [Field k] [IsAlgClosed k] (A B : Over (Sp k)) [GrpObj A] [GrpObj B], IsAbelianScheme A → IsAbelianScheme B → ∀ ψ : A ⟶ B, IsMonHom ψ → IsFinite ψ.left → Etale ψ.left → Surjective ψ.left → ∀ (L : LB A.left) (M : LB B.left), L.IsLB → M.IsLB → LBIso L (M.pull ψ.left) → Out.RelAmple A L → Out.RelAmple B M := by
  intro k _ _ A B _ _ hA hB ψ _ hf he hs L M hL hM hiso hamp
  have hN : IsLocallyNoetherian (Sp k) := inferInstanceAs (IsLocallyNoetherian (Spec (CommRingCat.of k)))
  have h₁ := (GlobalTheory.relAmple_finite_pow_iso (Sp k) A A (𝟙 A) L 1 one_pos hA hA hL
    (by simpa using (inferInstance : IsFinite (𝟙 A.left)))).2.2.2 (M.pull ψ.left) (LB.isLB_pull hM ψ.left) hiso hamp
  exact (GlobalTheory.relAmple_finite_pow_iso (Sp k) A B ψ M 1 one_pos hA hB hM hf).2.2.1 inferInstance hs h₁

end GlobalTheory.SS
end

