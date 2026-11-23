module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.ContCoef
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0032
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0021
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwJqEmbed
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0023

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.LocSub
section
open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL Formalism.BasicNotions
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z.Sym.Al

private theorem torusChar_injective {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {n : ℕ} {a b : Fin n → kˣ →* ℂˣ} (h : torusChar a = torusChar b) : a = b := by
  funext i
  ext x
  have e := DFunLike.congr_fun h (Pi.mulSingle i x)
  simp only [torusChar_apply] at e
  rw [Finset.prod_eq_single i (fun j _ hj => by simp [Pi.mulSingle_eq_of_ne hj]) (by simp),
    Finset.prod_eq_single i (fun j _ hj => by simp [Pi.mulSingle_eq_of_ne hj]) (by simp)] at e
  simpa using congrArg Units.val e

private theorem sdom_of_step {k : Type} [Field k] [ValuativeRel k] {n : ℕ} (s : Fin n → kˣ) (c : kˣ)
    (h1 : valuation k (c : k) ≤ 1)
    (h2 : ∀ i j : Fin n, i < j → valuation k (s i : k) * valuation k (c : k) < valuation k (s j : k)) :
    Sig.SDom fun i : Fin n => s i * c ^ (n - (i : ℕ)) := by
  intro i j hij
  have hj := j.2
  have hij' : (i : ℕ) < j := hij
  have e : n - (i : ℕ) = 1 + ((n - j) + (j - i - 1)) := by omega
  have hc0 : 0 < valuation k (c : k) := zero_lt_iff.2 ((valuation k).ne_zero_iff.2 c.ne_zero)
  beta_reduce
  rw [e]
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow, pow_add, pow_one]
  rw [← mul_assoc]
  calc valuation k (s i : k) * valuation k (c : k) *
        (valuation k (c : k) ^ (n - (j : ℕ)) * valuation k (c : k) ^ ((j : ℕ) - i - 1))
      ≤ valuation k (s i : k) * valuation k (c : k) * valuation k (c : k) ^ (n - (j : ℕ)) := by
        rw [← mul_assoc]
        exact mul_le_of_le_one_right' (pow_le_one' h1 _)
    _ < valuation k (s j : k) * valuation k (c : k) ^ (n - (j : ℕ)) :=
        mul_lt_mul_of_pos_right (h2 i j hij) (pow_pos hc0 _)

private theorem exists_sdom {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {n : ℕ} (t : Fin n → kˣ) :
    ∃ d : Fin n → kˣ, Sig.SDom d ∧ Sig.SDom (t * d) := by
  rcases isEmpty_or_nonempty (Fin n) with h | h
  · exact ⟨1, fun i => h.elim i, fun i => h.elim i⟩
  obtain ⟨p, hp⟩ := Finite.exists_min
    (fun p : Fin n × Fin n => valuation k ((t p.2 * (t p.1)⁻¹ : kˣ) : k))
  obtain ⟨x, q, hq, hx⟩ := UpperTheory.V.AlgebraTools.exists_isUnif (k := k)
  have hx1 : valuation k (x : k) < 1 := by
    have h0 : valuation k (q : k) ≤ 1 := q.2
    have hne : valuation k (q : k) ≠ 1 := fun h =>
      hq.not_isUnit ((Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one.2 h)
    rw [← hx]
    exact lt_of_le_of_ne h0 hne
  set c₀ : kˣ := t p.2 * (t p.1)⁻¹ with hc₀
  have hc1 : valuation k (c₀ : k) ≤ 1 := by simpa using hp (p.1, p.1)
  have hcx : valuation k ((c₀ * x : kˣ) : k) < 1 := by
    rw [Units.val_mul, map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' hc1) hx1
  refine ⟨fun i => (c₀ * x) ^ (n - (i : ℕ)), ?_, ?_⟩
  · simpa using sdom_of_step (1 : Fin n → kˣ) (c₀ * x) hcx.le fun i j _ => by simpa using hcx
  · refine sdom_of_step t (c₀ * x) hcx.le fun i j _ => ?_
    have hle : valuation k (t i : k) * valuation k (c₀ : k) ≤ valuation k (t j : k) := by
      refine (mul_le_mul_right (hp (i, j)) (valuation k (t i : k))).trans (le_of_eq ?_)
      rw [← map_mul, ← Units.val_mul]
      congr 2
      simp
    have hj0 : 0 < valuation k (t j : k) := zero_lt_iff.2 ((valuation k).ne_zero_iff.2 (t j).ne_zero)
    rw [Units.val_mul, map_mul, ← mul_assoc]
    calc valuation k (t i : k) * valuation k (c₀ : k) * valuation k (x : k)
        ≤ valuation k (t j : k) * valuation k (x : k) := mul_le_mul_left hle _
      _ < valuation k (t j : k) * 1 := mul_lt_mul_of_pos_left hx1 hj0
      _ = valuation k (t j : k) := mul_one _

theorem UpperTheory.V.Z.Sym.Al.locSub :
    GlobalTheory.Mem.LiteralAutomorphy.LitN → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ) (T : Type) [AddCommGroup T] [Module ℂ T] (τ : Representation ℂ (GL (Fin n) k) T),
                 IsSmooth τ → τ.IsIrreducible → ∀ v : T, v ≠ 0 → v ∈ Hi.fixd τ ((Sig.Lev.iw k).J n) →
                 (∀ d, Sig.SDom d → Hi.dc τ ((Sig.Lev.iw k).J n) ((Sig.Lev.iw k).J n) (Sig.dg d) v = expo ψ d • v) → IsSubquotient τ (prinSeries ψ) := by
  intro H k _ _ _ _ n ψ T _ _ τ hs hi v hv0 hvJ heig
  have hJ : (Sig.Lev.iw k).J n = UpperTheory.V.AlgebraTools.iwC k n ⊤ := (UpperTheory.V.Z.Sym.Sig.link k n).1
  rw [hJ] at hvJ heig
  have hq : IsUnit (resCard k : ℂ) := (Nat.cast_ne_zero.2 (Nat.card_pos (α := 𝓀[k])).ne').isUnit
  obtain ⟨θ, hθ, -⟩ := UpperTheory.V.AlgebraTools.thetaEx k n ⊤ ℂ T τ hq
  let δ : (Fin n → kˣ) →* ℂˣ := (deltaHalf k fun _ : Fin n => Unit).comp (leviTorus k (Fin n)).toMonoidHom
  let χ : (Fin n → kˣ) →* ℂˣ := torusChar ψ * δ⁻¹
  let w : Hi.fixd τ (UpperTheory.V.AlgebraTools.iwC k n ⊤) := ⟨v, hvJ⟩
  have hw0 : w ≠ 0 := fun h => hv0 (congrArg Subtype.val h)
  have hsd : ∀ d, Sig.SDom d →
      (θ d : Module.End ℂ (Hi.fixd τ (UpperTheory.V.AlgebraTools.iwC k n ⊤))) w = (χ d : ℂ) • w := by
    intro d hd
    have hD : UpperTheory.V.AlgebraTools.Dom d := fun i j hij => by
      rcases hij.eq_or_lt with rfl | h
      · exact le_rfl
      · exact (hd i j h).le
    rw [hθ d hD]
    refine Subtype.ext ?_
    have h1 := (UpperTheory.V.AlgebraTools.hkApply ℂ _ T τ _ _ (Sig.dg d)
      ((UpperTheory.V.AlgebraTools.heckePairIwC k n ⊤).1 (Sig.dg d))).1 w
    exact h1.trans (heig d hd)
  have ht : ∀ t, (θ t : Module.End ℂ (Hi.fixd τ (UpperTheory.V.AlgebraTools.iwC k n ⊤))) w = (χ t : ℂ) • w := by
    intro t
    obtain ⟨d, hd, htd⟩ := exists_sdom t
    have h1 := hsd d hd
    have h2 := hsd (t * d) htd
    rw [map_mul, Units.val_mul, Module.End.mul_apply, h1, map_smul, map_mul, Units.val_mul, mul_comm, mul_smul] at h2
    exact smul_right_injective _ (Units.ne_zero (χ d)) h2
  have hne : (⨅ t, Module.End.maxGenEigenspace (θ t : Module.End ℂ (Hi.fixd τ (UpperTheory.V.AlgebraTools.iwC k n ⊤))) (χ t : ℂ)) ≠ ⊥ := by
    refine (Submodule.ne_bot_iff _).2 ⟨w, (Submodule.mem_iInf _).2 fun t => ?_, hw0⟩
    refine (Module.End.mem_maxGenEigenspace _ _ _).2 ⟨1, ?_⟩
    simp [ht t]
  obtain ⟨ψ', -, -, e, h2⟩ := UpperTheory.V.AlgebraTools.jqEmbed H.loc.bz k n ⊤ T τ hs hi θ hθ χ hne
  have hψ : ψ' = ψ := torusChar_injective (e.trans (by
    change torusChar ψ * δ⁻¹ * δ = torusChar ψ
    simp))
  exact hψ ▸ h2
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.RegUnl
section
open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL Formalism.BasicNotions
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z.Sym.Al

private theorem ne_of_div {G : Type*} [CommGroup G] {p x y : G} (h₁ : x / y ≠ 1) (h₂ : x / y ≠ p) :
    x ≠ y ∧ x ≠ y * p :=
  ⟨fun h => h₁ (by rw [h, div_self']), fun h => h₂ (by rw [h, mul_div_cancel_left])⟩

private theorem inv_ne_of {G : Type*} [CommGroup G] {p x : G} (h : x ≠ p⁻¹) : x⁻¹ ≠ p :=
  fun e => h (by rw [← e, inv_inv])

private theorem triple {G : Type*} [CommGroup G] {a p : G} (h1 : a ≠ 1) (hp : a ≠ p) (hm : a ≠ p⁻¹)
    (s1 : a ^ 2 ≠ 1) (sp : a ^ 2 ≠ p) (sm : a ^ 2 ≠ p⁻¹) (i i' : Fin 3) (hne : i ≠ i') :
    (![a, 1, a⁻¹] : Fin 3 → G) i ≠ ![a, 1, a⁻¹] i' ∧ (![a, 1, a⁻¹] : Fin 3 → G) i ≠ ![a, 1, a⁻¹] i' * p := by
  have e02 : a / a⁻¹ = a ^ 2 := by rw [div_inv_eq_mul, pow_two]
  have e20 : a⁻¹ / a = (a ^ 2)⁻¹ := by rw [← e02, inv_div]
  fin_cases i <;> fin_cases i' <;> first
    | exact absurd rfl hne
    | (apply ne_of_div <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val, div_one, one_div, inv_inv, e02, e20]
       <;> first
         | exact h1 | exact hp | exact s1 | exact sp
         | exact inv_ne_one.2 h1 | exact inv_ne_one.2 s1
         | exact inv_ne_of hm | exact inv_ne_of sm)

theorem UpperTheory.V.Z.Sym.Al.regUnl :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a : kˣ →* ℂˣ), Reg a →
        ((∀ i, ∀ u ∈ Hi.Uo k, (![a, 1, a⁻¹] : Fin 3 → kˣ →* ℂˣ) i u = 1) ∧
          ∀ i i' : Fin 3, i ≠ i' → ![a, 1, a⁻¹] i ≠ ![a, 1, a⁻¹] i' ∧ ![a, 1, a⁻¹] i ≠ ![a, 1, a⁻¹] i' * absPow k 1) ∧
        ∀ ψ : Fin 2 → kˣ →* ℂˣ, ψ 0 / ψ 1 = a ^ 2 → ∀ i i', i ≠ i' → ψ i ≠ ψ i' ∧ ψ i ≠ ψ i' * absPow k 1 := by
  intro k _ _ _ _ a ⟨hu, hr⟩
  have two : absPow k 2 = absPow k 1 ^ 2 := by
    rw [pow_two, ← absPow_add]; norm_num
  have s1 : a ^ 2 ≠ 1 := by
    have := hr 0 (by norm_num)
    simpa using this
  have sp : a ^ 2 ≠ absPow k 1 := by
    have := hr 1 (by norm_num)
    simpa using this
  have sm : a ^ 2 ≠ (absPow k 1)⁻¹ := by
    have := hr (-1) (by norm_num)
    simpa [absPow_neg] using this
  have h1 : a ≠ 1 := fun h => s1 (by rw [h, one_pow])
  have hp : a ≠ absPow k 1 := fun h => hr 2 (by norm_num) (by
    rw [h]; push_cast; exact two.symm)
  have hm : a ≠ (absPow k 1)⁻¹ := fun h => hr (-2) (by norm_num) (by
    rw [h]; push_cast; rw [absPow_neg, two, inv_pow])
  refine ⟨⟨fun i u hu' => ?_, triple h1 hp hm s1 sp sm⟩, fun ψ hψ i i' hne => ?_⟩
  · fin_cases i
    · exact hu u hu'
    · rfl
    · show (a u)⁻¹ = 1
      rw [hu u hu', inv_one]
  · have e : ψ 1 / ψ 0 = (a ^ 2)⁻¹ := by rw [← hψ, inv_div]
    fin_cases i <;> fin_cases i'
    · exact absurd rfl hne
    · apply ne_of_div
      · exact hψ ▸ s1
      · exact hψ ▸ sp
    · apply ne_of_div
      · exact e ▸ inv_ne_one.2 s1
      · exact e ▸ inv_ne_of sm
    · exact absurd rfl hne
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.UnrSmooth
section
open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL Formalism.BasicNotions
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z.Sym.Al

private theorem exists_small (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    ∃ s : kˣ, valuation k (s : k) < 1 := by
  obtain ⟨x, hx0, hx⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation k)
  exact ⟨Units.mk0 x (fun h => hx0 (by simp [h])), hx⟩

private theorem split_small (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (x : kˣ) : ∃ s t : kˣ, valuation k (s : k) < 1 ∧ valuation k (t : k) < 1 ∧ x = s / t := by
  obtain ⟨p, hp⟩ := exists_small k
  by_cases hx : valuation k (x : k) < 1
  · refine ⟨x * p, p, ?_, hp, by simp⟩
    rw [Units.val_mul, map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' hx.le) hp
  · refine ⟨p, p * x⁻¹, hp, ?_, by simp⟩
    have h1 : 1 ≤ valuation k (x : k) := not_lt.1 hx
    rw [Units.val_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀]
    have h0 : valuation k (x : k) ≠ 0 := by simp
    have h2 : (valuation k (x : k))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h1
    exact lt_of_le_of_lt (mul_le_of_le_one_right' h2) hp

theorem UpperTheory.V.Z.Sym.Al.unrSmooth :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], (∀ χ : kˣ →* ℂˣ, (∀ u ∈ Hi.Uo k, χ u = 1) → IsSmoothChar χ) ∧
        ∀ (ψ : Fin 2 → kˣ →* ℂˣ) (b : kˣ →* ℂˣ), (∀ t : kˣ, valuation k (t : k) < 1 → expo ψ ![t, t⁻¹] = expo ![b, 1] ![t, t⁻¹]) → ψ 0 / ψ 1 = b := by
  intro k _ _ _ _
  refine ⟨fun χ h => isSmoothChar_of_isUnram fun x hx => h x hx, fun ψ b h => ?_⟩
  have key : ∀ t : kˣ, valuation k (t : k) < 1 → (ψ 0 / ψ 1) t = b t := by
    intro t ht
    have h1 := Units.val_injective (h t ht)
    have h2 := mul_right_cancel h1
    rw [torusChar_apply, torusChar_apply, Fin.prod_univ_two, Fin.prod_univ_two] at h2
    simpa [MonoidHom.div_apply, div_eq_mul_inv] using h2
  refine MonoidHom.ext fun x => ?_
  obtain ⟨s, t, hs, ht, rfl⟩ := split_small k x
  rw [map_div, map_div, key s hs, key t ht]
end

