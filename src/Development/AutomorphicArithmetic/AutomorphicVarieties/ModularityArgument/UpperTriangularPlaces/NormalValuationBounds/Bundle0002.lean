module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.UpperTriangularPlaces.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.SplAdjUnit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FrobeniusFields.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0362
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.Bundle0006

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.UpperTriangularPlaces.NormalValuationBounds.NeOfPair
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Z.Win

namespace UpperTheory.V.Keep

private theorem pairs (e : ℕ) (he : 2 ≤ e) (i j : Fin 4)
    (h : (![e + 1, e, 1, 0] : Fin 4 → ℕ) i = (![e + 1, e, 1, 0] : Fin 4 → ℕ) j + 1) :
    (i = 0 ∧ j = 1) ∨ (i = 2 ∧ j = 3) ∨ (i = 1 ∧ j = 2) := by
  fin_cases i <;> fin_cases j <;> simp at h ⊢ <;> omega

private theorem ne_of_pair {k : Type} [Field k] (x : k) (hx : x ≠ 1) (i j : Fin 4)
    (h : (i = 0 ∧ j = 1) ∨ (i = 2 ∧ j = 3) ∨ (i = 1 ∧ j = 2)) :
    (![x, 1, x, 1] : Fin 4 → k) i ≠ (![x, 1, x, 1] : Fin 4 → k) j := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [hx, Ne.symm hx]

private theorem exp_step {M : Type} [CommGroup M] (a b c : M) (m n : ℕ) (hc : ¬ IsOfFinOrder c)
    (h : a = b * c) (ha : a ^ 2 = c ^ (2 * (m : ℤ))) (hb : b ^ 2 = c ^ (2 * (n : ℤ))) : m = n + 1 := by
  have hinj := injective_zpow_iff_not_isOfFinOrder.2 hc
  have key : c ^ (2 * (m : ℤ)) = c ^ (2 * ((n : ℤ) + 1)) := by
    rw [← ha, h, mul_pow, hb, ← zpow_natCast c 2, ← zpow_add]
    congr 1
  have := hinj key
  omega

private theorem res_step {l : ℕ} [Fact l.Prime] (c : Coef l) (a b d : c.Oˣ) (x y : PadicAlgCl l)
    (hx : ‖x - ((a : c.O) : PadicAlgCl l)‖ < 1) (hy : ‖y - ((b : c.O) : PadicAlgCl l)‖ < 1)
    (e : x = y * ((d : c.O) : PadicAlgCl l)) :
    residue c.O (a : c.O) = residue c.O (b : c.O) * residue c.O (d : c.O) := by
  set z : c.O := (a : c.O) - (b : c.O) * (d : c.O) with hz
  have hnorm : ‖((z : c.O) : PadicAlgCl l)‖ < 1 := by
    have hd := GlobalTheory.CoefCoord.norm_unit c d
    have hsplit : ((z : c.O) : PadicAlgCl l) =
        -(x - ((a : c.O) : PadicAlgCl l)) + (y - ((b : c.O) : PadicAlgCl l)) * ((d : c.O) : PadicAlgCl l) := by
      rw [hz, e]
      push_cast
      ring
    rw [hsplit]
    refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ ?_)
    · rwa [norm_neg]
    · rw [norm_mul, hd, mul_one]
      exact hy
  have hmem : z ∈ maximalIdeal c.O := by
    rw [mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have := GlobalTheory.CoefCoord.norm_unit c hu.unit
    simp only [IsUnit.unit_spec] at this
    rw [this] at hnorm
    exact lt_irrefl _ hnorm
  have h0 : residue c.O z = 0 := (residue_eq_zero_iff _).2 hmem
  rw [hz, map_sub, map_mul, sub_eq_zero] at h0
  exact h0

section

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}

private theorem bar_chi (D : Raw Ω c) (hD : D.Good) (pr : Bool) (g : G ℚ Ω) (hp : Raw.bar D.Psi g = 1) (i : Fin 4) :
    Raw.bar (chi D pr i) g = (![Raw.bar D.ξ g, 1, Raw.bar D.ξ g, 1] : Fin 4 → ResidueField c.O) i := by
  obtain ⟨-, -, hal, hth, -⟩ := barFacts D hD
  have h1 : Raw.bar (1 : G ℚ Ω →* c.Oˣ) g = 1 := by
    simp [Raw.bar]
  have hth' : Raw.bar D.th g = Raw.bar D.ξ g := by
    rw [hth, hp, mul_one]
  cases pr <;> fin_cases i <;> simp [chi, lab, Raw.ps, hal g, hth', hp, h1]

end

theorem unlF : UnlF := by
  intro hinf Ω _ _ _ l _ c D T hD hT hLoc r A hA κ hord i j heq
  obtain ⟨-, -, -, -, -, hrbar, hrb, -⟩ := barFacts D hD
  have hstep : ∀ s : Dec (F := T.F) A, κ i s = κ j s * cycBar T.F Ω l s.1 := by
    intro s
    rw [heq]
    rfl
  have hres : ∀ s : Dec (F := T.F) A, Raw.bar (chi D T.pr i) (resQ T.F s.1) =
      Raw.bar (chi D T.pr j) (resQ T.F s.1) * Raw.bar (chiO ℚ Ω l c.O) (resQ T.F s.1) := by
    intro s
    have h2 := congrArg Units.val (hstep s)
    rw [Units.val_mul] at h2
    exact res_step c _ _ _ _ _ (hord.red i s) (hord.red j s) h2
  rcases hLoc A hA with ⟨g, hgI, hom⟩ | ⟨g, hgD, hom, hps, hal⟩
  · obtain ⟨hξ, hΨ⟩ := (hrbar _).1 (hT.ineL A hA g hgI)
    have e1 := hres ⟨g, Ine_le_Dec A hgI⟩
    have hall : ∀ k, (![Raw.bar D.ξ (resQ T.F g), 1, Raw.bar D.ξ (resQ T.F g), 1] : Fin 4 → ResidueField c.O) k = 1 := by
      intro k
      fin_cases k
      · exact hξ
      · rfl
      · exact hξ
      · rfl
    rw [bar_chi D hD T.pr _ hΨ, bar_chi D hD T.pr _ hΨ, hall, hall, one_mul, ← hD.om_bar] at e1
    exact hom e1.symm
  · have hΨ : Raw.bar D.Psi (resQ T.F g) = 1 := by
      rw [hrb] at hps
      cases h : T.pr <;> simp [wPs, h] at hps <;> exact hps
    have hξ : Raw.bar D.ξ (resQ T.F g) ≠ 1 := by
      rw [hrb] at hal
      simpa [wAl] using hal
    obtain ⟨U, hU, hw⟩ := hord.wts
    obtain ⟨s, hs, hc⟩ := hinf T.F Ω l A hA U hU
    let sD : Dec (F := T.F) A := ⟨s, Ine_le_Dec A (Subgroup.mem_inf.1 hs).2⟩
    have hnum : D.wts4 i = D.wts4 j + 1 :=
      exp_step _ _ _ _ _ hc (hstep sD) (hw i sD hs) (hw j sD hs)
    have hp := pairs D.e hD.two_le i j hnum
    have e1 := hres ⟨g, hgD⟩
    rw [bar_chi D hD T.pr _ hΨ, bar_chi D hD T.pr _ hΨ, ← hD.om_bar, hom, mul_one] at e1
    exact ne_of_pair _ hξ i j hp e1

end UpperTheory.V.Keep
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.UpperTriangularPlaces.NormalValuationBounds.ValLtOneIff
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Z.Win
open scoped Pointwise

namespace UpperTheory.V.Keep

section Place

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]

private theorem val_lt_one_iff (A : ValuationSubring Ω) (x : Ω) : A.valuation x < 1 ↔ x = 0 ∨ x⁻¹ ∉ A := by
  by_cases hx : x = 0
  · simp [hx]
  · have h0 : 0 < A.valuation x := zero_lt_iff.2 ((_root_.map_ne_zero _).2 hx)
    rw [← A.valuation_le_one_iff, map_inv₀, not_le, one_lt_inv₀ h0]
    simp [hx]

private theorem smul_place {A B : ValuationSubring Ω} {g : G F Ω} (hg : ∀ x, g x ∈ A ↔ x ∈ B) : g • B = A := by
  ext x
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ← hg]
  simp [AlgEquiv.smul_def]

private theorem conj_dec {A B : ValuationSubring Ω} {g : G F Ω} (hg : ∀ x, g x ∈ A ↔ x ∈ B) {s : G F Ω}
    (hs : s ∈ Dec (F := F) A) : g⁻¹ * s * g ∈ Dec (F := F) B := by
  have e := smul_place hg
  rw [mem_Dec] at hs ⊢
  rw [mul_smul, mul_smul, e, hs, ← e, inv_smul_smul]

private theorem conj_ine {A B : ValuationSubring Ω} {g : G F Ω} (hg : ∀ x, g x ∈ A ↔ x ∈ B) {s : G F Ω}
    (hs : s ∈ Ine (F := F) A) : g⁻¹ * s * g ∈ Ine (F := F) B := by
  refine ⟨conj_dec hg (Ine_le_Dec A hs), fun x hx => ?_⟩
  have h1 := hs.2 (g x) ((A.valuation_le_one_iff _).2 ((hg x).2 ((B.valuation_le_one_iff _).1 hx)))
  have e : (g⁻¹ * s * g) x - x = g⁻¹ (s (g x) - g x) := by
    rw [map_sub]
    simp [AlgEquiv.mul_apply]
  rw [e]
  rw [val_lt_one_iff] at h1 ⊢
  rcases h1 with h1 | h1
  · left; rw [h1, map_zero]
  · right
    intro h2
    apply h1
    rw [← map_inv₀, ← hg] at h2
    simpa using h2

end Place

section Mat

private theorem up_diag {K : Type} [CommRing K] {X Y : M4 K} (hX : IsUp X) (hY : IsUp Y) (i : Fin 4) :
    (X * Y) i i = X i i * Y i i := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · intro b _ hb
    rcases lt_or_gt_of_ne hb with h | h
    · rw [hX i b h, zero_mul]
    · rw [hY b i h, mul_zero]
  · simp

private theorem adj_map {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (X : M4 R) :
    adj (X.map f) = (adj X).map f := by
  ext i j
  simp [adj_apply, map_zsmul]

private theorem conj_map {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (n x : M4 R) :
    adj (n.map f) * x.map f * n.map f = (adj n * x * n).map f := by
  rw [adj_map, Matrix.map_mul, Matrix.map_mul]

private theorem flag_abs {Γ K ι : Type} [Group Γ] [Field K] (ρ : Γ →* GL (Fin 4) K) (P : PD ι Γ K) (v : ι) (g : Γ)
    (H : Subgroup Γ) (hρ : ∀ s, (ρ s : M4 K) = P.r s) (hn : adj (P.n v) * P.n v = 1)
    (hup : ∀ s : H, IsUp (adj (P.n v) * P.r (g⁻¹ * s * g) * P.n v)) :
    ∃ κ : Fin 4 → H →* Kˣ, Af.IsFlagOn ρ H κ ∧ ∀ i s, (κ i s : K) = P.ψ v i (g⁻¹ * s * g) := by
  have hn' : P.n v * adj (P.n v) = 1 := mul_eq_one_comm.1 hn
  have hgg : P.r g * P.r g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  have hgg' : P.r g⁻¹ * P.r g = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  let u : GL (Fin 4) K := ⟨adj (P.n v) * P.r g⁻¹, P.r g * P.n v,
    by rw [mul_assoc, ← mul_assoc (P.r g⁻¹), hgg', one_mul, hn],
    by rw [mul_assoc, ← mul_assoc (P.n v), hn', one_mul, hgg]⟩
  have hu : ∀ s : Γ, ((u * ρ s * u⁻¹ : GL (Fin 4) K) : M4 K) = adj (P.n v) * P.r (g⁻¹ * s * g) * P.n v := fun s => by
    show adj (P.n v) * P.r g⁻¹ * (ρ s : M4 K) * (P.r g * P.n v) = _
    rw [hρ, map_mul, map_mul]
    simp only [mul_assoc]
  let d : Fin 4 → H →* K := fun i =>
    { toFun := fun s => adj (P.n v) * P.r (g⁻¹ * s * g) * P.n v |>.diag i
      map_one' := by
        simp [Matrix.diag, hn]
      map_mul' := fun a b => by
        have e : adj (P.n v) * P.r (g⁻¹ * ((a * b : H) : Γ) * g) * P.n v =
            (adj (P.n v) * P.r (g⁻¹ * a * g) * P.n v) * (adj (P.n v) * P.r (g⁻¹ * b * g) * P.n v) := by
          rw [← hu, ← hu, ← hu, ← Units.val_mul]
          congr 1
          simp only [Subgroup.coe_mul, map_mul]
          group
        simp only [Matrix.diag_apply]
        rw [e, up_diag (hup a) (hup b)] }
  refine ⟨fun i => (d i).toHomUnits, ⟨u, fun s => ?_⟩, fun i s => rfl⟩
  have e := hu (s : Γ)
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · have := hup s i j hij
    rw [← e] at this
    simpa using this
  · have : ((u * ρ s * u⁻¹ : GL (Fin 4) K) : M4 K) i i = d i s := by rw [e]; rfl
    simpa using this

end Mat

private theorem mem_max_of_res {Λ R : Type} [CommRing Λ] [IsLocalRing Λ] [CommRing R] [Algebra Λ R] [IsCO Λ R] {x : R}
    (hx : res Λ R x = 0) : x ∈ maximalIdeal R := by
  by_contra h
  have h1 : IsUnit x := by simpa using h
  exact (h1.map (res Λ R)).ne_zero hx

private theorem psi_map {ι Γ R R' : Type} [Group Γ] [CommRing R] [CommRing R'] (f : R →+* R') (P : PD ι Γ R) (v : ι)
    (i : Fin 4) (s : Γ) : (P.map f).ψ v i s = f (P.ψ v i s) := by
  show (adj ((P.n v).map f) * (P.r s).map f * (P.n v).map f) i i = _
  rw [conj_map]
  rfl

private theorem comm_conj {Γ C : Type} [Group Γ] [CommGroup C] (f : Γ →* C) (g s : Γ) : f (g⁻¹ * s * g) = f s := by
  rw [map_mul, map_mul, map_inv, mul_comm (f g)⁻¹, mul_assoc, inv_mul_cancel, mul_one]

theorem flagF : FlagF := by
  intro Ω _ _ _ l _ c D T c' h X y hW r hr A hA
  obtain ⟨v₀, ⟨g, hg₀⟩, -⟩ := T.cover A hA
  suffices key : ∀ v : (T.fr ∅).ι, (∀ x, g x ∈ A ↔ x ∈ T.pl v) → ∃ κ, OrdAt T r A κ from key v₀ hg₀
  intro v hg
  have hconj : ∀ s : ↥(Dec (F := T.F) A), g⁻¹ * (s : G T.F Ω) * g ∈ Dec (F := T.F) (T.pl v) := fun s => conj_dec hg s.2
  have hn : adj ((X.P.map (y : X.A →+* PadicAlgCl l)).n v) * (X.P.map (y : X.A →+* PadicAlgCl l)).n v = 1 := by
    have h1 : adj (X.P.n v) * X.P.n v = 1 := by
      have := (X.pair.low v).1
      rw [IsGSp, one_smul] at this
      exact this
    show adj ((X.P.n v).map _) * (X.P.n v).map _ = 1
    rw [adj_map, ← Matrix.map_mul, h1]
    simp
  have hup : ∀ s : ↥(Dec (F := T.F) A), IsUp (adj ((X.P.map (y : X.A →+* PadicAlgCl l)).n v) *
      (X.P.map (y : X.A →+* PadicAlgCl l)).r (g⁻¹ * (s : G T.F Ω) * g) * (X.P.map (y : X.A →+* PadicAlgCl l)).n v) := fun s i j hij => by
    show (adj ((X.P.n v).map (y : X.A →+* PadicAlgCl l)) * (X.P.r (g⁻¹ * (s : G T.F Ω) * g)).map (y : X.A →+* PadicAlgCl l) *
      (X.P.n v).map (y : X.A →+* PadicAlgCl l) : M4 (PadicAlgCl l)) i j = 0
    rw [conj_map, Matrix.map_apply, X.pair.flag v _ (hconj s) i j hij, map_zero]
  obtain ⟨κ, hf, hκ⟩ := flag_abs (r.toHomUnits.comp (resQ T.F)) (X.P.map (y : X.A →+* PadicAlgCl l)) v g (Dec (F := T.F) A)
    (fun s => by rw [← hr]; rfl) hn hup
  refine ⟨κ, hf, fun i s => ?_, ?_⟩
  · have hm := X.ψ_map v i _ (hconj s)
    have hd := X.ψ_red v i _ (hconj s)
    let yB : X.B →ₐ[c'.O] PadicAlgCl l := y.comp (IsScalarTower.toAlgHom c'.O X.B X.A)
    let z : c.O := ((chi D T.pr i (resQ T.F (g⁻¹ * (s : G T.F Ω) * g)) : c.Oˣ) : c.O)
    have hb : X.ψ v i (g⁻¹ * (s : G T.F Ω) * g) - algebraMap c'.O X.B (inc h z) ∈ maximalIdeal X.B := by
      apply mem_max_of_res (Λ := c'.O)
      rw [map_sub, hd, AlgHom.commutes, sub_eq_zero]
      rfl
    obtain ⟨-, a, a1, -, ha⟩ := (coPt c' X.B).1 yB
    have hb' : X.ψ v i (g⁻¹ * (s : G T.F Ω) * g) - algebraMap c'.O X.B (inc h z) ∈ maximalIdeal X.B ^ 1 := by
      rw [pow_one]
      exact hb
    have h2 := ha 1 _ hb'
    have e : yB (X.ψ v i (g⁻¹ * (s : G T.F Ω) * g) - algebraMap c'.O X.B (inc h z)) =
        (κ i s : PadicAlgCl l) - (z : PadicAlgCl l) := by
      rw [map_sub, AlgHom.commutes, hκ, psi_map, ← hm]
      rfl
    rw [e, pow_one] at h2
    have e2 : z = ((chi D T.pr i (resQ T.F s) : c.Oˣ) : c.O) := by
      exact congrArg Units.val (comm_conj ((chi D T.pr i).comp (resQ T.F)) g (s : G T.F Ω))
    rw [← e2]
    exact lt_of_le_of_lt h2 a1
  · obtain ⟨U, hU, hw⟩ := hW
    refine ⟨U.comap (MulAut.conj g⁻¹).toMonoidHom, hU.preimage ?_, fun i s hs => ?_⟩
    · show Continuous fun s : G T.F Ω => g⁻¹ * s * g⁻¹⁻¹
      exact (continuous_const.mul continuous_id).mul continuous_const
    · have h1 : g⁻¹ * (s : G T.F Ω) * g ∈ U := by
        have := hs.1
        simpa [Subgroup.mem_comap] using this
      have h2 := hw v i _ ⟨h1, conj_ine hg hs.2⟩
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, hκ]
      refine Eq.trans h2 ?_
      show ((cycBar T.F Ω l (g⁻¹ * (s : G T.F Ω) * g) ^ (2 * (D.wts4 i : ℤ)) : (PadicAlgCl l)ˣ) : PadicAlgCl l) = _
      rw [comm_conj]

end UpperTheory.V.Keep

end
end

