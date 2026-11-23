module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.SymExOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.CastVal
section
open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym

section

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ}

private theorem eOm_red (ε : Ω →+* ℂ) {k m : ℕ} (hk : 0 < k) (hm : 0 < m) :
    eOm ε (1 / ((k * m : ℕ) : ℚ)) ^ k = eOm ε (1 / (m : ℚ)) := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  apply ε.injective
  rw [map_pow, eps_eOm, eps_eOm, ← Complex.exp_nat_mul]
  congr 1
  have h1 : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  have h2 : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  push_cast
  field_simp

private theorem zt_red (X : Tower Ω ε) {k m : ℕ} (hk : 0 < k) (hm : 0 < m) : zt X (k * m) ^ k = zt X m := by
  unfold zt
  rw [← map_pow, ← map_pow, eOm_red ε hk hm]

private theorem cast_val {k m : ℕ} (hk : 0 < k) (hm : 0 < m) (i : ZMod (k * m)) :
    (ZMod.castHom (dvd_mul_left m k) (ZMod m) i).val = i.val % m := by
  haveI : NeZero (k * m) := ⟨(Nat.mul_pos hk hm).ne'⟩
  rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.val_natCast]

private theorem lg_red (X : Tower Ω ε) {k m : ℕ} (hk : 0 < k) (hm : 0 < m) {a b : Kb X} (hb : b ≠ 0)
    (h : a ^ (k * m) = b ^ (k * m)) :
    lg X m (a ^ k) (b ^ k) = ZMod.castHom (dvd_mul_left m k) (ZMod m) (lg X (k * m) a b) := by
  obtain ⟨-, hrep1, -, -, -, -, -⟩ := lgB Ω ε X (k * m) (Nat.mul_pos hk hm)
  obtain ⟨hp2, -, huniq2, -, -, -, -⟩ := lgB Ω ε X m hm
  apply huniq2 _ _ _ (pow_ne_zero _ hb)
  rw [cast_val hk hm]
  have e : zt X m ^ (lg X (k * m) a b).val = zt X m ^ ((lg X (k * m) a b).val % m) := by
    conv_lhs => rw [← Nat.div_add_mod (lg X (k * m) a b).val m, pow_add, pow_mul, hp2.pow_eq_one,
      one_pow, one_mul]
  rw [← e, ← zt_red X hk hm, ← pow_mul, mul_comm k (lg X (k * m) a b).val, pow_mul, ← mul_pow,
    ← hrep1 a b hb h]

private theorem ka_red (X : Tower Ω ε) {k m : ℕ} (hk : 0 < k) (hm : 0 < m) {θ : Kb X} {u : X.K} (hu : u ≠ 0)
    (hθ : θ ^ (k * m) = io X u) {h : RingAut (Kb X)} (hh : InD X h) :
    ka X m (θ ^ k) h = ZMod.castHom (dvd_mul_left m k) (ZMod m) (ka X (k * m) θ h) := by
  have h0 : θ ≠ 0 := by
    rintro rfl
    rw [zero_pow (Nat.mul_pos hk hm).ne'] at hθ
    exact hu ((map_eq_zero _).1 hθ.symm)
  unfold ka
  rw [map_pow]
  exact lg_red X hk hm h0 (by rw [← map_pow, hθ, hh])

private theorem cyc_red (X : Tower Ω ε) {k m : ℕ} (hk : 0 < k) (hm : 0 < m) (s : Ω ≃ₐ[ℚ] Ω) :
    cyc m s = ZMod.castHom (dvd_mul_left m k) (ZMod m) (cyc (k * m) s) := by
  haveI : NeZero m := ⟨hm.ne'⟩
  obtain ⟨hp, -, -, -, -, -, hcyc⟩ := lgB Ω ε X m hm
  obtain ⟨-, -, -, -, -, -, hcyc2⟩ := lgB Ω ε X (k * m) (Nat.mul_pos hk hm)
  have hζ : IsPrimitiveRoot (eOm ε (1 / (m : ℚ))) m :=
    IsPrimitiveRoot.of_map_of_injective (f := (io X).comp (algebraMap Ω X.K)) hp
      (RingHom.injective _)
  have h1 : (eOm ε (1 / (m : ℚ))) ^ m = 1 := hζ.pow_eq_one
  have hA := (hcyc s s).2.2 _ h1
  have hB := (hcyc2 s s).2.2 _ (by rw [mul_comm, pow_mul, h1, one_pow])
  apply ZMod.val_injective
  apply hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _)
  rw [← hA, cast_val hk hm, hB]
  conv_lhs => rw [← Nat.div_add_mod (cyc (k * m) s).val m, pow_add, pow_mul, h1, one_pow, one_mul]

end

theorem UpperTheory.V.Z.Kato.Sym.redB :
    UpperTheory.V.Z.Kato.Sym.RedB := by
  intro Ω _ _ _ ε X k m hk hm
  have hkm := Nat.mul_pos hk hm
  refine ⟨fun u v P hP => ⟨hP.hu, hP.hv, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [← hP.ha, pow_mul]; rfl
  · rw [← hP.hb, pow_mul]; rfl
  · intro g h hg hh
    simp only [Pt.red]
    rw [ka_red X hk hm hP.hu.1 hP.ha hg, ka_red X hk hm hP.hv.1 hP.hb hh, ← map_mul, hP.cob g h hg hh, map_add (f := _), map_sub]
  · obtain ⟨B, hB⟩ := hP.lc
    refine ⟨B, fun h h' a b c => ?_⟩
    simp only [Pt.red]
    rw [hB h h' a b c]
  · intro B h a b c
    simp only [Pt.red]
    rw [hP.unr B h a b c, map_zero]
  · rintro τ s - u v P Q hP hQ f ⟨σ, hσ, θ, hθ, hd⟩
    refine ⟨σ, hσ, θ ^ k, by rw [← hθ, pow_mul], fun h hh => ?_⟩
    have nz : ∀ (a : Kb X) (w : X.K), w ≠ 0 → a ^ (k * m) = io X w → a ≠ 0 := by
      rintro a w hw ha rfl
      rw [zero_pow hkm.ne'] at ha
      exact hw ((map_eq_zero _).1 ha.symm)
    have ea : σ P.a ^ (k * m) = Q.a ^ (k * m) := by rw [← map_pow, hP.ha, hσ, hQ.ha]
    have eb : σ P.b ^ (k * m) = Q.b ^ (k * m) := by rw [← map_pow, hP.hb, hσ, hQ.hb]
    rw [ka_red X hk hm f.ne_zero hθ hh, hd h hh]
    simp only [dif, Pt.mv, Pt.red, map_add (f := _), map_sub, map_mul, map_pow]
    rw [ka_red X hk hm hQ.hu.1 hQ.ha hh, ka_red X hk hm hQ.hv.1 hQ.hb hh, lg_red X hk hm (nz _ _ hQ.hu.1 hQ.ha) ea,
      lg_red X hk hm (nz _ _ hQ.hv.1 hQ.hb) eb, cyc_red X hk hm s]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.KaB
section
open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym

theorem UpperTheory.V.Z.Kato.Sym.kaB :
    UpperTheory.V.Z.Kato.Sym.KaB := by
  intro Ω _ _ _ ε X m hm θ u hu hθ
  haveI : NeZero m := ⟨hm.ne'⟩
  obtain ⟨hprim, hrep, huniq, hcoc, hmul, hequiv, -⟩ := lgB Ω ε X m hm
  have hio : ∀ {x : X.K}, x ≠ 0 → io X x ≠ 0 := fun hx => (map_ne_zero (io X)).mpr hx
  have hne : ∀ {y : Kb X} {w : X.K}, w ≠ 0 → y ^ m = io X w → y ≠ 0 := by
    rintro y w hw hy rfl
    rw [zero_pow hm.ne'] at hy
    exact hio hw hy.symm
  have hθ0 : θ ≠ 0 := hne hu hθ
  have hpow : ∀ {y : Kb X} {w : X.K} (h : RingAut (Kb X)), InD X h → y ^ m = io X w →
      (h y) ^ m = y ^ m := by
    intro y w h hh hy
    rw [← map_pow, hy, hh w]
  have hzt : ∀ (g : RingAut (Kb X)), InD X g → g (zt X m) = zt X m := fun g hg => hg _
  have hkey : ∀ (h : RingAut (Kb X)), InD X h → h θ = zt X m ^ (ka X m θ h).val * θ :=
    fun h hh => hrep _ _ hθ0 (hpow h hh hθ)
  have hself : ∀ a : Kb X, a ≠ 0 → lg X m a a = 0 := fun a ha =>
    huniq a a 0 ha (by rw [ZMod.val_zero, pow_zero, one_mul])
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro g h hg hh
    have e1 : (g * h) θ = g (h θ) := rfl
    have hgθ : g θ ≠ 0 := (map_ne_zero g).mpr hθ0
    have hA : ((g * h) θ) ^ m = (g θ) ^ m := by
      rw [e1, ← map_pow, hpow h hh hθ, map_pow]
    have hB : (g θ) ^ m = θ ^ m := hpow g hg hθ
    have hC : ka X m θ (g * h) = lg X m ((g * h) θ) (g θ) + ka X m θ g := hcoc _ _ _ hθ0 hA hB
    have hD : lg X m ((g * h) θ) (g θ) = ka X m θ h := by
      apply huniq _ _ _ hgθ
      rw [e1, hkey h hh, map_mul, map_pow, hzt g hg]
    rw [hC, hD, add_comm]
  · intro θ' hθ' h hh
    obtain ⟨j, hj⟩ : ∃ j : ZMod m, θ' = zt X m ^ j.val * θ :=
      ⟨_, hrep _ _ hθ0 (by rw [hθ', hθ])⟩
    subst hj
    have hz0 : zt X m ^ j.val ≠ 0 := pow_ne_zero _ (hprim.ne_zero hm.ne')
    show lg X m (h (zt X m ^ j.val * θ)) (zt X m ^ j.val * θ) = lg X m (h θ) θ
    rw [map_mul, map_pow, hzt h hh, hmul _ _ _ _ hz0 hθ0 rfl (hpow h hh hθ), hself _ hz0, zero_add]
  · exact ⟨{θ}, fun h h' _ _ hb => by
      show lg X m (h θ) θ = lg X m (h' θ) θ
      rw [hb θ (by simp)]⟩
  · intro hU B h hOv hh hsmall
    by_contra hk
    have hone : ∀ y : Kb X, y ≠ 0 → y ∈ B → y⁻¹ ∈ B → B.valuation y = 1 := by
      intro y hy0 hy1 hy2
      have h1 := (B.valuation_le_one_iff y).mpr hy1
      have h2 := (B.valuation_le_one_iff _).mpr hy2
      rw [map_inv₀] at h2
      have hpos : 0 < B.valuation y := zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hy0)
      exact le_antisymm h1 ((inv_le_one₀ hpos).mp h2)
    have hWu : (B.comap (io X)).valuation u = 1 := hU.2 _ hOv
    have hu1 : u ∈ B.comap (io X) := ((B.comap (io X)).valuation_le_one_iff u).mp hWu.le
    have hu2 : u⁻¹ ∈ B.comap (io X) := by
      apply ((B.comap (io X)).valuation_le_one_iff _).mp
      rw [map_inv₀, hWu, inv_one]
    have hvu : B.valuation (io X u) = 1 := by
      apply hone _ (hio hu) (ValuationSubring.mem_comap.mp hu1)
      rw [← map_inv₀]
      exact ValuationSubring.mem_comap.mp hu2
    have hvθ : B.valuation θ = 1 := by
      have : B.valuation θ ^ m = 1 := by rw [← map_pow, hθ, hvu]
      exact (pow_eq_one_iff.mp this).resolve_right hm.ne'
    set k := ka X m θ h with hkdef
    have hkne : k.val ≠ 0 := fun h0 => hk ((ZMod.val_eq_zero k).mp h0)
    have hζ1 : zt X m ^ k.val ≠ 1 := hprim.pow_ne_one_of_pos_of_lt hkne (ZMod.val_lt k)
    set c : Ω := eOm ε (1 / (m : ℚ)) ^ k.val - 1 with hcdef
    have hc : zt X m ^ k.val - 1 = io X (algebraMap Ω X.K c) := by
      simp only [hcdef, zt, map_sub, map_pow, map_one]
    have hc0 : c ≠ 0 := by
      intro h0
      rw [h0, map_zero, map_zero] at hc
      exact hζ1 (sub_eq_zero.mp hc)
    have hv1 : B.valuation (zt X m ^ k.val - 1) = 1 := by
      apply hone _ (sub_ne_zero.mpr hζ1)
      · rw [hc]; exact ValuationSubring.mem_comap.mp (hOv.1 c)
      · rw [hc, ← map_inv₀, ← map_inv₀]; exact ValuationSubring.mem_comap.mp (hOv.1 c⁻¹)
    have hs := hsmall θ hvθ.le
    rw [hkey h hh, ← sub_one_mul, map_mul, hv1, hvθ, one_mul] at hs
    exact lt_irrefl _ hs
  · intro σ τ s hA hLf h hh
    have hD : InD X (σ⁻¹ * h * σ) := by
      intro f
      show σ.symm (h (σ (io X f))) = io X f
      rw [hLf f, hh, ← hLf f, RingEquiv.symm_apply_apply]
    refine ⟨hD, ?_⟩
    show lg X m (h (σ θ)) (σ θ) = cyc m s * lg X m ((σ⁻¹ * h * σ) θ) θ
    have hy : ((σ⁻¹ * h * σ) θ) ^ m = θ ^ m := hpow _ hD hθ
    have e : h (σ θ) = σ ((σ⁻¹ * h * σ) θ) := by
      show _ = σ (σ.symm (h (σ θ)))
      rw [RingEquiv.apply_symm_apply]
    rw [e]
    exact hequiv σ τ s hA hLf _ _ hθ0 hy
  · intro θ' u' hu' hθ' h hh
    have hθ'0 := hne hu' hθ'
    show lg X m (h (θ * θ')) (θ * θ') = lg X m (h θ) θ + lg X m (h θ') θ'
    rw [map_mul]
    exact hmul _ _ _ _ hθ0 hθ'0 (hpow h hh hθ) (hpow h hh hθ')
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.KumLagr
section
open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym

private theorem kum_lagr {K L : Type} [Field K] [Field L] [Algebra K L] [IsGalois K L]
    (c : (L ≃ₐ[K] L) → K) (h0 : ∀ g, c g ≠ 0) (hm : ∀ g h, c (g * h) = c g * c h)
    (B : Finset L) (hB : ∀ g h : L ≃ₐ[K] L, (∀ b ∈ B, g b = h b) → c g = c h) :
    ∃ θ : L, θ ≠ 0 ∧ ∀ g : L ≃ₐ[K] L, g θ = algebraMap K L (c g) * θ := by
  classical
  let F : IntermediateField K L := (FiniteGaloisIntermediateField.adjoin K (B : Set L)).toIntermediateField
  haveI : FiniteDimensional K F := (FiniteGaloisIntermediateField.adjoin K (B : Set L)).finiteDimensional
  haveI : IsGalois K F := (FiniteGaloisIntermediateField.adjoin K (B : Set L)).isGalois
  have hBF : ∀ b ∈ B, b ∈ F := fun b hb =>
    FiniteGaloisIntermediateField.subset_adjoin K (B : Set L) hb
  have hagree : ∀ (g : L ≃ₐ[K] L) (σ : F ≃ₐ[K] F), (∀ x : F, g (x : L) = (σ x : L)) →
      c g = c (σ.liftNormal L) := by
    intro g σ hgσ
    apply hB
    intro b hb
    have h1 := hgσ ⟨b, hBF b hb⟩
    have h2 := σ.liftNormal_commutes L ⟨b, hBF b hb⟩
    simp only [IntermediateField.algebraMap_apply] at h2
    rw [h1, h2]
  let cE : (F ≃ₐ[K] F) → K := fun σ => c (σ.liftNormal L)
  have hlift : ∀ (σ : F ≃ₐ[K] F) (x : F), σ.liftNormal L (x : L) = (σ x : L) := by
    intro σ x
    have := σ.liftNormal_commutes L x
    simpa only [IntermediateField.algebraMap_apply] using this
  have hcEmul : ∀ σ τ, cE (σ * τ) = cE σ * cE τ := by
    intro σ τ
    have : c ((σ * τ).liftNormal L) = c (σ.liftNormal L * τ.liftNormal L) := by
      symm
      apply hagree
      intro x
      simp only [AlgEquiv.mul_apply, hlift]
    simp only [cE, this, hm]
  have hcE0 : ∀ σ, algebraMap K F (cE σ) ≠ 0 := fun σ => by
    simpa using h0 (σ.liftNormal L)
  let f : (F ≃ₐ[K] F) → Fˣ := fun σ => Units.mk0 _ (hcE0 σ)
  have hcoc : groupCohomology.IsMulCocycle₁ f := by
    intro σ τ
    ext
    simp [f, hcEmul, mul_comm]
  obtain ⟨β, hβ⟩ := groupCohomology.isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units f hcoc
  refine ⟨((β : F) : L), by simp, fun g => ?_⟩
  set σ := g.restrictNormal F
  have hgσ : ∀ x : F, g (x : L) = (σ x : L) := by
    intro x
    have := g.restrictNormal_commutes F x
    simpa only [IntermediateField.algebraMap_apply] using this.symm
  have hσβ : (σ (β : F)) = algebraMap K F (cE σ) * (β : F) := by
    have := congrArg (fun u : Fˣ => (u : F)) (hβ σ)
    simp [f, div_eq_iff (β.ne_zero)] at this
    simpa using this
  rw [hgσ, hσβ, hagree g σ hgσ]
  simp [cE]

theorem UpperTheory.V.Z.Kato.Sym.kum :
    UpperTheory.V.Z.Kato.Sym.Kum := by
  intro Ω _ _ _ ε X m hm
  classical
  haveI : NeZero m := ⟨hm.ne'⟩
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  haveI : CharZero X.K := charZero_of_injective_algebraMap (algebraMap Ω X.K).injective
  haveI : IsGalois X.K (Kb X) := IsGalois.mk
  obtain ⟨hprim, hL2, hL3, -, -, -, -⟩ := lgB Ω ε X m hm
  set ζK : X.K := algebraMap Ω X.K (eOm ε (1 / (m : ℚ))) with hζK
  have hzt : zt X m = io X ζK := rfl
  have hinj : Function.Injective (io X) := (io X).injective
  have hζm : ζK ^ m = 1 := by
    apply hinj
    rw [map_pow, ← hzt, hprim.pow_eq_one, map_one]
  have hζ0 : ζK ≠ 0 := by
    intro h
    rw [h, zero_pow hm.ne'] at hζm
    exact zero_ne_one hζm
  have hpowmod : ∀ n, ζK ^ (n % m) = ζK ^ n := fun n => by
    conv_rhs => rw [← Nat.mod_add_div n m, pow_add, pow_mul, hζm, one_pow, mul_one]
  have hInDalg : ∀ g : Kb X ≃ₐ[X.K] Kb X, InD X g.toRingEquiv := fun g x => g.commutes x
  let toAlg : ∀ h : RingAut (Kb X), InD X h → (Kb X ≃ₐ[X.K] Kb X) :=
    fun h hh => AlgEquiv.ofRingEquiv (f := h) hh
  have htoAlg : ∀ h hh, (toAlg h hh).toRingEquiv = h := fun h hh => rfl
  have hfixed : ∀ x : Kb X, (∀ h : RingAut (Kb X), InD X h → h x = x) → ∃ a : X.K, io X a = x := by
    intro x hx
    have hbot : x ∈ (⊥ : IntermediateField X.K (Kb X)) :=
      (InfiniteGalois.mem_bot_iff_fixed x).mpr fun g => hx g.toRingEquiv (hInDalg g)
    obtain ⟨a, ha⟩ := IntermediateField.mem_bot.mp hbot
    exact ⟨a, ha⟩
  have hne : ∀ (θ : Kb X) (f : X.Kˣ), θ ^ m = io X (f : X.K) → θ ≠ 0 := by
    intro θ f hθ h0
    rw [h0, zero_pow hm.ne'] at hθ
    exact f.ne_zero (hinj (by rw [← hθ, map_zero]))
  have hact : ∀ (θ : Kb X) (f : X.Kˣ), θ ^ m = io X (f : X.K) → ∀ h : RingAut (Kb X), InD X h →
      h θ = zt X m ^ (ka X m θ h).val * θ := by
    intro θ f hθ h hh
    apply hL2 _ _ (hne θ f hθ)
    rw [← map_pow, hθ, hh]
  refine ⟨fun φ hadd hLC => ?_, fun φ φ' f f' hK hφ => ?_⟩
  · obtain ⟨B, hB⟩ := hLC
    let c : (Kb X ≃ₐ[X.K] Kb X) → X.K := fun g => ζK ^ (φ g.toRingEquiv).val
    have hc0 : ∀ g, c g ≠ 0 := fun g => pow_ne_zero _ hζ0
    have hcm : ∀ g h, c (g * h) = c g * c h := by
      intro g h
      have e : (g * h).toRingEquiv = g.toRingEquiv * h.toRingEquiv := RingEquiv.ext fun _ => rfl
      simp only [c, e, hadd _ _ (hInDalg g) (hInDalg h), ZMod.val_add, hpowmod, pow_add]
    have hcB : ∀ g h : Kb X ≃ₐ[X.K] Kb X, (∀ b ∈ B, g b = h b) → c g = c h := by
      intro g h hgh
      simp only [c, hB _ _ (hInDalg g) (hInDalg h) hgh]
    obtain ⟨θ, hθ0, hθ⟩ := kum_lagr c hc0 hcm B hcB
    obtain ⟨a, ha⟩ := hfixed (θ ^ m) (by
      intro h hh
      rw [map_pow, show h θ = (toAlg h hh) θ from rfl, hθ, mul_pow, ← map_pow, ← pow_mul,
        mul_comm _ m, pow_mul, hζm, one_pow, map_one, one_mul])
    have ha0 : a ≠ 0 := by
      intro h0
      rw [h0, map_zero] at ha
      exact pow_ne_zero m hθ0 ha.symm
    refine ⟨Units.mk0 a ha0, θ, by simp [ha], fun h hh => ?_⟩
    apply hL3 _ _ _ hθ0
    rw [show h θ = (toAlg h hh) θ from rfl, hθ]
    show io X (ζK ^ (φ (toAlg h hh).toRingEquiv).val) * θ = zt X m ^ (φ h).val * θ
    rw [htoAlg, hzt, map_pow]
  · obtain ⟨θ, hθm, hθ⟩ := hK
    have hθ0 := hne θ f hθm
    have hθact : ∀ h, InD X h → h θ = zt X m ^ (φ h).val * θ := fun h hh => by
      rw [hact θ f hθm h hh, hθ h hh]
    constructor
    · rintro ⟨θ', hθ'm, hθ'⟩
      have hθ'0 := hne θ' f' hθ'm
      obtain ⟨u, hu⟩ := hfixed (θ' / θ) (by
        intro h hh
        rw [map_div₀, hθact h hh, hact θ' f' hθ'm h hh, hθ' h hh, ← hφ h hh]
        field_simp [hθ0, hθ'0, pow_ne_zero _ (hprim.ne_zero hm.ne')])
      have hu0 : u ≠ 0 := by
        intro h0
        rw [h0, map_zero, eq_comm, div_eq_zero_iff] at hu
        exact hu.elim hθ'0 hθ0
      refine ⟨Units.mk0 u hu0, Units.ext (hinj ?_)⟩
      simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_mk0, map_mul, map_pow, hu,
        ← hθ'm, ← hθm]
      rw [div_pow, mul_div_cancel₀ _ (pow_ne_zero m hθ0)]
    · rintro ⟨v, hv⟩
      refine ⟨θ * io X (v : X.K), ?_, fun h hh => ?_⟩
      · rw [mul_pow, hθm, ← map_pow, ← map_mul, hv, Units.val_mul, Units.val_pow_eq_pow_val]
      · apply hL3 _ _ _ (mul_ne_zero hθ0 ((map_ne_zero _).mpr v.ne_zero))
        rw [map_mul, hh, hθact h hh, hφ h hh, mul_assoc]
end

