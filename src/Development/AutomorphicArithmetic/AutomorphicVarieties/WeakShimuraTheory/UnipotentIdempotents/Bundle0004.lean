module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.UnipotentIdempotents.TCont
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.UnipotentIdempotents.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.CoefRes
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PhiCharacterResidues.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.UnipotentIdempotents.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle0007

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.UnipotentIdempotents.CbFacts
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Ws.Lk

private theorem chi_rev {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
    (D : Raw Ω c) (pr : Bool) (i : Fin 4) : chi D pr i * chi D pr i.rev = D.th := by
  cases pr <;> fin_cases i
  · exact mul_one _
  · exact mul_comm _ _
  · rfl
  · exact one_mul _
  · rfl
  · exact one_mul _
  · exact mul_one _
  · exact mul_comm _ _

theorem UpperTheory.V.Ws.Lk.cbFacts :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c} {T : Tower D} {c' : Coef l} {h : c.O ≤ c'.O} (X : OCh T c' h), D.Good → (∀ i, IsOpen ((X.cb i).ker : Set (G T.L Ω))) ∧ (∀ i A, Raw.Away D.S A → Ine (F := T.L) A ≤ (X.cb i).ker) ∧ ∀ σ ∉ T.K.fixingSubgroup, ∀ g g' : G T.L Ω, resQ T.L g' = σ * resQ T.L g * σ⁻¹ → ∀ i : Fin 4, (X.cb i g' * X.cb i.rev g : ResidueField c'.O) * residue c'.O (chiO T.L Ω l c'.O g) ^ 3 = 1 := by
  intro Ω _ _ _ l _ c D T c' h X hD
  obtain ⟨hop, -, hun⟩ := Lk.barFacts hD
  refine ⟨fun i => ?_, fun i A hA g hg => ?_, fun σ hσ g g' hgg i => ?_⟩
  · have hq : Continuous (resQ T.L) := UpperTheory.V.Af.continuous_restrictScalarsHom ℚ T.L Ω
    haveI := (P1.coefRes c).2.2.1 c' h
    have h1 : IsOpen {g : G T.L Ω | Ideal.Quotient.mk (maximalIdeal c'.O ^ 1) (X.κ g : c'.O) = 1} :=
      (X.κ_cont 1).isOpen_fiber 1
    have h2 := (hop (lab T.pr i)).preimage hq
    refine Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset ((h1.inter h2).mem_nhds ⟨?_, ?_⟩) ?_)
    · show Ideal.Quotient.mk _ (X.κ 1 : c'.O) = 1
      rw [map_one, Units.val_one, map_one]
    · show residue c.O (D.ps (lab T.pr i) (resQ T.L 1) : c.O) = 1
      rw [map_one, map_one, Units.val_one, map_one]
    · rintro g ⟨a, b⟩
      have a1 : (X.κ g : c'.O) - 1 ∈ maximalIdeal c'.O ^ 1 := Ideal.Quotient.eq.1 (a.trans (map_one _).symm)
      rw [pow_one] at a1
      have a2 : residue c'.O (X.κ g : c'.O) = residue c'.O 1 := Ideal.Quotient.eq.2 a1
      have b1 : residue c.O (chi D T.pr i (resQ T.L g) : c.O) = 1 := b
      have b2 : residue c'.O (inc h (chi D T.pr i (resQ T.L g) : c.O)) = 1 := by
        rw [← ResidueField.map_residue, b1, map_one]
      refine Units.ext ?_
      rw [OCh.cb_val, map_mul, a2, b2, map_one, one_mul, Units.val_one]
  · have a : X.κ g = 1 := X.unr A hA hg
    have b : chi D T.pr i (resQ T.L g) = 1 := (hun A hA (resQ T.L g) ⟨hg.1, hg.2⟩).1 _
    refine Units.ext ?_
    rw [OCh.cb_val, a, b, Units.val_one, Units.val_one, map_one, one_mul, map_one, Units.val_one]
  · have a := (X.conj σ hσ g g' hgg).1
    have b : chi D T.pr i (resQ T.L g') = chi D T.pr i (resQ T.L g) := by
      rw [hgg, map_mul, map_mul, map_inv, mul_right_comm, mul_inv_cancel, one_mul]
    have e : D.th (resQ T.L g) = chi D T.pr i (resQ T.L g) * chi D T.pr i.rev (resQ T.L g) :=
      (DFunLike.congr_fun (chi_rev D T.pr i) _).symm
    rw [e, Units.val_mul, map_mul] at a
    rw [OCh.cb_val, OCh.cb_val, b, ← map_pow, ← map_mul, ← map_mul, ← map_one (residue c'.O), ← a]
    congr 1
    ring
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.UnipotentIdempotents.Descend
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Ws.Lk

theorem UpperTheory.V.Ws.Lk.descend :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : W.HidaSetting l L Ω) (V : s.Lev) (M : Type) [Group M] (χ : G L Ω →* M), IsOpen (χ.ker : Set (G L Ω)) → (∀ (A : ValuationSubring Ω) (v : W.Plc (W.Lp L)), IsPlaceOver A v → v ∉ V.S' → Ine (F := L) A ≤ χ.ker) → ∃ χ' : V.frame.G₀ →* M, IsOpen (χ'.ker : Set V.frame.G₀) ∧ ∀ g, χ' (V.pr g) = χ g := by
  intro l _ L Ω _ _ _ _ _ _ s V M _ χ hopen hine
  obtain ⟨hsurj, hquot, hker⟩ := phiKer V
  have hle : V.pr.ker ≤ χ.ker := hker χ.ker (Subgroup.isClosed_of_isOpen _ hopen) hine
  let χ₀ : ↥V.η.ker →* M :=
    (QuotientGroup.lift V.pr.ker χ hle).comp
      (QuotientGroup.quotientKerEquivOfSurjective V.pr hsurj).symm.toMonoidHom
  have hcomp : ∀ g, χ₀ (V.pr g) = χ g := by
    intro g
    have h1 : (QuotientGroup.quotientKerEquivOfSurjective V.pr hsurj).symm (V.pr g) =
        (QuotientGroup.mk g : G L Ω ⧸ V.pr.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    simp only [χ₀, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, h1, QuotientGroup.lift_mk]
  have hpre : (V.pr : G L Ω → ↥V.η.ker) ⁻¹' (χ₀.ker : Set ↥V.η.ker) = (χ.ker : Set (G L Ω)) := by
    ext g
    simp [MonoidHom.mem_ker, hcomp]
  have hop : IsOpen (χ₀.ker : Set ↥V.η.ker) := hquot.isOpen_preimage.mp (hpre ▸ hopen)
  exact ⟨χ₀, hop, hcomp⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.UnipotentIdempotents.GExRtZero
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Ws.Lk

private theorem gEx_rt_wt {O Γ : Type} [CommRing O] [Group Γ] (Φ : Fr O Γ) (g : Γ)
    (h : Φ.χ 0 g * Φ.χ 3 g = Φ.χ 1 g * Φ.χ 2 g) (i j : Fin 4) : Φ.rt (wt i j) g * Φ.χ j g = Φ.χ i g := by
  have hd : Φ.χ 3 g = (Φ.χ 0 g)⁻¹ * (Φ.χ 1 g * Φ.χ 2 g) := eq_inv_mul_of_mul_eq h
  fin_cases i <;> fin_cases j <;> simp [Fr.rt, wt, lamW, muW, hd] <;>
    apply Additive.ofMul.injective <;> simp <;> abel

private theorem gEx_rt_add {O Γ : Type} [CommRing O] [Group Γ] (Φ : Fr O Γ) (g : Γ) (w w' : ℤ × ℤ) :
    Φ.rt (w + w') g = Φ.rt w g * Φ.rt w' g := by
  simp only [Fr.rt, MonoidHom.coe_mk, OneHom.coe_mk, Prod.fst_add, Prod.snd_add, zpow_add]
  exact mul_mul_mul_comm _ _ _ _

private theorem gEx_rt_zero {O Γ : Type} [CommRing O] [Group Γ] (Φ : Fr O Γ) (g : Γ) : Φ.rt 0 g = 1 := by
  simp [Fr.rt]

private theorem gEx_abs {O Γ Δ k : Type} [CommRing O] [Group Γ] [Group Δ] [Field k] [Finite k] (Φ : Fr O Γ)
    (h : ∀ g, Φ.χ 0 g * Φ.χ 3 g = Φ.χ 1 g * Φ.χ 2 g) (a : O →+* k) (φ : Δ →* Γ) (ω : Γ →* Oˣ)
    (hω : ∀ w, ∃ g, a (Φ.rt w (φ g)) ≠ a (ω (φ g))) :
    ∃ g, (∀ i j, a (Φ.χ i (φ g)) = a (Φ.χ j (φ g))) ∧ a (ω (φ g)) ≠ 1 := by
  classical
  let κ : Fin 4 → Δ →* kˣ := fun i => (Units.map a.toMonoidHom).comp ((Φ.χ i).comp φ)
  let ω' : Δ →* kˣ := (Units.map a.toMonoidHom).comp (ω.comp φ)
  have hmain : ω' ∉ Subgroup.closure (Set.range fun q : Fin 4 × Fin 4 => κ q.1 / κ q.2) := by
    intro hmem
    let S : Subgroup (Δ →* kˣ) :=
      { carrier := {ψ | ∃ w : ℤ × ℤ, ∀ g, ψ g = Units.map a.toMonoidHom (Φ.rt w (φ g))}
        mul_mem' := by
          rintro ψ₁ ψ₂ ⟨w₁, h₁⟩ ⟨w₂, h₂⟩
          exact ⟨w₁ + w₂, fun g => by simp [h₁, h₂, gEx_rt_add]⟩
        one_mem' := ⟨0, fun g => by simp [gEx_rt_zero]⟩
        inv_mem' := by
          rintro ψ ⟨w, hw⟩
          refine ⟨-w, fun g => ?_⟩
          have hinv : Φ.rt (-w) (φ g) = (Φ.rt w (φ g))⁻¹ := by
            rw [eq_inv_iff_mul_eq_one, ← gEx_rt_add]
            simp [gEx_rt_zero]
          simp [hw, hinv] }
    have hle : Subgroup.closure (Set.range fun q : Fin 4 × Fin 4 => κ q.1 / κ q.2) ≤ S := by
      rw [Subgroup.closure_le]
      rintro _ ⟨⟨p, q⟩, rfl⟩
      refine ⟨wt p q, fun g => ?_⟩
      have hpq := gEx_rt_wt Φ (φ g) (h _) p q
      simp only [κ, MonoidHom.div_apply, MonoidHom.comp_apply, ← hpq, map_mul]
      exact mul_div_cancel_right _ _
    obtain ⟨w, hw⟩ := hle hmem
    obtain ⟨g, hg⟩ := hω w
    apply hg
    have := congrArg Units.val (hw g)
    simpa [ω'] using this.symm
  obtain ⟨g, hg1, hg2⟩ := (Loc.v0e κ ω').2 hmain
  refine ⟨g, fun i j => ?_, ?_⟩
  · have := congrArg Units.val (hg1 i j)
    simpa [κ] using this
  · intro h1
    apply hg2
    ext
    simpa [ω'] using h1

theorem UpperTheory.V.Ws.Lk.gEx :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c} (T : Tower D), T.Ok → ∃ g : G T.L Ω, (∀ i j, Raw.bar (chi D T.pr i) (resQ T.L g) = Raw.bar (chi D T.pr j) (resQ T.L g)) ∧ Raw.bar D.om (resQ T.L g) ≠ 1 := by
  intro Ω _ _ _ l _ c D T hT
  haveI := c.dvr
  haveI := c.fin
  haveI : Finite (ResidueField c.O) :=
    IsLocalRing.ResidueField.finite_of_finite (R := ℤ_[l]) inferInstance
  have hrel : ∀ x, (T.fr ∅).χ 0 x * (T.fr ∅).χ 3 x = (T.fr ∅).χ 1 x * (T.fr ∅).χ 2 x := by
    intro x
    simp only [Tower.fr, MonoidHom.coe_comp, Function.comp_apply, chi]
    cases T.pr <;> simp [lab, Raw.ps, Raw.th, mul_comm]
  have hω : ∀ w, ∃ g, residue c.O ((T.fr ∅).rt w (resLe T.F_le g) : c.O) ≠
      residue c.O ((D.om.comp (resQ T.F)) (resLe T.F_le g) : c.O) := by
    intro w
    obtain ⟨g, hgL, hg⟩ := hT.g2 w
    obtain ⟨g', rfl⟩ := ((galEq T).2.2 g).1 hgL
    exact ⟨g', hg⟩
  obtain ⟨g, hg1, hg2⟩ :=
    gEx_abs (T.fr ∅) hrel (residue c.O) (resLe T.F_le) (D.om.comp (resQ T.F)) hω
  exact ⟨g, fun i j => hg1 i j, hg2⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.UnipotentIdempotents.PlacesEq
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Ws.Lk

private theorem nat_place {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {A : ValuationSubring Ω}
    {v : W.Plc F} (h : IsPlaceOver A v) (n : ℕ) : A.valuation (n : Ω) < 1 ↔ (n : 𝓞 F) ∈ v.asIdeal := by
  have key := h (n : 𝓞 F)
  simpa using key

open scoped Pointwise in
theorem UpperTheory.V.Ws.Lk.placesEq :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c} (T : Tower D), ∃ e : W.Vl l T.L ≃ T.ι, ∀ v : W.Vl l T.L, IsPlaceOver (T.pl (e v)) v.1 := by
  intro Ω _ _ _ l _ c D T
  obtain ⟨hF, ⟨φ, hφ, -⟩, -⟩ := galEq T
  have hfix : ∀ (g : G T.F Ω) (y : W.Lp T.L), g (algebraMap (W.Lp T.L) Ω y) = algebraMap (W.Lp T.L) Ω y := by
    intro g y
    have hy := (hF (algebraMap (W.Lp T.L) Ω y)).2 ⟨y, rfl⟩
    exact g.commutes ⟨_, hy⟩
  have hmove : ∀ (g : G T.F Ω) {A B : ValuationSubring Ω}, (∀ x, g x ∈ B ↔ x ∈ A) →
      ∀ {v : W.Plc (W.Lp T.L)}, IsPlaceOver A v → IsPlaceOver B v := by
    intro g A B hg v h x
    have key := val_lt_one (σ := g.toRingEquiv) hg (algebraMap (W.Lp T.L) Ω x)
    have hx : g.toRingEquiv (algebraMap (W.Lp T.L) Ω x) = algebraMap (W.Lp T.L) Ω x := hfix g x
    rw [hx] at key
    rw [key]
    exact h x
  have hA : ∀ v : W.Vl l T.L, ∃ A : ValuationSubring Ω, IsPlaceOver A v.1 := fun v => exists_isPlaceOver Ω v.1
  choose A hAv using hA
  have hAl : ∀ v, (A v).valuation (l : Ω) < 1 := fun v => (nat_place (hAv v) l).2 v.2
  choose e he using fun v => (T.cover (A v) (hAl v)).exists
  have hover : ∀ v, IsPlaceOver (T.pl (e v)) v.1 := by
    intro v
    obtain ⟨g, hg⟩ := he v
    refine hmove g⁻¹ ?_ (hAv v)
    intro x
    rw [← hg]
    simp
  refine ⟨Equiv.ofBijective e ⟨?_, ?_⟩, hover⟩
  · intro v v' hvv
    apply Subtype.ext
    have h1 := hover v
    have h2 := hover v'
    rw [hvv] at h1
    exact eq_of_isPlaceOver h1 h2
  · intro w
    have hne : T.pl w ≠ ⊤ := by
      intro htop
      exact ((places (W.Lp T.L) Ω l (T.pl w)).2.1 htop).2 (T.ovl w)
    obtain ⟨v0, hv0⟩ := (places (W.Lp T.L) Ω l (T.pl w)).1 hne
    have hv0l : (l : 𝓞 (W.Lp T.L)) ∈ v0.asIdeal := (nat_place hv0 l).1 (T.ovl w)
    refine ⟨⟨v0, hv0l⟩, ?_⟩
    obtain ⟨σ, hσ⟩ := exists_smul_eq_of_isPlaceOver hv0 (hAv ⟨v0, hv0l⟩)
    apply (T.cover (A ⟨v0, hv0l⟩) (hAl _)).unique (he _)
    refine ⟨φ σ, fun x => ?_⟩
    rw [hφ, ← hσ, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ← AlgEquiv.smul_def, inv_smul_smul]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.UnipotentIdempotents.WtRoot
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Ws.Lk

private theorem wt_root : ∀ i j : Fin 4, i ≠ j → wt i j ∈ roots := by
  decide

private theorem rt_wt' {O Γ : Type} [CommRing O] [Group Γ] (Φ : Fr O Γ) (g : Γ)
    (h : Φ.χ 0 g * Φ.χ 3 g = Φ.χ 1 g * Φ.χ 2 g) (i j : Fin 4) : Φ.rt (wt i j) g * Φ.χ j g = Φ.χ i g := by
  have hd : Φ.χ 3 g = (Φ.χ 0 g)⁻¹ * (Φ.χ 1 g * Φ.χ 2 g) := eq_inv_mul_of_mul_eq h
  fin_cases i <;> fin_cases j <;> simp [Fr.rt, wt, lamW, muW, hd] <;>
    apply Additive.ofMul.injective <;> simp <;> abel

theorem UpperTheory.V.Ws.Lk.cbInj :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c} {T : Tower D} {c' : Coef l} {h : c.O ≤ c'.O} (X : OCh T c' h), T.Ok → Function.Injective X.cb := by
  intro Ω _ _ _ l _ c D T c' h X hT i j hij
  by_contra hne
  obtain ⟨g, hgL, hg⟩ := hT.g3 _ (wt_root i j hne)
  obtain ⟨g', rfl⟩ := ((galEq T).2.2 g).1 hgL
  have hrel : (T.fr ∅).χ 0 (resLe T.F_le g') * (T.fr ∅).χ 3 (resLe T.F_le g') =
      (T.fr ∅).χ 1 (resLe T.F_le g') * (T.fr ∅).χ 2 (resLe T.F_le g') := by
    simp only [Tower.fr, MonoidHom.coe_comp, Function.comp_apply, chi]
    cases T.pr <;> simp [lab, Raw.ps, Raw.th, mul_comm]
  have key := rt_wt' (T.fr ∅) (resLe T.F_le g') hrel i j
  have hcb := congrArg (fun φ => ((φ g' : (ResidueField c'.O)ˣ) : ResidueField c'.O)) hij
  simp only [OCh.cb_val] at hcb
  simp only [Tower.rb] at hg
  set r := (T.fr ∅).rt (wt i j) (resLe T.F_le g') with hr_def
  have key' : ((r : c.O) * (chi D T.pr j (resQ T.L g') : c.O)) = (chi D T.pr i (resQ T.L g') : c.O) := by
    rw [← Units.val_mul]
    exact congrArg Units.val key
  rw [← key'] at hcb
  simp only [map_mul] at hcb
  have hu1 : residue c'.O (X.κ g' : c'.O) ≠ 0 := ((X.κ g').isUnit.map (residue c'.O)).ne_zero
  have hu2 : residue c'.O (inc h (chi D T.pr j (resQ T.L g') : c.O)) ≠ 0 :=
    (((chi D T.pr j (resQ T.L g')).isUnit.map (inc h)).map (residue c'.O)).ne_zero
  have hr : residue c'.O (inc h (r : c.O)) = 1 := by
    have h1 := mul_left_cancel₀ hu1 hcb
    exact mul_right_cancel₀ hu2 (h1.trans (one_mul _).symm)
  apply hg
  by_contra hne1
  have hmem : (r : c.O) - 1 ∉ maximalIdeal c.O := by
    intro hm
    apply hne1
    rw [← sub_eq_zero, ← map_one (residue c.O), ← map_sub]
    exact (residue_eq_zero_iff _).2 hm
  have hunit : IsUnit ((r : c.O) - 1) := by
    by_contra hn
    exact hmem ((mem_maximalIdeal _).2 hn)
  have hu := (hunit.map (inc h)).map (residue c'.O)
  rw [map_sub, map_sub, map_one, map_one, hr, sub_self] at hu
  exact not_isUnit_zero hu
end

