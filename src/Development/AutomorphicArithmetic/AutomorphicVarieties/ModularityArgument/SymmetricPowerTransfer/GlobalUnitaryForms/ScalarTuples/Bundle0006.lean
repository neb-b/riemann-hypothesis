module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.HodgeTateFromSandwich
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvenCardOfNotLone
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Bundle0008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.Bundle0007
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.HeckeCharacterChoice.TendstoUnderCofinite

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.HsCast
section
open NumberField UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Glob

private theorem hs_cast {F A : Type} [Field F] [NumberField F] [Field A] (φ : F →+* A) (p : GlobalTheory.HilbertRecip.Place F) (x d : Fˣ)
    (h : x ∈ GlobalTheory.HilbertRecip.nrm p d ↔ ∃ a b : A, φ x = a ^ 2 - φ d * b ^ 2) :
    Loc.hs (φ d) (φ x) = (((GlobalTheory.HilbertRecip.hs p x d : ℤˣ) : ℤ) : ℂ) := by
  unfold Loc.hs
  by_cases hx : x ∈ GlobalTheory.HilbertRecip.nrm p d
  · obtain ⟨a, b, e⟩ := h.1 hx
    rw [if_pos ⟨a, b, e.symm⟩, GlobalTheory.HilbertRecip.hs_eq_one_iff.2 hx]
    simp
  · rw [if_neg fun ⟨a, b, e⟩ => hx (h.2 ⟨a, b, e.symm⟩), GlobalTheory.HilbertRecip.hs_eq_neg_one_iff.2 hx]
    simp

theorem UpperTheory.V.Z.Sym.Glob.recip :
    UpperTheory.V.Z.Sym.Glob.Recip := by
  intro F _ _ d x hd hx
  classical
  lift d to Fˣ using hd.isUnit
  lift x to Fˣ using hx.isUnit
  have h1 : ∀ v : Pl F, Loc.hs (cv v d) (cv v x) = (((GlobalTheory.HilbertRecip.hs (.inl v) x d : ℤˣ) : ℤ) : ℂ) :=
    fun v => hs_cast (cv v) (.inl v) x d Iff.rfl
  have h2 : ∀ σ : F →+* ℝ, Loc.hs (σ d) (σ x) = (((GlobalTheory.HilbertRecip.hs (.inr σ) x d : ℤˣ) : ℤ) : ℂ) :=
    fun σ => hs_cast σ (.inr σ) x d Iff.rfl
  have hfin : {v : Pl F | x ∉ GlobalTheory.HilbertRecip.nrm (.inl v) d}.Finite :=
    (GlobalTheory.HilbertRecip.finite_not_mem_nrm x d).preimage (f := Sum.inl) Sum.inl_injective.injOn
  have hsub : {v : Pl F | Loc.hs (cv v d) (cv v x) ≠ 1} ⊆ {v : Pl F | x ∉ GlobalTheory.HilbertRecip.nrm (.inl v) d} := by
    intro v hv hm
    refine hv ?_
    rw [h1, GlobalTheory.HilbertRecip.hs_eq_one_iff.2 hm]
    simp
  refine ⟨hfin.subset hsub, ?_⟩
  have h := GlobalTheory.HilbertRecip.prod_hs x d (hfin.toFinset.disjSum Finset.univ) (by
    rintro (v | σ) hv
    · rw [Finset.inl_mem_disjSum, Set.Finite.mem_toFinset]
      exact hv
    · simp)
  rw [Finset.prod_disjSum, mul_eq_one_iff_eq_inv, Int.units_inv_eq_self] at h
  rw [finprod_eq_prod_of_mulSupport_subset _ (s := hfin.toFinset) (by rw [Set.Finite.coe_toFinset]; exact hsub)]
  simp only [h1, h2]
  have h' := congrArg (fun u : ℤˣ => ((u : ℤ) : ℂ)) h
  simpa only [Units.coe_prod, Int.cast_prod] using h'
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.SelCard
section
open NumberField IsDedekindDomain

namespace UpperTheory.V.Z.Sym.Glob

open Loc

private theorem ev_mul {O K : Type} [CommRing O] [Field K] [Algebra O K] {x y : K} (h : EvenVal O x) (h' : EvenVal O y) :
    EvenVal O (x * y) := by
  obtain ⟨u, s, hs, rfl⟩ := h
  obtain ⟨u', s', hs', rfl⟩ := h'
  exact ⟨u * u', s * s', mul_ne_zero hs hs', by simp only [Units.val_mul, map_mul]; ring⟩

private theorem ev_sq {O K : Type} [CommRing O] [Field K] [Algebra O K] {s : K} (hs : s ≠ 0) : EvenVal O (s ^ 2) :=
  ⟨1, s, hs, by simp⟩

variable {F : Type} [Field F] [NumberField F]

private theorem dvd_of_ev (v : Pl F) (a : Fˣ) (h : EvenVal (Ov v) (cv v (a : F))) : ((2 : ℕ) : ℤ) ∣ Kum.ordv v a := by
  obtain ⟨u, s, hs, hx⟩ := h
  have hu : ∀ w : (Ov v)ˣ, Valued.v (algebraMap (Ov v) (Kv v) ↑w) = 1 := by
    intro w
    have ha : Valued.v (algebraMap (Ov v) (Kv v) ↑w) ≤ 1 := (w : Ov v).2
    have hb : Valued.v (algebraMap (Ov v) (Kv v) ↑w⁻¹) ≤ 1 := ((w⁻¹ : (Ov v)ˣ) : Ov v).2
    have hm : Valued.v (algebraMap (Ov v) (Kv v) ↑w) * Valued.v (algebraMap (Ov v) (Kv v) ↑w⁻¹) = 1 := by
      rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
    refine le_antisymm ha ?_
    calc (1 : WithZero (Multiplicative ℤ)) = _ := hm.symm
      _ ≤ Valued.v (algebraMap (Ov v) (Kv v) ↑w) * 1 := by gcongr
      _ = _ := mul_one _
  have hv := congrArg Valued.v hx
  rw [map_mul, hu, one_mul, map_pow] at hv
  have hs0 : Valued.v s ≠ 0 := (Valuation.ne_zero_iff _).mpr hs
  obtain ⟨w, hw⟩ := WithZero.ne_zero_iff_exists.mp hs0
  have hva : Valued.v (cv v (a : F)) = v.valuation F (a : F) :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (a : F)
  have h2 : ((v.valuationOfNeZero a : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) =
      ((w ^ 2 : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
    rw [HeightOneSpectrum.valuationOfNeZero_eq, ← hva, hv, WithZero.coe_pow, hw]
  have h3 := WithZero.coe_inj.mp h2
  refine ⟨-Multiplicative.toAdd w, ?_⟩
  simp only [Kum.ordv, h3, toAdd_pow, smul_eq_mul]
  push_cast
  ring

private theorem fin_sel (S : Finset (Pl F)) :
    {c : Fˣ ⧸ (powMonoidHom 2 : Fˣ →* Fˣ).range | c.out ∈ Kum.SelK (S : Set (Pl F)) 2}.Finite := by
  classical
  have hS : (S : Set (Pl F)).Finite := S.finite_toSet
  have hc := Kum.cardSel F (S : Set (Pl F)) 2 two_ne_zero
  have hu := Kum.cardSUnit F (S : Set (Pl F)) 2 hS
  have hne : Nat.card (↥(Kum.SelK (S : Set (Pl F)) 2) ⧸
      (Kum.powK F 2).subgroupOf (Kum.SelK (S : Set (Pl F)) 2)) ≠ 0 := by
    rw [hc, hu]
    have h1 : Nat.card ↥(rootsOfUnity 2 F) ≠ 0 := Nat.card_pos.ne'
    have h2 : Nat.card { c : Kum.ClS (S : Set (Pl F)) // c ^ 2 = 1 } ≠ 0 := by
      haveI : Nonempty { c : Kum.ClS (S : Set (Pl F)) // c ^ 2 = 1 } := ⟨⟨1, one_pow 2⟩⟩
      exact Nat.card_pos.ne'
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ two_ne_zero) h1) h2
  haveI := Nat.finite_of_card_ne_zero hne
  let f : {c : Fˣ ⧸ (powMonoidHom 2 : Fˣ →* Fˣ).range | c.out ∈ Kum.SelK (S : Set (Pl F)) 2} →
      (↥(Kum.SelK (S : Set (Pl F)) 2) ⧸ (Kum.powK F 2).subgroupOf (Kum.SelK (S : Set (Pl F)) 2)) :=
    fun c => QuotientGroup.mk ⟨c.1.out, c.2⟩
  have hf : Function.Injective f := by
    rintro ⟨c, hc⟩ ⟨c', hc'⟩ h
    have h' := QuotientGroup.eq.mp h
    rw [Subgroup.mem_subgroupOf] at h'
    apply Subtype.ext
    show c = c'
    rw [← QuotientGroup.out_eq' c, ← QuotientGroup.out_eq' c']
    apply QuotientGroup.eq.mpr
    simpa [Kum.powK] using h'
  exact Set.finite_coe_iff.mp (Finite.of_injective f hf)

variable {Δ : F} (D : Dat Δ)

private theorem quotient_out_eq_mul_sq (a : Fˣ) :
    ∃ b : Fˣ, ((Quotient.out (a : Fˣ ⧸ (powMonoidHom 2 : Fˣ →* Fˣ).range) : Fˣ) : F) = (a : F) * (b : F) ^ 2 := by
  have h := QuotientGroup.eq.mp (QuotientGroup.out_eq' (a : Fˣ ⧸ (powMonoidHom 2 : Fˣ →* Fˣ).range))
  obtain ⟨b, hb⟩ := h
  have hb' : b ^ 2 = (Quotient.out (a : Fˣ ⧸ (powMonoidHom 2 : Fˣ →* Fˣ).range))⁻¹ * a := hb
  refine ⟨b⁻¹, ?_⟩
  have e : Quotient.out (a : Fˣ ⧸ (powMonoidHom 2 : Fˣ →* Fˣ).range) = a * (b⁻¹) ^ 2 := by
    rw [inv_pow, hb']
    group
  rw [e]
  push_cast
  ring

private theorem mem_sel (y : F) (a : Fˣ) (h : TPos (a : F)) (h' : D.Ev ((a : F) * y)) :
    (a : Fˣ ⧸ (powMonoidHom 2 : Fˣ →* Fˣ).range) ∈ D.Sel y := by
  obtain ⟨b, hb⟩ := quotient_out_eq_mul_sq a
  simp only [Dat.Sel, Set.mem_setOf_eq]
  rw [hb]
  constructor
  · intro σ
    rw [map_mul, map_pow]
    have hne : σ (b : F) ≠ 0 := (map_ne_zero σ).mpr b.ne_zero
    exact mul_pos (h σ) (lt_of_le_of_ne (sq_nonneg _) (pow_ne_zero 2 hne).symm)
  · intro v hv
    rw [show (a : F) * (b : F) ^ 2 * y = ((a : F) * y) * (b : F) ^ 2 by ring, map_mul, map_pow]
    exact ev_mul (h' v hv) (ev_sq ((map_ne_zero _).mpr b.ne_zero))

end UpperTheory.V.Z.Sym.Glob

open UpperTheory.V.Z.Sym.Glob in
theorem UpperTheory.V.Z.Sym.Glob.selCard :
    UpperTheory.V.Z.Sym.Glob.SelCard := by
  intro F _ _ Δ D hOk
  haveI := hOk.real
  have hfin1 : (D.Sel 1).Finite := by
    refine (fin_sel D.Sg).subset ?_
    intro c hc v hv
    exact dvd_of_ev v _ (by simpa using hc.2 v (by simpa using hv))
  have hnon : (D.Sel 1).Nonempty :=
    ⟨_, mem_sel D 1 1 (fun σ => by simp)
      (fun v _ => by simpa using ev_sq (O := Ov v) (one_ne_zero (α := Kv v)))⟩
  refine ⟨hfin1, hnon, ?_⟩
  intro y hy
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have σ0 := InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal w)
  have hy0 : y ≠ 0 := fun h0 => by
    have := hy σ0
    simp [h0] at this
  obtain ⟨yU, hyU⟩ : ∃ u : Fˣ, (u : F) = y := ⟨Units.mk0 y hy0, rfl⟩
  have hmul : ∀ c ∈ D.Sel 1, c * (yU : Fˣ ⧸ (powMonoidHom 2 : Fˣ →* Fˣ).range) ∈ D.Sel y := by
    intro c hc
    have e : c * (yU : Fˣ ⧸ (powMonoidHom 2 : Fˣ →* Fˣ).range) =
        ((c.out * yU : Fˣ) : Fˣ ⧸ (powMonoidHom 2 : Fˣ →* Fˣ).range) := by
      rw [QuotientGroup.mk_mul, QuotientGroup.out_eq']
    rw [e]
    apply mem_sel D y
    · intro σ
      rw [Units.val_mul, hyU, map_mul]
      exact mul_pos (hc.1 σ) (hy σ)
    · intro v hv
      have h1 := hc.2 v hv
      rw [show ((c.out * yU : Fˣ) : F) * y = ((c.out : F) * 1) * y ^ 2 by rw [Units.val_mul, hyU]; ring,
        map_mul (cv v), map_pow]
      exact ev_mul h1 (ev_sq ((map_ne_zero _).mpr hy0))
  have hback : ∀ c ∈ D.Sel y, c * (yU : Fˣ ⧸ (powMonoidHom 2 : Fˣ →* Fˣ).range) ∈ D.Sel 1 := by
    intro c hc
    have e : c * (yU : Fˣ ⧸ (powMonoidHom 2 : Fˣ →* Fˣ).range) =
        ((c.out * yU : Fˣ) : Fˣ ⧸ (powMonoidHom 2 : Fˣ →* Fˣ).range) := by
      rw [QuotientGroup.mk_mul, QuotientGroup.out_eq']
    rw [e]
    apply mem_sel D 1
    · intro σ
      rw [Units.val_mul, hyU, map_mul]
      exact mul_pos (hc.1 σ) (hy σ)
    · intro v hv
      rw [Units.val_mul, hyU, mul_one]
      exact hc.2 v hv
  have hsq : (yU : Fˣ ⧸ (powMonoidHom 2 : Fˣ →* Fˣ).range) * (yU : Fˣ ⧸ (powMonoidHom 2 : Fˣ →* Fˣ).range) = 1 := by
    rw [← QuotientGroup.mk_mul]
    exact (QuotientGroup.eq_one_iff _).mpr ⟨yU, sq yU⟩
  have himg : (fun c => c * (yU : Fˣ ⧸ (powMonoidHom 2 : Fˣ →* Fˣ).range)) '' D.Sel 1 = D.Sel y := by
    ext c
    constructor
    · rintro ⟨c', hc', rfl⟩
      exact hmul c' hc'
    · intro hc
      refine ⟨c * yU, hback c hc, ?_⟩
      show c * (yU : Fˣ ⧸ (powMonoidHom 2 : Fˣ →* Fˣ).range) * (yU : Fˣ ⧸ (powMonoidHom 2 : Fˣ →* Fˣ).range) = c
      rw [mul_assoc, hsq, mul_one]
  have hinj : Function.Injective (fun c : Fˣ ⧸ (powMonoidHom 2 : Fˣ →* Fˣ).range =>
      c * (yU : Fˣ ⧸ (powMonoidHom 2 : Fˣ →* Fˣ).range)) := mul_left_injective _
  rw [← himg]
  exact ⟨hfin1.image _, Set.ncard_image_of_injective _ hinj⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.SigOneAdd
section
open QuadraticAlgebra NumberField UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob

namespace UpperTheory.V.Z.Sym.Glob.GlobalDataExistence

private theorem sq_of_norm {K R : Type} [Field K] [Field R] (f : K →+* R) {Δ τ : K} (a : R) (ha : a ^ 2 = f τ * a - 1)
    (d : EL Δ τ) (hd : d * sigL d = ofE Δ (ω : Etau K τ)) : ∃ x y : R, x ^ 2 - f Δ * y ^ 2 = a := by
  obtain ⟨⟨p0, q0⟩, ⟨p1, q1⟩⟩ := d
  have h1 : p0 ^ 2 - Δ * q0 ^ 2 - (p1 ^ 2 - Δ * q1 ^ 2) = 0 := by
    have := congrArg (fun z : EL Δ τ => z.re.re) hd
    simp [sigL, ofE, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one] at this
    linear_combination this
  have h2 : 2 * (p0 * p1 - Δ * q0 * q1) + τ * (p1 ^ 2 - Δ * q1 ^ 2) = 1 := by
    have := congrArg (fun z : EL Δ τ => z.im.re) hd
    simp [sigL, ofE, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one] at this
    linear_combination this
  have g1 := congrArg f h1
  have g2 := congrArg f h2
  simp only [map_sub, map_add (f := _), map_mul, map_pow, map_zero, map_one, map_ofNat] at g1 g2
  exact ⟨f p0 + f p1 * a, f q0 + f q1 * a, by linear_combination g1 + a * g2 + (f p1 ^ 2 - f Δ * f q1 ^ 2) * ha⟩

private theorem norm_of_sq {K : Type} [Field K] {Δ τ : K} (x y : Etau K τ)
    (h : x ^ 2 - algebraMap K (Etau K τ) Δ * y ^ 2 = ω) : ∃ d : EL Δ τ, d * sigL d = ofE Δ (ω : Etau K τ) := by
  obtain ⟨p0, p1⟩ := x
  obtain ⟨q0, q1⟩ := y
  have h1 := congrArg QuadraticAlgebra.re h
  have h2 := congrArg QuadraticAlgebra.im h
  simp [pow_two] at h1 h2
  refine ⟨⟨⟨p0, q0⟩, ⟨p1, q1⟩⟩, ?_⟩
  ext <;> simp [sigL, ofE, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  · linear_combination h1
  · ring
  · linear_combination h2
  · ring

private theorem hasse {F : Type} [Field F] [NumberField F] {Δ : F} (D : Dat Δ) (h : D.Ok) (τ : F) (hτ : IsCM τ)
    (hi : ∀ v ∉ D.Sg, cv v τ ∈ (algebraMap (Ov v) (Kv v)).range) (hΔ : Δ ≠ 0)
    (E : Type) [Field E] [NumberField E] [Algebra F E] (a : E) (ha : a ^ 2 = algebraMap F E τ * a - 1) :
    ∃ x y : E, x ^ 2 - algebraMap F E Δ * y ^ 2 = a := by
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp at ha
  have key : hs (algebraMap F E Δ) a = 1 := by
    refine hsHasse E _ a ((map_ne_zero _).2 hΔ) ha0 (fun σ => ?_) fun w => ?_
    · exfalso
      have h1 := hτ (σ.comp (algebraMap F E))
      have h2 := congrArg σ ha
      simp only [map_sub, map_mul, map_pow, map_one, map_ofNat, RingHom.comp_apply] at h1 h2
      nlinarith [sq_nonneg (2 * σ a - σ (algebraMap F E τ))]
    · let v : Pl F := w.under (𝓞 F)
      haveI : w.asIdeal.LiesOver v.asIdeal := ⟨rfl⟩
      have hf : ∀ x : F, KStar.Choice.complMap v w (cv v x) = cv w (algebraMap F E x) :=
        KStar.Choice.complMap_algebraMap v w
      unfold hs
      rw [if_pos]
      by_cases hv : v ∈ D.Sg
      · obtain ⟨s, hs⟩ := h.split v hv
        have e := congrArg (KStar.Choice.complMap v w) hs
        rw [hf, map_mul] at e
        set r := KStar.Choice.complMap v w s
        have hr : r ≠ 0 := by
          rintro h0
          rw [h0, mul_zero, map_eq_zero, map_eq_zero] at e
          exact hΔ e
        haveI : CharZero (Kv w) := algebraRat.charZero _
        refine ⟨(cv w a + 1) / 2, (cv w a - 1) / (2 * r), ?_⟩
        rw [e]
        field_simp
        ring
      · obtain ⟨d, hd⟩ := locNorm (Ov v) (Kv v) (cv v Δ) (cv v τ) (h.off v hv) (hi v hv)
        rw [← hf]
        refine sq_of_norm _ _ ?_ d hd
        rw [hf, ← map_pow, ha, map_sub, map_mul, map_one]
  unfold hs at key
  by_contra hn
  rw [if_neg hn] at key
  norm_num at key

private theorem d_ex {F : Type} [Field F] [NumberField F] {Δ : F} (D : Dat Δ) (h : D.Ok) (τ : F) (hτ : IsCM τ)
    (hi : ∀ v ∉ D.Sg, cv v τ ∈ (algebraMap (Ov v) (Kv v)).range) (σ : F →+* ℝ) :
    ∃ d : EL Δ τ, d * sigL d = ofE Δ (ω : Etau F τ) := by
  have hΔ : Δ ≠ 0 := fun h0 => by simpa [h0] using h.neg σ
  haveI : Fact (∀ r : F, r ^ 2 ≠ -1 + τ * r) := ⟨fun r hr => by
    have h1 := hτ σ
    have h2 := congrArg σ hr
    simp only [map_sub, map_add (f := _), map_neg, map_mul, map_pow, map_one, map_ofNat] at h1 h2
    nlinarith [sq_nonneg (2 * σ r - σ τ)]⟩
  haveI : NumberField (Etau F τ) := NumberField.of_module_finite F _
  obtain ⟨x, y, hxy⟩ := hasse D h τ hτ hi hΔ (Etau F τ) ω (by ext <;> simp [pow_two, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one])
  exact norm_of_sq x y hxy

private theorem tr_re {K : Type} [Field K] {Δ τ : K} (y : EL Δ τ) :
    (QuadraticAlgebra.trace (y * star (sigL y))).re =
      2 * (y.re.re ^ 2 + τ * y.re.re * y.im.re + y.im.re ^ 2) - 2 * Δ * (y.re.im ^ 2 + τ * y.re.im * y.im.im + y.im.im ^ 2) := by
  obtain ⟨⟨p0, q0⟩, ⟨p1, q1⟩⟩ := y
  simp [sigL, QuadraticAlgebra.trace_def, two_mul, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  ring

private theorem q_nonneg {t : ℝ} (ht : t ^ 2 - 4 < 0) (p q : ℝ) : 0 ≤ p ^ 2 + t * p * q + q ^ 2 := by
  nlinarith [sq_nonneg (2 * p + t * q), mul_nonneg (sub_nonneg.2 (show t ^ 2 ≤ 4 by linarith)) (sq_nonneg q)]

private theorem q_zero {t : ℝ} (ht : t ^ 2 - 4 < 0) {p q : ℝ} (h : p ^ 2 + t * p * q + q ^ 2 = 0) : p = 0 ∧ q = 0 := by
  have hq : q = 0 := by
    by_contra hq
    nlinarith [sq_nonneg (2 * p + t * q), mul_pos (sub_pos.2 (show t ^ 2 < 4 by linarith)) (sq_pos_of_ne_zero hq)]
  subst hq
  exact ⟨by simpa using h, rfl⟩

private theorem tr_pos {K : Type} [Field K] {Δ τ : K} (σ : K →+* ℝ) (hΔ : σ Δ < 0) (hτ : σ (τ ^ 2 - 4) < 0) (y : EL Δ τ) :
    0 ≤ σ (QuadraticAlgebra.trace (y * star (sigL y))).re ∧ (y ≠ 0 → 0 < σ (QuadraticAlgebra.trace (y * star (sigL y))).re) := by
  rw [tr_re]
  simp only [map_sub, map_add (f := _), map_mul, map_pow, map_ofNat] at hτ ⊢
  have h1 := q_nonneg hτ (σ y.re.re) (σ y.im.re)
  have h2 := q_nonneg hτ (σ y.re.im) (σ y.im.im)
  have h3 := mul_nonneg (neg_pos.2 hΔ).le h2
  refine ⟨by linarith, fun hy => ?_⟩
  by_contra hn
  have e1 := q_zero hτ (le_antisymm (by linarith) h1)
  have e2 := q_zero hτ ((mul_eq_zero.1 (le_antisymm (by linarith) h3)).resolve_left (neg_pos.2 hΔ).ne')
  simp only [map_eq_zero] at e1 e2
  exact hy (by ext <;> simp [e1.1, e1.2, e2.1, e2.2])

private theorem sig_mul {K : Type} [Field K] {Δ τ : K} (x y : EL Δ τ) : sigL (x * y) = sigL x * sigL y := by
  ext <;> simp [sigL] <;> ring

private theorem sig_sig {K : Type} [Field K] {Δ τ : K} (x : EL Δ τ) : sigL (sigL x) = x := by
  ext <;> simp [sigL]

private theorem sig_star {K : Type} [Field K] {Δ τ : K} (x : EL Δ τ) : sigL (star x) = star (sigL x) := by
  ext <;> simp [sigL]

private theorem sig_one_add {K : Type} [Field K] {Δ τ : K} (x : EL Δ τ) : sigL (1 + x) = 1 + sigL x := by
  ext <;> simp [sigL, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]

private theorem posF {F : Type} [Field F] {Δ τ : F} (hΔ : ∀ σ : F →+* ℝ, σ Δ < 0) (hτ : IsCM τ) (d : EL Δ τ) :
    PosF 1 (1 + sigL d * star d) := by
  rintro ⟨⟨p, q⟩, x⟩ hx σ
  have e : (1 + sigL d * star d) * x * star (sigL x) = x * star (sigL x) + (sigL d * x) * star (sigL (sigL d * x)) := by
    rw [sig_mul, sig_sig, star_mul]
    ring
  have e2 : (herm 1 (1 + sigL d * star d) (⟨p, q⟩, x) (⟨p, q⟩, x)).re = p ^ 2 - Δ * q ^ 2 +
      ((QuadraticAlgebra.trace (x * star (sigL x))).re + (QuadraticAlgebra.trace ((sigL d * x) * star (sigL (sigL d * x)))).re) := by
    simp only [herm]
    rw [e, map_add (f := _), map_one, one_mul]
    simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.re_mul, QuadraticAlgebra.re_star, QuadraticAlgebra.im_star]
    ring
  rw [e2]
  have h1 := tr_pos σ (hΔ σ) (hτ σ) x
  have h2 := (tr_pos σ (hΔ σ) (hτ σ) (sigL d * x)).1
  simp only [map_add σ, map_sub σ, map_mul σ, map_pow σ]
  have h3 := mul_nonneg (neg_pos.2 (hΔ σ)).le (sq_nonneg (σ q))
  have h4 := sq_nonneg (σ p)
  by_cases h0 : x = 0
  · by_contra hn
    have hp : σ p ^ 2 = 0 := le_antisymm (by linarith [h1.1]) h4
    have hq : σ q ^ 2 = 0 := (mul_eq_zero.1 (le_antisymm (by linarith [h1.1]) h3)).resolve_left (neg_pos.2 (hΔ σ)).ne'
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff, map_eq_zero] at hp hq
    exact hx (by rw [hp, hq, h0]; rfl)
  · linarith [h1.2 h0]

end UpperTheory.V.Z.Sym.Glob.GlobalDataExistence

open UpperTheory.V.Z.Sym.Glob.GlobalDataExistence in
theorem UpperTheory.V.Z.Sym.Glob.datEx :
    UpperTheory.V.Z.Sym.Glob.DatEx := by
  intro F _ _ Δ D h τ hτ hi
  haveI := h.real
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  let σ : F →+* ℝ := InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal w)
  obtain ⟨d, hd⟩ := d_ex D h τ hτ hi σ
  have hp := posF h.neg hτ d
  refine ⟨d, _, ⟨fun h0 => by simpa [h0] using hτ σ, one_ne_zero, hd, ?_, ?_, ?_⟩, hp⟩
  · haveI : Module.Finite F (EL Δ τ) := Module.Finite.trans (Lsq F Δ) _
    haveI : IsArtinianRing (EL Δ τ) := IsArtinianRing.of_finite F _
    refine IsArtinianRing.isUnit_iff_mem_nonZeroDivisors.2 (mem_nonZeroDivisors_iff_left.2 fun x hx => ?_)
    by_contra h0
    have := hp (0, x) (fun e => h0 (congrArg Prod.snd e)) σ
    simp [herm, hx] at this
  · rw [sig_one_add, sig_mul, sig_sig, sig_star, star_add, star_one, star_mul, star_star]
  · have e : (d * sigL d) * star (d * sigL d) = 1 := by
      rw [hd]
      ext <;> simp [ofE, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
    rw [star_mul] at e
    rw [sig_one_add, sig_mul, sig_sig, sig_star]
    linear_combination -e
end

