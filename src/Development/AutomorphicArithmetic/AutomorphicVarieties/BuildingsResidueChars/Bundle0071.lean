module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.QuadraticSplitting.QuadSplit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0067
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0218
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.WeightChange
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.Distinct
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0046
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.OrdFlagU
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0031
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0042
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0069
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle0007

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.AutomorphicFormsDescentToSmallerLevel
section
open Formalism.ConjugateSelfDual IsLocalRing UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.automorphic_forms_descent_to_smaller_level :
    UpperTheory.V.Sd.S2.Descend := by
  intro l _ c
  refine ⟨UpperTheory.V.Fr.sc_norm l c, ?_⟩
  intro ι Γ _ _ _ _ _ _ P hc hr hn
  obtain ⟨E, hE, hEr⟩ := GlobalTheory.CompactRepField.exists_finiteDimensional_entries_mem l Γ 4 P.r.toHomUnits
    fun i j => hc.matrix_elem i j
  let s : Set (PadicAlgCl l) := Set.range fun p : ι × Fin 4 × Fin 4 => P.n p.1 p.2.1 p.2.2
  haveI : Finite s := (Set.finite_range _).to_subtype
  haveI : FiniteDimensional ℚ_[l] (IntermediateField.adjoin ℚ_[l] s) :=
    IntermediateField.finiteDimensional_adjoin fun z _ =>
      (Algebra.IsAlgebraic.isAlgebraic z).isIntegral
  obtain ⟨c₁, hcc, h₁⟩ := (UpperTheory.integrality_of_norm_coefficients l).1 c (IntermediateField.adjoin ℚ_[l] s ⊔ E) inferInstance
  have hr₁ : ∀ g i j, P.r g i j ∈ c₁.O := fun g i j =>
    h₁ _ ((le_sup_right : E ≤ _) (hEr g i j)) (hr g i j)
  have hn₁ : ∀ v i j, P.n v i j ∈ c₁.O := fun v i j =>
    h₁ _ ((le_sup_left : IntermediateField.adjoin ℚ_[l] s ≤ _)
      (IntermediateField.subset_adjoin _ _ ⟨(v, i, j), rfl⟩)) (hn v i j)
  let ρ : Γ →* M4 c₁.O :=
    { toFun := fun g => Matrix.of fun i j => ⟨P.r g i j, hr₁ g i j⟩
      map_one' := by
        ext i j
        simp only [map_one, Matrix.of_apply, Matrix.one_apply]
        split_ifs <;> rfl
      map_mul' := fun g h => by
        ext i j
        simp only [map_mul, Matrix.of_apply, Matrix.mul_apply, AddSubmonoidClass.coe_finsetSum, MulMemClass.coe_mul] }
  refine ⟨c₁, hcc, ⟨ρ, fun v => Matrix.of fun i j => ⟨P.n v i j, hn₁ v i j⟩⟩, ?_, fun i j => ?_⟩
  · exact PD.ext (MonoidHom.ext fun g => Matrix.ext fun i j => rfl) (funext fun v => Matrix.ext fun i j => rfl)
  · exact ((UpperTheory.integrality_of_norm_coefficients l).2 c₁ Γ _).2 (hc.matrix_elem i j)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.DeRhamWeightsOfLocalArtinCharacters
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.HeckeGal UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem norm_q {F : Type} [Field F] [NumberField F] {l : ℕ} [Fact l.Prime] (w : HeightOneSpectrum (𝓞 F))
    (hw : ((l : ℕ) : 𝓞 F) ∈ w.asIdeal) : ((normV w : ℕ) : Qbar l) ≠ 0 ∧ ‖((normV w : ℕ) : Qbar l)‖ < 1 := by
  have := w.isMaximal
  letI := Ideal.Quotient.field w.asIdeal
  have : Finite (𝓞 F ⧸ w.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ w.ne_bot
  refine ⟨Nat.cast_ne_zero.2 Nat.card_pos.ne', ?_⟩
  letI := Fintype.ofFinite (𝓞 F ⧸ w.asIdeal)
  have hd : l ∣ normV w := by
    rw [normV, Nat.card_eq_fintype_card, ← prime_dvd_char_iff_dvd_card]
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, ringChar.spec] at hw
    have hq : (ringChar (𝓞 F ⧸ w.asIdeal)).Prime := CharP.prime_ringChar _
    rw [(Nat.prime_dvd_prime_iff_eq hq Fact.out).1 hw]
  rw [← map_natCast (algebraMap ℚ_[l] (Qbar l)), norm_algebraMap']
  exact_mod_cast Padic.norm_intCast_lt_one_iff.2 (Int.natCast_dvd_natCast.2 hd)

private theorem abs_art {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 F)} {h : IsPlaceOver A w}
    {a : Weil h →* (w.adicCompletion F)ˣ} (ha : IsLocalArtin h a) (c : ℤ) (s : Weil h) :
    (GlobalTheory.SmGL.absPow (w.adicCompletion F) (c : ℂ) (a s) : ℂ) = ((normV w : ℕ) : ℂ) ^ (c * deg s) := by
  rw [GlobalTheory.SmGL.val_absPow, GlobalTheory.LGrp.nabs_eq_zpow, ha.ord_eq, neg_neg, resCard_eq_normV, Complex.cpow_intCast,
    mul_comm, zpow_mul]
  push_cast
  rfl

private theorem cont_smooth {X : Type} [Group X] [TopologicalSpace X] [IsTopologicalGroup X] {B : Type} [Group B]
    [TopologicalSpace B] [IsTopologicalGroup B] (f : X →* B) (hf : IsOpen (f.ker : Set X)) : Continuous f := by
  refine continuous_of_continuousAt_one f ?_
  refine (continuousAt_const (y := (1 : B))).congr ?_
  filter_upwards [hf.mem_nhds f.ker.one_mem] with x hx
  exact (MonoidHom.mem_ker.1 hx).symm

theorem UpperTheory.deRham_weights_of_localArtin_characters :
    GlobalTheory.Mem.LiteralAutomorphy.LitN → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (ι : Qbar l ≃+* ℂ) (n : ℕ) (w : HeightOneSpectrum (𝓞 F)), ((l : ℕ) : 𝓞 F) ∈ w.asIdeal → ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w) (a : Weil h →* (w.adicCompletion F)ˣ), IsLocalArtin h a → ∀ (r : Dec (F := F) A →* GL (Fin n) (Qbar l)), Continuous r → ∀ (m : Fin n → ℤ), (∀ i j, i < j → m j + 2 ≤ m i) → ∀ (ω : Fin n → (w.adicCompletion F)ˣ →* ℂˣ), (∀ j, GlobalTheory.SmGL.IsSmoothChar (ω j)) → (∀ j (s : Weil h), ‖ι.symm (ω j (a s) : ℂ)‖ = ‖((normV w : ℕ) : Qbar l)‖ ^ (m j * deg s)) → Hi.DRat ι h r (fun _ => Finset.univ.val.map fun j => -m j) (fun s => ∏ j, (X - C (ω j (a s) : ℂ))) → ∃ κ : Fin n → Dec (F := F) A →* (Qbar l)ˣ, W.HasFlag r κ ∧ ∀ j (s : Weil h), (κ j (Subgroup.inclusion (Weil_le_Dec h) s) : Qbar l) * ((normV w : ℕ) : Qbar l) ^ (m j * deg s) = ι.symm (ω j (a s) : ℂ) * (cycBar F Ω l (s : G F Ω) : Qbar l) ^ m j := by
  intro N F Ω _ _ _ _ _ l _ hl ι n w hw A h a ha r hr m hm ω hω hn hD
  obtain ⟨q0, q1⟩ := norm_q w hw
  have q2 : 0 < ‖((normV w : ℕ) : Qbar l)‖ := norm_pos_iff.2 q0
  have hcyc : Continuous (cycBar F Ω l) :=
    (Continuous.units_map ((algebraMap ℚ_[l] (Qbar l)).comp PadicInt.Coe.ringHom).toMonoidHom
      ((continuous_algebraMap ℚ_[l] (Qbar l)).comp continuous_subtype_val)).comp (continuous_cycZ F Ω l)
  have key : ∀ j, ∃ κ : Dec (F := F) A →* (Qbar l)ˣ, Continuous κ ∧ ∀ s : Weil h,
      (κ (Subgroup.inclusion (Weil_le_Dec h) s) : Qbar l) * ((normV w : ℕ) : Qbar l) ^ (m j * deg s) =
        ι.symm (ω j (a s) : ℂ) * (cycBar F Ω l (s : G F Ω) : Qbar l) ^ m j := by
    intro j
    let φ := ω j * GlobalTheory.SmGL.absPow (w.adicCompletion F) ((-m j : ℤ) : ℂ)
    have hφ : GlobalTheory.SmGL.IsSmoothChar φ :=
      (hω j).mul (GlobalTheory.SmGL.isSmoothChar_of_isUnram (GlobalTheory.SmGL.isUnram_absPow _ _))
    let ξ : (w.adicCompletion F)ˣ →* (Qbar l)ˣ := (Units.map ι.symm.toRingHom.toMonoidHom).comp φ
    have hξ : ∀ s, (ξ (a s) : Qbar l) = ι.symm (ω j (a s) : ℂ) * ((normV w : ℕ) : Qbar l) ^ (-m j * deg s) := by
      intro s
      show ι.symm ((ω j (a s) : ℂ) * (GlobalTheory.SmGL.absPow (w.adicCompletion F) ((-m j : ℤ) : ℂ) (a s) : ℂ)) = _
      rw [abs_art ha, map_mul, map_zpow₀, map_natCast]
    have hc : Continuous ξ := by
      refine cont_smooth ξ (Subgroup.isOpen_mono (fun x hx => ?_) hφ)
      rw [MonoidHom.mem_ker] at hx ⊢
      rw [MonoidHom.comp_apply, hx, map_one]
    obtain ⟨κ, ⟨c1, c2⟩, -⟩ := UpperTheory.V.Loc.laExists N.aut.art h a ha ξ hc fun x => by
      obtain ⟨s, rfl⟩ := ha.surj x
      rw [hξ, norm_mul, hn, norm_zpow, ← zpow_add₀ q2.ne', neg_mul, add_neg_cancel, zpow_zero]
    refine ⟨κ * ((cycBar F Ω l).comp (Dec (F := F) A).subtype) ^ m j,
      c1.mul ((continuous_zpow (m j)).comp (hcyc.comp continuous_subtype_val)), fun s => ?_⟩
    show ((κ (Subgroup.inclusion (Weil_le_Dec h) s) * cycBar F Ω l (s : G F Ω) ^ m j : (Qbar l)ˣ) : Qbar l) * _ = _
    rw [c2, Units.val_mul, hξ, Units.val_zpow_eq_zpow_val, neg_mul, zpow_neg, mul_right_comm,
      inv_mul_cancel_right₀ (zpow_ne_zero _ q0)]
  choose κ hκ hv using key
  refine ⟨κ, (UpperTheory.V.Loc.ordFlagU N F Ω l hl ι n w hw A h a ha r hr (fun j _ => -m j)
    (fun _ i j hij => ?_) ω κ (fun j => ⟨hω j, hκ j, fun s g hg _ => ?_⟩) (fun i j hij => ?_) hD).1, hv⟩
  · have := hm i j hij
    show -m i < -m j
    omega
  · obtain rfl : g = Subgroup.inclusion (Weil_le_Dec h) s := Subtype.ext hg
    have h1 := hv j s
    rw [UpperTheory.V.Loc.epsArt N.aut.art h hw a ha s, mul_zpow, ← zpow_mul, mul_comm (deg s), mul_comm (_ ^ _),
      ← mul_assoc] at h1
    refine (mul_right_cancel₀ (zpow_ne_zero _ q0) h1).trans ?_
    congr 1
    haveI := finite_contEmb (l := l) w
    letI := Fintype.ofFinite {j : w.adicCompletion F →+* Qbar l // Continuous j}
    unfold Hi.algPow
    rw [finprod_eq_prod_of_fintype, finprod_eq_prod_of_fintype, ← Finset.prod_zpow]
    simp
  · have hi := hn i (frob h)
    have hj := hn j (frob h)
    rw [deg_frob, mul_one] at hi hj
    have hij' : m i ≠ m j ∧ m i ≠ m j + 1 := by
      rcases lt_or_gt_of_ne hij with h1 | h1
      · have := hm _ _ h1; omega
      · have := hm _ _ h1; omega
    refine ⟨fun e => hij'.1 ?_, fun e => hij'.2 ?_⟩
    · rw [e, hj] at hi
      exact (zpow_right_injective₀ q2 q1.ne hi).symm
    · have h1 := abs_art ha 1 (frob h)
      rw [deg_frob, mul_one, zpow_one, Int.cast_one] at h1
      rw [e, MonoidHom.mul_apply, Units.val_mul, h1, map_mul, map_natCast, norm_mul, hj, ← zpow_add_one₀ q2.ne'] at hi
      exact (zpow_right_injective₀ q2 q1.ne hi).symm
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.GaloisCharacterResidualDecomposition
section
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing
open GlobalTheory.GalOfCusp UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S2

noncomputable section

section SlopeTestRemainingChoices

variable {l : ℕ} [Fact l.Prime] (c : Coef l)

private def mU : c.Oˣ →* (Qbar l)ˣ := Units.map (algebraMap c.O (Qbar l)).toMonoidHom

private def bU : c.Oˣ →* (ResidueField c.O)ˣ := Units.map (residue c.O).toMonoidHom

private theorem cong_iff (x y : c.Oˣ) : Cong (mU c x) (mU c y) ↔ bU c x = bU c y := by
  have h := (UpperTheory.V.Fr.sc_norm l c ((x : c.O) - y)).2
  rw [← residue_eq_zero_iff, map_sub, sub_eq_zero] at h
  rw [Units.ext_iff]
  exact h.symm

private theorem mU_neg (x : c.Oˣ) : mU c (-x) = - mU c x :=
  Units.ext (map_neg (algebraMap c.O (Qbar l)) (x : c.O))

private theorem bU_neg (x : c.Oˣ) : bU c (-x) = - bU c x :=
  Units.ext (map_neg (residue c.O) (x : c.O))

private theorem norm_mU (x : c.Oˣ) : ‖(mU c x : Qbar l)‖ = 1 := by
  have h := UpperTheory.V.Fr.sc_norm l c (x : c.O)
  refine le_antisymm h.1 (not_lt.1 fun h1 => ?_)
  exact (mem_maximalIdeal _).1 (h.2.2 h1) x.isUnit

private theorem cont_of_ker {Γ M : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Group M] [TopologicalSpace M]
    [IsTopologicalGroup M] (f : Γ →* M) (H : Subgroup Γ) (hH : IsOpen (H : Set Γ)) (h : ∀ g ∈ H, f g = 1) : Continuous f := by
  refine continuous_of_continuousAt_one f (continuousAt_const (y := (1 : M)) |>.congr ?_)
  filter_upwards [hH.mem_nhds H.one_mem] with g hg using (h g hg).symm

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω]

private theorem cyc_eq (g : G ℚ Ω) : cycBar ℚ Ω l g = mU c (chiO ℚ Ω l c.O g) := Units.ext rfl

omit [IsAlgClosure ℚ Ω] in
private theorem cont_cyc : Continuous (cycBar ℚ Ω l) :=
  (Continuous.units_map ((algebraMap ℚ_[l] (Qbar l)).comp PadicInt.Coe.ringHom).toMonoidHom
    ((continuous_algebraMap ℚ_[l] (Qbar l)).comp continuous_subtype_val)).comp (continuous_cycZ ℚ Ω l)

variable {c} {D : Raw Ω c}

private theorem b_om (hD : D.Good) (g : G ℚ Ω) : bU c (D.om g) = bU c (chiO ℚ Ω l c.O g) := Units.ext (hD.om_bar g)

private theorem b_al (hD : D.Good) (g : G ℚ Ω) : bU c (D.al g) = bU c (D.ξ g) := by
  have : D.al g = chiO ℚ Ω l c.O g * (D.om g)⁻¹ * D.ξ g := rfl
  rw [this, map_mul, map_mul, map_inv, b_om hD, mul_inv_cancel, one_mul]

private theorem b_th (hD : D.Good) (g : G ℚ Ω) : bU c (D.th g) = bU c (D.ξ g) * bU c (D.Psi g) := by
  have : D.th g = D.al g * D.Psi g := rfl
  rw [this, map_mul, b_al hD]

private theorem chi_f (g : G ℚ Ω) : chi D false 0 g = D.al g * D.Psi g ∧ chi D false 1 g = D.Psi g ∧ chi D false 2 g = D.al g ∧
    chi D false 3 g = 1 := ⟨rfl, rfl, rfl, rfl⟩

private theorem induced_characters_values (g : G ℚ Ω) : chi D true 0 g = D.al g ∧ chi D true 1 g = 1 ∧ chi D true 2 g = D.al g * D.Psi g ∧
    chi D true 3 g = D.Psi g := ⟨rfl, rfl, rfl, rfl⟩

private theorem b_chi (hD : D.Good) (pr : Bool) (g : G ℚ Ω) :
    (bU c (chi D pr 0 g) = bU c (D.ξ g) * bU c (D.Psi g) ∧ bU c (chi D pr 1 g) = bU c (D.Psi g) ∧
      bU c (chi D pr 2 g) = bU c (D.ξ g) ∧ bU c (chi D pr 3 g) = 1) ∨
    (bU c (chi D pr 0 g) = bU c (D.ξ g) ∧ bU c (chi D pr 1 g) = 1 ∧
      bU c (chi D pr 2 g) = bU c (D.ξ g) * bU c (D.Psi g) ∧ bU c (chi D pr 3 g) = bU c (D.Psi g)) := by
  cases pr
  · left
    obtain ⟨h0, h1, h2, h3⟩ := chi_f (D := D) g
    rw [h0, h1, h2, h3, map_mul, b_al hD, map_one]
    exact ⟨rfl, rfl, rfl, rfl⟩
  · right
    obtain ⟨h0, h1, h2, h3⟩ := induced_characters_values (D := D) g
    rw [h0, h1, h2, h3, map_mul, b_al hD, map_one]
    exact ⟨rfl, rfl, rfl, rfl⟩

private theorem chi_mul (pr : Bool) (i : Fin 4) (g : G ℚ Ω) : chi D pr i g * chi D pr i.rev g = D.th g := by
  have ht : D.th g = D.al g * D.Psi g := rfl
  cases pr
  · obtain ⟨h0, h1, h2, h3⟩ := chi_f (D := D) g
    fin_cases i
    · show chi D false 0 g * chi D false 3 g = _
      rw [h0, h3, ht, mul_one]
    · show chi D false 1 g * chi D false 2 g = _
      rw [h1, h2, ht, mul_comm]
    · show chi D false 2 g * chi D false 1 g = _
      rw [h1, h2, ht]
    · show chi D false 3 g * chi D false 0 g = _
      rw [h0, h3, ht, one_mul]
  · obtain ⟨h0, h1, h2, h3⟩ := induced_characters_values (D := D) g
    fin_cases i
    · show chi D true 0 g * chi D true 3 g = _
      rw [h0, h3, ht]
    · show chi D true 1 g * chi D true 2 g = _
      rw [h1, h2, ht, one_mul]
    · show chi D true 2 g * chi D true 1 g = _
      rw [h1, h2, ht, mul_one]
    · show chi D true 3 g * chi D true 0 g = _
      rw [h0, h3, ht, mul_comm]

variable (T : Tower D)

private theorem rb_eq (w : ℤ × ℤ) (g : G T.F Ω) : T.rb w g =
    (((bU c (chi D T.pr 0 (resQ T.F g)) * (bU c (chi D T.pr 1 (resQ T.F g)))⁻¹) ^ w.1 *
      (bU c (chi D T.pr 0 (resQ T.F g)) * (bU c (chi D T.pr 2 (resQ T.F g)))⁻¹) ^ w.2 : (ResidueField c.O)ˣ) : ResidueField c.O) := by
  simp only [← map_inv (bU c), ← map_mul (bU c), ← map_zpow (bU c)]
  rfl

private theorem rb_al (hD : D.Good) (g : G T.F Ω) : T.rb wAl g = (bU c (D.ξ (resQ T.F g)) : ResidueField c.O) := by
  rw [rb_eq]
  congr 1
  generalize resQ T.F g = γ
  rcases b_chi hD T.pr γ with ⟨h0, h1, -, -⟩ | ⟨h0, h1, -, -⟩ <;> simp [wAl, h0, h1]

private theorem rb_ps (hD : D.Good) (g : G T.F Ω) (n : ℕ) : T.rb wPs g ^ n = 1 ↔ bU c (D.Psi (resQ T.F g)) ^ n = 1 := by
  rw [rb_eq, ← Units.val_pow_eq_pow_val, Units.val_eq_one]
  generalize resQ T.F g = γ
  rcases b_chi hD T.pr γ with ⟨h0, -, h2, -⟩ | ⟨h0, -, h2, -⟩
  · simp [wPs, h0, h2, mul_inv_cancel_comm]
  · simp [wPs, h0, h2, mul_comm (bU c (D.ξ _))]

end SlopeTestRemainingChoices

theorem UpperTheory.galois_character_residual_decomposition :
    UpperTheory.V.Sd.S2.Chars := by
  intro Ω _ _ _ l _ c D T k₀ φ H
  have hD := H.good
  have hup : ∀ (χ : G ℚ Ω →* c.Oˣ) g, up χ g = mU c (χ g) := fun _ _ => rfl
  have h1 : (1 : (Qbar l)ˣ) = mU c 1 := (map_one _).symm
  have hm1 : (-1 : (Qbar l)ˣ) = mU c (-1) := by rw [mU_neg, map_one]
  have hin : ∀ g : G T.F Ω, resQ T.F g ∈ k₀.fixingSubgroup ↔ bU c (D.Psi (resQ T.F g)) = 1 := fun g => by
    rw [← H.ps, ← pow_one (T.rb wPs g), rb_ps T hD, pow_one]
  have hout : ∀ g : G T.F Ω, resQ T.F g ∉ k₀.fixingSubgroup → bU c (D.Psi (resQ T.F g)) = -1 := fun g hg => by
    have h2 := (rb_ps T hD g 2).1 (H.two.sq g)
    rw [Units.ext_iff, Units.val_pow_eq_pow_val, Units.val_one, sq, mul_self_eq_one_iff] at h2
    rcases h2 with h2 | h2
    · exact absurd ((hin g).2 (Units.ext h2)) hg
    · exact Units.ext h2
  have hdist : ∀ i j, i ≠ j → bU c (chi D T.pr i (resQ T.F T.g0)) ≠ bU c (chi D T.pr j (resQ T.F T.g0)) :=
    fun i j hij h => H.ok.dist i j hij (congrArg Units.val h)
  have hg0 : resQ T.F T.g0 ∉ k₀.fixingSubgroup := by
    intro h
    refine hdist 1 3 (by decide) ?_
    rcases b_chi hD T.pr (resQ T.F T.g0) with ⟨-, h1, -, h3⟩ | ⟨-, h1, -, h3⟩ <;> rw [h1, h3, (hin _).1 h]
  have hp0 := hout _ hg0
  have hcop : l.Coprime (l - 1) := by
    have := (Fact.out : l.Prime).one_lt
    exact (Nat.coprime_self_sub_right this.le).2 (Nat.coprime_one_right l)
  have hom : ∀ g : G ℚ Ω, D.om g = 1 ↔ Cong (cycBar ℚ Ω l g) 1 := fun g => by
    rw [cyc_eq c, h1, cong_iff, ← b_om hD, map_one]
    refine ⟨fun h => by rw [h, map_one], fun h => ?_⟩
    exact UpperTheory.teichmuller_character_spec l c _ (l - 1) hcop (DFunLike.congr_fun hD.om_pow g) (congrArg Units.val h)
  have homo : IsOpen (D.om.ker : Set (G ℚ Ω)) := by
    have : (D.om.ker : Set (G ℚ Ω)) = {g | ‖(cycBar ℚ Ω l g : Qbar l) - ((1 : (Qbar l)ˣ) : Qbar l)‖ < 1} := Set.ext hom
    rw [this]
    exact isOpen_lt ((Units.continuous_val.comp cont_cyc).sub continuous_const).norm continuous_const
  refine ⟨fun χ g => norm_mU c _, fun i g => ?_, fun g hg i => ?_, hg0, ?_, ?_, ?_, ?_, fun k hk g => ?_, fun k => ?_,
    fun g n => ?_, fun g hg => ?_, hom, homo⟩
  · rw [hup, hup, hup, ← map_mul, chi_mul]
  · have hp := (hin g).1 hg
    have e : (![up D.ξ, 1, up D.ξ, 1] i (resQ T.F g) : (Qbar l)ˣ) = mU c (![D.ξ (resQ T.F g), 1, D.ξ (resQ T.F g), 1] i) := by
      fin_cases i
      exacts [rfl, h1, rfl, h1]
    rw [e, hup, cong_iff]
    clear e
    generalize resQ T.F g = γ at hp ⊢
    rcases b_chi hD T.pr γ with ⟨h0, h1, h2, h3⟩ | ⟨h0, h1, h2, h3⟩ <;> fin_cases i <;> simp [h0, h1, h2, h3, hp]
  · rw [h1, hup, cong_iff, map_one, map_mul, map_mul, eq_comm, Units.ext_iff, Units.val_mul, Units.val_one, mul_self_eq_one_iff]
    intro h
    have h' : bU c (D.ξ (resQ T.F T.g0)) = 1 ∨ bU c (D.ξ (resQ T.F T.g0)) = -1 := h.imp Units.ext Units.ext
    have d1 := hdist 0 1 (by decide)
    have d3 := hdist 0 3 (by decide)
    generalize resQ T.F T.g0 = γ at hp0 d1 d3 h'
    rcases b_chi hD T.pr γ with ⟨h0, h1, h2, h3⟩ | ⟨h0, h1, h2, h3⟩ <;> rcases h' with h' | h' <;>
      simp [h0, h1, h3, hp0, h'] at d1 d3
  · rw [hm1, h1, hup, cong_iff, cong_iff, bU_neg, map_one]
    rcases b_chi hD T.pr (resQ T.F T.g0) with ⟨h0, h1, h2, h3⟩ | ⟨h0, h1, h2, h3⟩
    · exact Or.inl h3
    · exact Or.inr (h3.trans hp0)
  · rw [hup, hup, ← mU_neg, cong_iff, bU_neg]
    generalize resQ T.F T.g0 = γ at hp0 ⊢
    rcases b_chi hD T.pr γ with ⟨h0, h1, h2, h3⟩ | ⟨h0, h1, h2, h3⟩ <;> simp [h1, h3, hp0]
  · rw [hup, hup, ← mU_neg, cong_iff, bU_neg]
    generalize resQ T.F T.g0 = γ at hp0 ⊢
    rcases b_chi hD T.pr γ with ⟨h0, h1, h2, h3⟩ | ⟨h0, h1, h2, h3⟩ <;> simp [h0, h2, hp0]
  · obtain ⟨j, rfl⟩ := hk
    have ho : bU c (chiO ℚ Ω l c.O (resQ T.F g)) ^ ((l - 1) * j) = 1 := by
      have : D.om (resQ T.F g) ^ (l - 1) = 1 := DFunLike.congr_fun hD.om_pow _
      rw [← b_om hD, pow_mul, ← map_pow, this, map_one, one_pow]
    rw [MonoidHom.mul_apply, MonoidHom.mul_apply, MonoidHom.pow_apply, cyc_eq c, hup, hup]
    by_cases hg : resQ T.F g ∈ k₀.fixingSubgroup
    · rw [H.φ_in _ hg, mul_one, ← map_pow, ← map_mul, cong_iff, b_th hD, map_mul, map_pow, ho, (hin g).1 hg, mul_one, one_mul]
    · rw [H.φ_out _ hg, hm1, ← map_pow, ← map_mul, ← map_mul, cong_iff, b_th hD, map_mul, map_mul, map_pow, ho, hout g hg, bU_neg,
        map_one, one_mul]
  · haveI : FiniteDimensional ℚ k₀ := Module.finite_of_finrank_pos (by rw [H.deg]; norm_num)
    have cφ : Continuous φ := cont_of_ker φ _ k₀.fixingSubgroup_isOpen H.φ_in
    have cu : ∀ χ : G ℚ Ω →* c.Oˣ, IsOpen (χ.ker : Set (G ℚ Ω)) → Continuous (up χ) := fun χ hχ =>
      cont_of_ker _ _ hχ fun g hg => by rw [hup, MonoidHom.mem_ker.1 hg, map_one]
    have cξ := cu _ hD.xi_open
    have cψ := cu _ hD.psi_open
    have co := cu _ homo
    have cc : Continuous (cycBar ℚ Ω l) := cont_cyc
    refine (((cc.mul co.inv).mul cξ).mul ((cc.zpow D.e).mul cψ) |>.div' (((cc.pow k).mul cξ).mul cφ)).congr fun g => ?_
    have : D.th g = chiO ℚ Ω l c.O g * (D.om g)⁻¹ * D.ξ g * (chiO ℚ Ω l c.O g ^ (D.e : ℤ) * D.ψ g) := rfl
    show _ = up D.th g / (cycBar ℚ Ω l g ^ k * up D.ξ g * φ g)
    rw [hup D.th, this]
    simp only [map_mul, map_inv, map_zpow, ← cyc_eq, ← hup]
    rfl
  · rw [rb_al T hD, hup, ← map_pow, h1, cong_iff, map_pow, map_one, ← Units.val_pow_eq_pow_val, Units.val_eq_one]
  · obtain ⟨m, hm, hx⟩ := hD.xi_ord
    rw [hup, h1, cong_iff, map_one] at hg
    exact UpperTheory.teichmuller_character_spec l c _ m hm (DFunLike.congr_fun hx g) (congrArg Units.val hg)
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.InducedDeletionCondition
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S2

private theorem norm_two (l : ℕ) [Fact l.Prime] (hl : l ≠ 2) : ‖(2 : Qbar l)‖ = 1 := by
  have h : (2 : Qbar l) = algebraMap ℚ_[l] (Qbar l) ((2 : ℕ) : ℚ_[l]) := by simp [map_ofNat]
  rw [h, norm_algebraMap', Padic.norm_natCast_eq_one_iff]
  exact (Nat.coprime_primes Fact.out Nat.prime_two).2 hl

private theorem alg {A : Type} [CommGroup A] (d x o p q f : A) (k e : ℕ)
    (h : d ^ 2 * (x ^ k * q * f) = x * o⁻¹ * q * (x ^ (e : ℤ) * p)) :
    d ^ 2 = x ^ ((e : ℤ) + 1 - k) * (o⁻¹ * p * f⁻¹) := by
  rw [eq_mul_inv_of_mul_eq h, zpow_sub, zpow_add, zpow_one, zpow_natCast, zpow_natCast]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_pow]
  abel

private theorem pow_one_of_dvd {A : Type} [Monoid A] {x : A} {a : ℕ} (h : x ^ a = 1) {n : ℕ} (hn : a ∣ n) : x ^ n = 1 := by
  obtain ⟨b, rfl⟩ := hn
  rw [pow_mul, h, one_pow]

theorem UpperTheory.induced_deletion_condition :
    UpperTheory.V.Sd.S2.IndDel := by
  intro Ω _ _ _ l hl c D T k₀ _ _ φ ι k t r α β R δ h
  have hG := h.hyp.good
  have hchi : ∀ g : G T.F Ω, up (chiO ℚ Ω l c.O) (resQ T.F g) = cycBar T.F Ω l g := fun g => Units.ext rfl
  have key : ∀ g : G T.F Ω, δ g ^ 2 = cycBar T.F Ω l g ^ ((D.e : ℤ) + 1 - k) *
      ((up D.om (resQ T.F g))⁻¹ * up D.ψ (resQ T.F g) * (φ (resQ T.F g))⁻¹) := by
    intro g
    apply alg _ _ _ _ (up D.ξ (resQ T.F g))
    have h1 := h.δ_sq g
    have h2 : up D.th (resQ T.F g) = cycBar T.F Ω l g * (up D.om (resQ T.F g))⁻¹ * up D.ξ (resQ T.F g) *
        (cycBar T.F Ω l g ^ (D.e : ℤ) * up D.ψ (resQ T.F g)) := by
      rw [← hchi]
      simp only [up, Raw.th, Raw.al, Raw.Psi, UpperTheory.V.Chr.Psi, MonoidHom.comp_apply, MonoidHom.mul_apply, MonoidHom.inv_apply,
        MonoidHom.zpow_apply, map_mul, map_inv, map_zpow]
    rw [← h2, ← h1]
    rfl
  obtain ⟨m, hm, hψ⟩ := h.hyp.deep
  have hl1 : 1 < l := hl.out.one_lt
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with rfl | h0
    · rw [Nat.coprime_zero_right] at hm; omega
    · exact h0
  have hφ : ∀ g, φ g ^ 2 = 1 := by
    intro g
    by_cases hg : g ∈ k₀.fixingSubgroup
    · rw [h.hyp.φ_in g hg, one_pow]
    · rw [h.hyp.φ_out g hg]; simp
  have hφI : ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ∀ s ∈ Ine (F := T.F) A, φ (resQ T.F s) = 1 := by
    intro A hA s hs
    apply h.hyp.φ_in
    apply h.hyp.spl A hA
    exact hs.1
  have hcont : Continuous (resQ T.F) := by
    haveI : IsAlgClosure T.F Ω := ⟨IsAlgClosure.isAlgClosed ℚ, inferInstance⟩
    exact (galEmbTop ℚ T.F Ω).1.continuous
  have hup : ∀ (χ : G ℚ Ω →* c.Oˣ) g, χ g = 1 → up χ g = 1 := fun χ g hg => by
    simp only [up, MonoidHom.comp_apply, hg, map_one]
  refine ⟨(D.e : ℤ) + 1 - k, (l - 1) * m * 2, (D.ψ.ker ⊓ D.om.ker).comap (resQ T.F), ?_, ?_, ?_, ?_⟩
  · exact Nat.mul_pos (Nat.mul_pos (by omega) hm0) two_pos
  · intro g
    have a1 : up D.om (resQ T.F g) ^ (l - 1) = 1 := by
      have := DFunLike.congr_fun hG.om_pow (resQ T.F g)
      rw [MonoidHom.pow_apply, MonoidHom.one_apply] at this
      simp only [up, MonoidHom.comp_apply, ← map_pow, this, map_one]
    have a2 : up D.ψ (resQ T.F g) ^ m = 1 := by
      simp only [up, MonoidHom.comp_apply, ← map_pow, hψ g, map_one]
    have b1 := (pow_one_of_dvd a1 (n := (l - 1) * m * 2) ⟨m * 2, by ring⟩)
    have b2 := (pow_one_of_dvd a2 (n := (l - 1) * m * 2) ⟨(l - 1) * 2, by ring⟩)
    have b3 := (pow_one_of_dvd (hφ (resQ T.F g)) (n := (l - 1) * m * 2) ⟨(l - 1) * m, by ring⟩)
    rw [key g, zpow_neg, mul_inv_cancel_comm, mul_pow, mul_pow, inv_pow, inv_pow, b1, b2, b3]
    simp
  · exact (hG.psi_open.inter h.chars.om_open).preimage hcont
  · intro A hA s hs
    have fin : D.ψ (resQ T.F s) = 1 → D.om (resQ T.F s) = 1 → δ s ^ 2 = cycBar T.F Ω l s ^ ((D.e : ℤ) + 1 - k) := by
      intro h1 h2
      rw [key s, hup _ _ h1, hup _ _ h2, hφI A hA s hs]
      simp
    refine ⟨fun hU => fin hU.1 hU.2, fun hc => ?_⟩
    have hc' : cycZ ℚ Ω l (resQ T.F s) = 1 := hc
    have hb : cycBar T.F Ω l s = 1 := by
      simp only [cycBar, MonoidHom.comp_apply, hc, map_one]
    have hb' : cycBar ℚ Ω l (resQ T.F s) = 1 := hb
    have ho : D.om (resQ T.F s) = 1 := by
      rw [h.chars.om, hb']
      simp [Cong]
    have hP : D.Psi (resQ T.F s) = D.ψ (resQ T.F s) := by
      simp only [Raw.Psi, UpperTheory.V.Chr.Psi, chiO, MonoidHom.mul_apply, MonoidHom.zpow_apply, MonoidHom.comp_apply, hc', map_one,
        one_zpow, one_mul]
    have hp : D.ψ (resQ T.F s) = 1 := by
      apply UpperTheory.teichmuller_character_spec l c _ m hm (hψ s)
      have := congrFun (congrFun (h.hyp.ok.ineL A hA s hs) 1) 1
      rw [← hP]
      simpa [Raw.rbar, Raw.r0, diagRep, Raw.ps] using this
    have h2 := fin hp ho
    rw [hb, one_zpow] at h2
    have h3 : (δ s : Qbar l) ^ 2 = 1 := by rw [← Units.val_pow_eq_pow_val, h2, Units.val_one]
    rcases sq_eq_one_iff.1 h3 with h4 | h4
    · exact Units.ext h4
    · have h5 := h.δ_one s
      rw [Cong, h4, Units.val_one, show (-1 - 1 : Qbar l) = -2 by norm_num, norm_neg, norm_two l hG.l_odd] at h5
      exact absurd h5 (lt_irrefl _)
end

