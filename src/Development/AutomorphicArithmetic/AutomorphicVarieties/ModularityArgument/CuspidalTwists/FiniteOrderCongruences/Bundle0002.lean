module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.FiniteOrderCongruences.ExistsSplittingAuxiliaryCharacterForTower
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0069
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0068
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0067
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0033
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LMemMax
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0064
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0066
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.DirichletGroupPowers.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Bundle0004

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.FiniteOrderCongruences.ExistsRibetLatticeOfEisensteinRep
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N IsLocalRing Polynomial
open UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S3
open UpperTheory.V.Cu
open scoped Matrix

namespace UpperTheory.V.Cu2

namespace ModEx4

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime]

structure RibetLatticeEisensteinRep (Φ φ θ : G ℚ Ω →* (Qbar l)ˣ) (k : ℕ) (g0 : G ℚ Ω) (ρ : G ℚ Ω →* GL (Fin 2) (Qbar l))
    (x : ValuationSubring Ω → Qbar l) : Prop where
  cont : Continuous ρ
  red : ∀ g, ‖ρ g 0 0 - Φ g‖ < 1 ∧ ‖ρ g 1 1 - 1‖ < 1 ∧ ‖ρ g 0 1‖ < 1 ∧ ‖ρ g 1 0‖ ≤ 1
  ne : ∃ g, ‖ρ g 1 0‖ = 1
  nrm : ρ g0 0 1 = 0 ∧ ρ g0 1 0 = 0
  det : Matrix.GeneralLinearGroup.det.comp ρ = cycBar ℚ Ω l ^ (k - 1) * (φ * θ)
  away : ∀ A : ValuationSubring Ω, ¬ A.valuation (l : Ω) < 1 → ∀ g ∈ Ine (F := ℚ) A, φ g = 1 → θ g = 1 → ρ g = 1
  int : ∀ A, ‖x A‖ ≤ 1
  mem : ∀ E : IntermediateField ℚ_[l] (Qbar l), (∀ g i j, ρ g i j ∈ E) → ∀ A, x A ∈ E
  flag : ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ∀ s ∈ Dec (F := ℚ) A,
    ρ s 1 0 + ρ s 1 1 * x A = (ρ s 0 0 + ρ s 0 1 * x A) * x A
  ine : ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ∀ s ∈ Ine (F := ℚ) A,
    ρ s 0 0 + ρ s 0 1 * x A = (cycBar ℚ Ω l s ^ (k - 1) : (Qbar l)ˣ) ∧ ρ s 1 1 - x A * ρ s 0 1 = 1

private theorem near_trans {a b c : Qbar l} (h : ‖a - b‖ < 1) (h' : ‖b - c‖ < 1) : ‖a - c‖ < 1 := by
  have := IsUltrametricDist.norm_add_le_max (a - b) (b - c)
  rw [sub_add_sub_cancel] at this
  exact this.trans_lt (max_lt h h')

private theorem swap_basis {Γ k : Type} [Group Γ] [Field k] (ρ : Γ →* GL (Fin 2) k) :
    ∃ σ : Γ →* GL (Fin 2) k, RepIso ρ σ ∧ ∀ s, σ s 0 0 = ρ s 1 1 ∧ σ s 0 1 = ρ s 1 0 ∧ σ s 1 0 = ρ s 0 1 ∧ σ s 1 1 = ρ s 0 0 := by
  have e : (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) k) * !![0, 1; 1, 0] = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  let P : GL (Fin 2) k := ⟨!![0, 1; 1, 0], !![0, 1; 1, 0], e, e⟩
  refine ⟨(MulAut.conj P).toMonoidHom.comp ρ, ⟨P, fun s => rfl⟩, fun s => ?_⟩
  have h : ((((MulAut.conj P).toMonoidHom.comp ρ) s : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) =
      !![0, 1; 1, 0] * (ρ s : Matrix (Fin 2) (Fin 2) k) * !![0, 1; 1, 0] := rfl
  rw [h]
  simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]

private theorem cong_iff {c : Coef l} (a : c.Oˣ) :
    Cong (Units.map (algebraMap c.O (PadicAlgCl l)).toMonoidHom a) 1 ↔ residue c.O a = 1 := by
  rw [← map_one (residue c.O), ← sub_eq_zero, ← map_sub, residue_eq_zero_iff, (UpperTheory.V.Fr.sc_norm l c _).2]
  rfl

private theorem norm_unit {c : Coef l} (a : c.Oˣ) : ‖((a : c.O) : PadicAlgCl l)‖ = 1 := by
  refine le_antisymm (UpperTheory.V.Fr.sc_norm l c _).1 (not_lt.1 fun h => ?_)
  exact (mem_maximalIdeal _).1 ((UpperTheory.V.Fr.sc_norm l c _).2.2 h) a.isUnit

theorem exists_ribetLattice_of_eisensteinRep (ι : Qbar l ≃+* ℂ) (φ θ Φ : G ℚ Ω →* (Qbar l)ˣ) (k : ℕ) (hk : 1 ≤ k)
    (hΦ : Φ = cycBar ℚ Ω l ^ (k - 1) * φ) (ρ : G ℚ Ω →* GL (Fin 2) (Qbar l)) (hρ : EisRep ι φ θ k ρ)
    (hΦn : ∀ g, ‖(Φ g : Qbar l)‖ = 1)
    (hloc : ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ∃ s ∈ Dec (F := ℚ) A, ¬ Cong (Φ s) 1)
    (g0 : G ℚ Ω) (hg0 : ¬ Cong (Φ g0) 1) : ∃ ρ' x, RepIso ρ ρ' ∧ RibetLatticeEisensteinRep Φ φ θ k g0 ρ' x := by
  have hres : ResSum ρ ![1, Φ] := by rw [hΦ]; exact hρ.res
  obtain ⟨ρ₁, i1, d01, d10, r1, s₀, hs₀⟩ := UpperTheory.V.Sd.ribetLat l (G ℚ Ω) ρ 1 Φ hρ.cont hρ.irr
    (fun s => ⟨by simp, hΦn s⟩) hres g0
    (fun h => hg0 (by unfold Cong at h ⊢; rw [norm_sub_rev]; exact h))
  obtain ⟨σ, i2, hσ⟩ := swap_basis ρ₁
  have iso : RepIso ρ σ := by
    obtain ⟨a, ha⟩ := i1
    obtain ⟨b, hb⟩ := i2
    exact ⟨b * a, fun s => by rw [hb, ha]; group⟩
  have red : ∀ g, ‖σ g 0 0 - Φ g‖ < 1 ∧ ‖σ g 1 1 - 1‖ < 1 ∧ ‖σ g 0 1‖ < 1 ∧ ‖σ g 1 0‖ ≤ 1 := fun g => by
    obtain ⟨a, b, c, d⟩ := hσ g
    rw [a, b, c, d]
    exact ⟨(r1 g).2.1, (r1 g).1, (r1 g).2.2.1, (r1 g).2.2.2⟩
  have hx : ∀ A : ValuationSubring Ω, ∃ x : Qbar l, ‖x‖ ≤ 1 ∧ (¬ A.valuation (l : Ω) < 1 → x = 0) ∧
      (A.valuation (l : Ω) < 1 → (∀ s ∈ Dec (F := ℚ) A, σ s 1 0 + σ s 1 1 * x = (σ s 0 0 + σ s 0 1 * x) * x) ∧
        ∀ s ∈ Ine (F := ℚ) A, σ s 0 0 + σ s 0 1 * x = (cycBar ℚ Ω l s ^ (k - 1) : (Qbar l)ˣ) ∧ σ s 1 1 - x * σ s 0 1 = 1) := by
    intro A
    by_cases hA : A.valuation (l : Ω) < 1
    · obtain ⟨κ, k1, k2, k3⟩ := hρ.above A hA
      obtain ⟨x, x1, x2⟩ := UpperTheory.symmetric_cube_line_exists l (G ℚ Ω) (Dec (F := ℚ) A) σ Φ κ (fun g => ⟨(red g).2.1, (red g).2.2.2⟩)
        (k1.of_iso iso) (fun s => by rw [hΦ]; exact k3 0 s) (hloc A hA)
      refine ⟨x, x1, fun h => absurd hA h, fun _ => ⟨fun s hs => ?_, fun s hs => ?_⟩⟩
      · obtain ⟨a, b, -⟩ := x2 ⟨s, hs⟩
        exact b.trans (congrArg (· * x) a.symm)
      · obtain ⟨a, -, c⟩ := x2 ⟨s, hs.1⟩
        have e0 := k2 0 ⟨s, hs.1⟩ hs
        have e1 := k2 1 ⟨s, hs.1⟩ hs
        rw [e0] at a
        rw [e1] at c
        refine ⟨a.trans ?_, c.trans ?_⟩
        · have : ((k : ℤ) - 1) = ((k - 1 : ℕ) : ℤ) := by omega
          simp [this]
        · simp
    · exact ⟨0, by simp, fun _ => rfl, fun h => absurd h hA⟩
  choose x x1 x2 x3 using hx
  refine ⟨σ, x, iso, continuous_of_iso hρ.cont iso, red, ⟨s₀, by rw [(hσ s₀).2.2.1]; exact hs₀⟩,
    ⟨(hσ g0).2.1.trans d10, (hσ g0).2.2.1.trans d01⟩, ?_, fun A hA g hg h1 h2 => ?_, x1, fun E hE A => ?_,
    fun A hA => (x3 A hA).1, fun A hA => (x3 A hA).2⟩
  · rw [← hρ.det]
    obtain ⟨a, ha⟩ := iso
    ext s
    simp only [MonoidHom.comp_apply, ha, map_mul, map_inv, mul_inv_cancel_comm]
  · obtain ⟨a, ha⟩ := (hρ.away A hA).of_iso iso
    have e : a * σ g * a⁻¹ = 1 := by
      apply Units.ext
      rw [ha g hg, Units.val_one, ← Matrix.diagonal_one]
      congr 1
      funext i
      fin_cases i <;> simp [h1, h2]
    rw [mul_inv_eq_one, mul_eq_left] at e
    exact e
  · by_cases hA : A.valuation (l : Ω) < 1
    · obtain ⟨s, hs, hn⟩ := hloc A hA
      refine UpperTheory.symmetric_cube_root_mem l E _ _ _ _ _ (hE s 0 0) (hE s 0 1) (hE s 1 0) (hE s 1 1) (red s).2.2.1 ?_ (x1 A)
        ((x3 A hA).1 s hs)
      have a := (red s).1
      have d := (red s).2.1
      refine le_antisymm ?_ (not_lt.1 fun h => hn ?_)
      · have e : σ s 0 0 - σ s 1 1 = ((σ s 0 0 - Φ s) + Φ s) + (-(σ s 1 1 - 1) + -1) := by ring
        rw [e]
        refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_) <;>
          refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
        · exact a.le
        · exact (hΦn s).le
        · rw [norm_neg]; exact d.le
        · simp
      · rw [norm_sub_rev] at a
        exact near_trans (near_trans a h) d
    · rw [x2 A hA]
      exact E.zero_mem

end ModEx4

open ModEx4 in
theorem modEx4 : ModEx4 := by
  intro Ω _ _ _ l _ ι c D pr θ k hk ρ hρ hloc g0 hg0 c₀
  haveI : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  haveI : CompactSpace (G ℚ Ω) := inferInstanceAs (CompactSpace (Ω ≃ₐ[ℚ] Ω))
  have hT : ∀ g, ((toB (Phi D pr k) g : (Qbar l)ˣ) : Qbar l) =
      ((cycBar ℚ Ω l ^ (k - 1) * toB (phi D pr)) g : (Qbar l)ˣ) := fun g => by
    change (((Phi D pr k g : c.Oˣ) : c.O) : PadicAlgCl l) = _
    simp only [Phi, MonoidHom.mul_apply, MonoidHom.pow_apply, Units.val_mul, Units.val_pow_eq_pow_val, Subalgebra.coe_mul,
      Subalgebra.coe_pow]
    rfl
  have hTh : toB (Phi D pr k) = cycBar ℚ Ω l ^ (k - 1) * toB (phi D pr) := MonoidHom.ext fun g => Units.ext (hT g)
  have hbar : ∀ s, ¬ Cong (toB (Phi D pr k) s) 1 → Raw.bar (Phi D pr k) s ≠ 1 := fun s h e => h ((cong_iff _).2 e)
  obtain ⟨ρ', x, hiso, hB⟩ := exists_ribetLattice_of_eisensteinRep ι (toB (phi D pr)) θ (toB (Phi D pr k)) k hk hTh ρ hρ
    (fun g => norm_unit (Phi D pr k g))
    (fun A hA => by
      obtain ⟨s, hs, hn⟩ := hloc A hA
      exact ⟨s, hs, fun h => hn ((cong_iff _).1 h)⟩)
    g0 (fun h => hg0 ((cong_iff _).1 h))
  obtain ⟨E, hE, hmem⟩ := UpperTheory.V.Sd.finCoef l (G ℚ Ω) 2 ρ' hB.cont
  obtain ⟨hC1, hC2⟩ := UpperTheory.integrality_of_norm_coefficients l
  obtain ⟨c', hcc', hc0⟩ := (UpperTheory.V.HV.coefSup l).1 c c₀
  obtain ⟨c₁, h', hc₁⟩ := hC1 c' E hE
  have h : c.O ≤ c₁.O := hcc'.trans h'
  have hinc : ∀ y : c.O, ((inc h y : c₁.O) : PadicAlgCl l) = (y : PadicAlgCl l) := fun y => rfl
  have hchi : ∀ (c' : Coef l) g, ((chiO ℚ Ω l c'.O g : c'.O) : PadicAlgCl l) = (cycBar ℚ Ω l g : Qbar l) := fun c' g => rfl
  have hint : ∀ g i j, ‖ρ' g i j‖ ≤ 1 := by
    intro g i j
    obtain ⟨h0, h1, h2, h3⟩ := hB.red g
    fin_cases i <;> fin_cases j
    · have e : ρ' g 0 0 = (ρ' g 0 0 - toB (Phi D pr k) g) + toB (Phi D pr k) g := by ring
      show ‖ρ' g 0 0‖ ≤ 1
      rw [e]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h0.le (UpperTheory.V.Fr.sc_norm l c (Phi D pr k g)).1)
    · exact h2.le
    · exact h3
    · have e : ρ' g 1 1 = (ρ' g 1 1 - 1) + 1 := by ring
      show ‖ρ' g 1 1‖ ≤ 1
      rw [e]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1.le norm_one.le)
  have hO : ∀ g i j, ρ' g i j ∈ c₁.O := fun g i j => hc₁ _ (hmem g i j) (hint g i j)
  let ρ₁ : G ℚ Ω →* M2 c₁.O :=
    { toFun := fun g => Matrix.of fun i j => ⟨ρ' g i j, hO g i j⟩
      map_one' := by
        ext i j
        simp only [Matrix.of_apply, map_one, Units.val_one, Matrix.one_apply]
        split_ifs <;> rfl
      map_mul' := by
        intro g g'
        ext i j
        simp [Matrix.mul_apply, Fin.sum_univ_two] }
  have hρ₁ : ∀ g i j, ((ρ₁ g i j : c₁.O) : PadicAlgCl l) = ρ' g i j := fun g i j => rfl
  let x₁ : ValuationSubring Ω → c₁.O := fun A => ⟨x A, hc₁ _ (hB.mem E hmem A) (hB.int A)⟩
  have hm : ∀ y : c₁.O, y ∈ maximalIdeal c₁.O ↔ ‖(y : PadicAlgCl l)‖ < 1 := fun y => (UpperTheory.V.Fr.sc_norm l c₁ y).2
  refine ⟨c₁, h, ρ₁, x₁, hc0.trans h', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨P, hP⟩ := hiso
    refine ⟨P, fun s => ?_⟩
    rw [← hP]
    exact Units.ext (Matrix.ext fun i j => rfl)
  · intro i j
    rw [hC2]
    exact (Units.continuous_val.comp hB.cont).matrix_elem i j
  · intro g
    obtain ⟨h0, h1, h2, -⟩ := hB.red g
    exact ⟨(hm _).2 h0, (hm _).2 h1, (hm _).2 h2⟩
  · obtain ⟨g, hg⟩ := hB.ne
    exact ⟨g, fun hh => ((hm _).1 hh).ne hg⟩
  · exact ⟨Subtype.ext hB.nrm.1, Subtype.ext hB.nrm.2⟩
  · intro g hg
    have e := congrArg Units.val (DFunLike.congr_fun hB.det g)
    have e2 := hT g
    simp only [MonoidHom.comp_apply, MonoidHom.mul_apply, MonoidHom.pow_apply, hg, mul_one, Units.val_mul,
      Units.val_pow_eq_pow_val, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two] at e e2
    apply Subtype.ext
    rw [hinc, Matrix.det_fin_two]
    simp only [Subalgebra.coe_mul, Subalgebra.coe_sub, hρ₁]
    exact e.trans e2.symm
  · intro A hA g hg h1 h2
    have e := hB.away A hA g hg (by simp [toB, h1]) h2
    ext i j
    rw [hρ₁, e]
    simp only [Units.val_one, Matrix.one_apply]
    split_ifs <;> rfl
  · intro A hA s hs
    exact Subtype.ext (hB.flag A hA s hs)
  · intro A hA s hs
    obtain ⟨h1, h2⟩ := hB.ine A hA s hs
    refine ⟨Subtype.ext ?_, Subtype.ext h2⟩
    simp only [Units.val_pow_eq_pow_val, Subalgebra.coe_pow, hchi] at h1 ⊢
    exact h1

end UpperTheory.V.Cu2

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.FiniteOrderCongruences.ExistsWeightFourAuxiliaryCharacters
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N IsLocalRing Polynomial
open UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S3
open UpperTheory.V.Cu
open scoped Matrix

namespace UpperTheory.V.Cu2

private theorem cls_one {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (N : ℕ) [NeZero N] (s : G ℚ Ω)
    (hs : ∀ ζ : Ω, ζ ^ N = 1 → s ζ = ζ) : UpperTheory.V.Chr.cls ℚ Ω N s = 1 := by
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω N
  have h := UpperTheory.V.Chr.cls_spec N s ζ hζ.pow_eq_one
  rw [hs ζ hζ.pow_eq_one] at h
  have h2 : ζ ^ ((UpperTheory.V.Chr.cls ℚ Ω N s : (ZMod N)ˣ) : ZMod N).val = ζ ^ (1 : ZMod N).val := by
    rw [← h, ZMod.val_one_eq_one_mod, ← pow_eq_pow_mod 1 hζ.pow_eq_one, pow_one]
  exact Units.ext (ZMod.val_injective N (hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) h2))

private theorem comm_le {Γ M : Type} [Group Γ] [Monoid M] (f : Γ →* M) (h : ∀ a b, f a * f b = f b * f a) :
    commutator Γ ≤ f.ker := by
  rw [commutator_def, Subgroup.commutator_le]
  intro a _ b _
  rw [MonoidHom.mem_ker, commutatorElement_def, map_mul, map_mul, map_mul, h a b, mul_assoc (f b), ← map_mul, mul_inv_cancel,
    map_one, mul_one, ← map_mul, mul_inv_cancel, map_one]

private theorem odd_one {M : Type} [Monoid M] (x : M) {m : ℕ} (hm : Odd m) (h2 : x ^ 2 = 1) (hm1 : x ^ m = 1) : x = 1 := by
  obtain ⟨j, rfl⟩ := hm
  rw [pow_succ, pow_mul, h2, one_pow, one_mul] at hm1
  exact hm1

section

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}

private theorem psi_level (D : Raw Ω c) (h3 : Ctx3 D) : ∃ N : ℕ, 0 < N ∧ ¬ l ∣ N ∧ KillsMu N D.ψ := by
  obtain ⟨hG, h, t, e, ψ, hB, he0, het, hX, ⟨c1, c2, c3, c4⟩, he, hψ, -⟩ := h3
  have hlp : l.Prime := Fact.out
  obtain ⟨-, -, -, -, hb⟩ := bchiFacts h t hB
  obtain ⟨-, -, -, -, -, -, -, n3⟩ := hb l hlp hG.l_odd c1
  obtain ⟨-, -, n4⟩ := n3 e he0 het c2
  refine ⟨h.N, h.N_pos, n4, fun s hs => ?_⟩
  rw [hψ, UpperTheory.V.Chr.dirG, MonoidHom.comp_apply, cls_one h.N s hs, map_one]

private theorem e_even (D : Raw Ω c) (h3 : Ctx3 D) : Even D.e := by
  obtain ⟨-, h, t, e, ψ, -, -, -, hX, ⟨-, -, c3, -⟩, he, -⟩ := h3
  have hev : ψ (-1) = (-1) ^ e := (h.mem_X.1 hX).2
  have h1 : ψ (-1) = 1 := by
    refine odd_one _ c3 ?_ ?_
    · rw [sq, ← map_mul, neg_one_mul, neg_neg, map_one]
    · rw [← MulChar.pow_apply' ψ c3.pos.ne', pow_orderOf_eq_one, MulChar.one_apply isUnit_one.neg]
  rw [h1] at hev
  have hne : (-1 : c.O) ≠ 1 := by
    intro h0
    have h' : ((-1 : c.O) : PadicAlgCl l) = ((1 : c.O) : PadicAlgCl l) := congrArg _ h0
    have h'' : (algebraMap ℚ_[l] (PadicAlgCl l)) (-1) = (algebraMap ℚ_[l] (PadicAlgCl l)) 1 := by
      rw [map_neg, map_one]
      simpa using h'
    have h4 := (algebraMap ℚ_[l] (PadicAlgCl l)).injective h''
    norm_num at h4
  rw [he]
  exact (neg_one_pow_eq_one_iff_even hne).1 hev.symm

private theorem cc_sq {cc : G ℚ Ω} (h : ReciprocityTheory.Gal.IsCC cc) : cc * cc = 1 := by
  obtain ⟨j, hj⟩ := h
  ext x
  apply j.injective
  rw [AlgEquiv.mul_apply, hj, hj, Complex.conj_conj, AlgEquiv.one_apply]

private theorem bar_mul (γ δ : G ℚ Ω →* c.Oˣ) (g : G ℚ Ω) : Raw.bar (γ * δ) g = Raw.bar γ g * Raw.bar δ g := by
  simp only [Raw.bar, MonoidHom.mul_apply, Units.val_mul, map_mul]

private theorem bar_inv (γ : G ℚ Ω →* c.Oˣ) (g : G ℚ Ω) : Raw.bar γ⁻¹ g = (Raw.bar γ g)⁻¹ := by
  simp only [Raw.bar, MonoidHom.inv_apply]
  exact map_units_inv (residue c.O) (γ g)

private theorem bar_pow (γ : G ℚ Ω →* c.Oˣ) (n : ℕ) (g : G ℚ Ω) : Raw.bar (γ ^ n) g = Raw.bar γ g ^ n := by
  simp only [Raw.bar, MonoidHom.pow_apply, Units.val_pow_eq_pow_val, map_pow]

private theorem bar_zpow (γ : G ℚ Ω →* c.Oˣ) (n : ℕ) (g : G ℚ Ω) : Raw.bar (γ ^ (n : ℤ)) g = Raw.bar γ g ^ n := by
  rw [zpow_natCast, bar_pow]

private theorem bar_one (g : G ℚ Ω) : Raw.bar (1 : G ℚ Ω →* c.Oˣ) g = 1 := by
  simp only [Raw.bar, MonoidHom.one_apply, Units.val_one, map_one]

private theorem bar_ne (γ : G ℚ Ω →* c.Oˣ) (g : G ℚ Ω) : Raw.bar γ g ≠ 0 :=
  ((γ g).isUnit.map (residue c.O)).ne_zero

private theorem bar_conj (γ : G ℚ Ω →* c.Oˣ) (u s : G ℚ Ω) : Raw.bar γ (u⁻¹ * s * u) = Raw.bar γ s := by
  have h : γ (u⁻¹ * s * u) = γ s := by
    rw [map_mul, map_mul, map_inv, mul_right_comm, inv_mul_cancel, one_mul]
  simp only [Raw.bar, h]

private theorem bar_Phi (D : Raw Ω c) (hG : D.Good) (hd : l - 1 ∣ 2 * D.e) (pr : Bool) (k : ℕ)
    (hk : k - 1 ≡ D.e [MOD l - 1]) : ∃ i : ℤ, ∀ g, Raw.bar (Phi D pr k) g = Raw.bar (D.ξ * D.Psi ^ i) g ∧
      Raw.bar (chi D pr 0) g * (Raw.bar (chi D pr 3) g)⁻¹ = Raw.bar (D.ξ * D.Psi ^ i) g := by
  have key : ∀ g, Raw.bar (chiO ℚ Ω l c.O) g = Raw.bar D.om g ∧ Raw.bar D.om g ^ (k - 1) = Raw.bar D.om g ^ D.e ∧
      Raw.bar D.om g ^ D.e * Raw.bar D.om g ^ D.e = 1 ∧ Raw.bar D.om g ≠ 0 := by
    intro g
    have hu : Raw.bar D.om g ^ (l - 1) = 1 := by rw [← bar_pow, hG.om_pow, bar_one]
    refine ⟨(hG.om_bar g).symm, ?_, ?_, bar_ne _ _⟩
    · rw [pow_eq_pow_mod (k - 1) hu, show (k - 1) % (l - 1) = D.e % (l - 1) from hk, ← pow_eq_pow_mod D.e hu]
    · obtain ⟨q, hq⟩ := hd
      rw [← pow_add, ← two_mul, hq, pow_mul, hu, one_pow]
  have eP : D.Psi = chiO ℚ Ω l c.O ^ (D.e : ℤ) * D.ψ := rfl
  cases pr
  · refine ⟨1, fun g => ?_⟩
    obtain ⟨hcu, hue, -, hu0⟩ := key g
    have e0 : chi D false 0 = chiO ℚ Ω l c.O * D.om⁻¹ * D.ξ * D.Psi := rfl
    have e3 : chi D false 3 = 1 := rfl
    have ep : Phi D false k = chiO ℚ Ω l c.O ^ (k - 1) * (D.ξ * D.ψ) := rfl
    rw [ep, e0, e3, zpow_one, eP]
    simp only [bar_mul, bar_inv, bar_pow, bar_zpow, bar_one, hcu, hue]
    constructor
    · ring
    · rw [mul_inv_cancel₀ hu0, one_mul, inv_one, mul_one]
  · refine ⟨-1, fun g => ?_⟩
    obtain ⟨hcu, hue, hu2, hu0⟩ := key g
    have hinv : (Raw.bar D.om g ^ D.e)⁻¹ = Raw.bar D.om g ^ D.e := inv_eq_of_mul_eq_one_right hu2
    have e0 : chi D true 0 = chiO ℚ Ω l c.O * D.om⁻¹ * D.ξ := rfl
    have e3 : chi D true 3 = D.Psi := rfl
    have ep : Phi D true k = chiO ℚ Ω l c.O ^ (k - 1) * (D.ξ * D.ψ⁻¹) := rfl
    rw [ep, e0, e3, zpow_neg_one, eP]
    simp only [bar_mul, bar_inv, bar_pow, bar_zpow, bar_one, hcu, hue]
    constructor
    · rw [mul_inv, hinv]
      ring
    · rw [mul_inv_cancel₀ hu0, one_mul]

end

theorem exists_weight_four_auxiliary_characters : ExistsSplittingAuxiliaryCharacterForTower := by
  intro Ω _ _ _ l hl c D T h3 _
  have hG := h3.1
  obtain ⟨N, hN, hlN, hKB⟩ : ∃ N : ℕ, 0 < N ∧ ¬ l ∣ N ∧ KillsMu N (toB (phi D T.pr)) := by
    obtain ⟨N₁, hN₁, hlN₁, hK₁⟩ := UpperTheory.cyclotomicChar_pow_N_trivial Ω l c D h3
    obtain ⟨N₂, hN₂, hlN₂, hK₂⟩ := psi_level D h3
    refine ⟨N₁ * N₂, Nat.mul_pos hN₁ hN₂, fun hd => (hl.out.dvd_mul.1 hd).elim hlN₁ hlN₂, fun s hs => ?_⟩
    have h1 : D.ξ s = 1 := hK₁ s fun ζ hζ => hs ζ (by rw [pow_mul, hζ, one_pow])
    have h2 : D.ψ s = 1 := hK₂ s fun ζ hζ => hs ζ (by rw [mul_comm, pow_mul, hζ, one_pow])
    unfold phi
    split <;> simp [toB, h1, h2]
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, ho1, ho2, -⟩ := UpperTheory.V.GradeZeroInterpolatingElement.facts D hG
  have ho0 : IsOpen (T.F.fixingSubgroup : Set (G ℚ Ω)) := IntermediateField.fixingSubgroup_isOpen T.F
  have hc0 : commutator (G ℚ Ω) ≤ T.F.fixingSubgroup := by
    have hn := T.abF.toIsGalois.to_normal
    rw [← @IntermediateField.restrictNormalHom_ker ℚ Ω _ _ _ T.F hn]
    exact comm_le _ fun a b => T.abF.toIsMulCommutative.is_comm.comm _ _
  have hc1 : commutator (G ℚ Ω) ≤ D.rbar.ker := comm_le _ fun a b => by
    rw [← map_mul, ← map_mul]
    ext i j
    simp [Raw.rbar, Raw.r0, diagRep, GradeZeroInterpolatingElement.mapRep, Matrix.diagonal_apply, mul_comm]
  have hc2 : commutator (G ℚ Ω) ≤ D.om.ker := comm_le _ fun a b => mul_comm _ _
  obtain ⟨w, hw, hlt, hmod, hs⟩ := UpperTheory.exists_splitPrime_cmDatum Ω (T.F.fixingSubgroup ⊓ D.rbar.ker ⊓ D.om.ker)
    ((ho0.inter ho1).inter ho2) (le_inf (le_inf hc0 hc1) hc2) (N * l) (Nat.mul_pos hN hl.out.pos)
  obtain ⟨θ, t1, t2, t3⟩ := UpperTheory.exists_theta_character_cmDatum Ω l w hw (hmod.of_mul_left N)
  refine ⟨N, w, θ, ⟨hG.l_odd, hN, hlN, hw, fun hd => ?_, t1, t2, t3⟩, ⟨hKB, fun s hs => hKB s fun ζ hζ => ?_⟩, hs⟩
  · have h1 := Nat.le_of_dvd hN hd
    have h2 := Nat.le_mul_of_pos_right N hl.out.pos
    omega
  · have h1 : w % N = 1 % N := hmod.of_mul_right l
    rw [hs ζ hζ, pow_eq_pow_mod w hζ, h1, ← pow_eq_pow_mod 1 hζ, pow_one]

theorem phiFacts : PhiFacts := by
  intro Ω _ _ _ l hl c D T h3 hok h4
  have hG := h3.1
  obtain ⟨-, hd, -, ⟨m, hm, -, hψm⟩, -⟩ := large₂.host3 D h3
  refine ⟨?_, e_even D h3, fun k hk1 hk => ?_⟩
  · have hcc : D.cc * D.cc = 1 := cc_sq hG.isCC
    have hψ : D.ψ D.cc = 1 := odd_one (D.ψ D.cc) hm (by rw [sq, ← map_mul, hcc, map_one])
      (by rw [← MonoidHom.pow_apply, hψm, MonoidHom.one_apply])
    unfold phi
    split <;> simp [hG.xi_odd, hψ]
  · obtain ⟨i, hi⟩ := bar_Phi D hG hd T.pr k hk
    refine ⟨?_, fun A hA => ?_⟩
    · intro hsq
      have hq := (hi (resQ T.F T.g0)).1.trans (hi (resQ T.F T.g0)).2.symm
      obtain ⟨K', _, hQ⟩ := h4.quad
      have hη : T.rb wAl T.g0 = Raw.bar (chi D T.pr 0) (resQ T.F T.g0) * (Raw.bar (chi D T.pr 1) (resQ T.F T.g0))⁻¹ := by
        have h0 : (T.fr ∅).rt wAl T.g0 = chi D T.pr 0 (resQ T.F T.g0) * (chi D T.pr 1 (resQ T.F T.g0))⁻¹ := by
          show (chi D T.pr 0 (resQ T.F T.g0) * (chi D T.pr 1 (resQ T.F T.g0))⁻¹) ^ (1 : ℤ) *
            (chi D T.pr 0 (resQ T.F T.g0) * (chi D T.pr 2 (resQ T.F T.g0))⁻¹) ^ (0 : ℤ) = _
          rw [zpow_one, zpow_zero, mul_one]
        show residue c.O (((T.fr ∅).rt wAl T.g0 : c.Oˣ) : c.O) = _
        rw [h0, Units.val_mul, map_mul, map_units_inv]
      have hη2 : T.rb wAl T.g0 = 1 ∨ T.rb wAl T.g0 = -1 := by
        by_cases hmem : resQ T.F T.g0 ∈ K'.fixingSubgroup
        · exact Or.inl (hQ.on _ hmem)
        · exact Or.inr (hQ.off _ hmem)
      have h1 := bar_ne (chi D T.pr 1) (resQ T.F T.g0)
      have h3' := bar_ne (chi D T.pr 3) (resQ T.F T.g0)
      rw [hq] at hsq
      rw [hη] at hη2
      rcases mul_self_eq_one_iff.1 ((sq _).symm.trans hsq) with ha | ha
      · exact hok.dist 0 3 (by decide) ((mul_inv_eq_one₀ h3').1 ha)
      · rcases hη2 with hb | hb
        · exact hok.dist 0 1 (by decide) ((mul_inv_eq_one₀ h1).1 hb)
        · apply hok.dist 1 3 (by decide)
          rw [mul_inv_eq_iff_eq_mul₀ h3'] at ha
          rw [mul_inv_eq_iff_eq_mul₀ h1] at hb
          linear_combination hb - ha
    · have hT : l ∈ D.T := Finset.mem_insert_self _ _
      obtain ⟨u, hu, -⟩ := (UpperTheory.V.Chr.placesQ Ω).2.2 l _ A hl.out (hG.pl_over l hl.out) hA
      exact ⟨_, hu _ (hG.sg_frob l hT).1, fun e =>
        hG.condD l hT i (((hi _).1).symm.trans ((bar_conj _ u _).symm.trans e))⟩

end UpperTheory.V.Cu2

end
end

