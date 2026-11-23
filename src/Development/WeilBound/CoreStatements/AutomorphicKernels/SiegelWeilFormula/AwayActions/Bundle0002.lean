module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AwayActions.FinBase
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockSpaces.VolumeIsAddHaar
public import Development.WeilBound.ThetaLifts.SmallCones.IdeleTop

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AwayActions.FinSteps
section
noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)

namespace PositivityTheory.SiegelWeilFormula.KAway

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

namespace SDf

variable (d : SD σ)

theorem stepN (hT : TAll) (x : d.G) (β : Mx F E d.n d.n) (hx : inFrame d.b x = Matrix.fromBlocks 1 β 0 1)
    (hβ : eInf F • β = 0) :
    StepF d x id (fun G X => d.B.ψ (-(⅟(2 : AF F) * d.tt (β * d.gram X X))) * G X) := by
  have hβf : finOne F • β = β := by
    have h := smul_split (F := F) β
    rw [hβ, zero_add] at h
    exact h
  have hq : ∀ X Z : Mx F E d.m d.n, finOne F • Z = 0 → β * d.gram (X + Z) (X + Z) = β * d.gram X X := by
    intro X Z hZ
    have hZe : eInf F • Z = Z := by
      have h := smul_split (F := F) Z
      rw [hZ, add_zero] at h
      exact h
    have h1 : β * d.gram X Z = 0 := by
      rw [← hZe, gram_smul_right, ← hβf, Matrix.smul_mul, Matrix.mul_smul, smul_smul, finOne_mul_eInf,
        zero_smul]
    have h2 : β * d.gram Z X = 0 := by
      rw [← hZe, gram_smul_left, Matrix.mul_smul, ← hβf, Matrix.smul_mul, smul_smul, eInf_mul_finOne,
        zero_smul]
    have h3 : β * d.gram Z Z = 0 := by
      rw [← hZe, gram_smul_left, Matrix.mul_smul, ← hβf, Matrix.smul_mul, smul_smul, eInf_mul_finOne,
        zero_smul]
    simp only [gram_add_left, gram_add_right, Matrix.mul_add, h1, h2, h3, add_zero]
  refine ⟨fun f hf => hf, fun G hG => ⟨?_, ?_⟩⟩
  · intro X Z hZ
    show d.B.ψ (-(⅟(2 : AF F) * d.tt (β * d.gram (X + Z) (X + Z)))) * G (X + Z) =
      d.B.ψ (-(⅟(2 : AF F) * d.tt (β * d.gram X X))) * G X
    rw [hq X Z hZ, hG X Z hZ]
  · intro f hf Φ hΦ hTΦ
    funext X
    rw [(hT.2.1 F E σ d Φ hΦ).1 x β hx X, hTΦ]
    simp only [id]
    ring

theorem stepM (hT : TAll) (x : d.G) (a a' : GL (Fin d.n) (AE F E))
    (hx : inFrame d.b x = Matrix.fromBlocks a.1 0 0 a'.1) (ha : eInf F • a'.1 = eInf F • (1 : Mx F E d.n d.n)) :
    ∃ B, StepF d x id B := by
  have hinv : eInf F • ((a'⁻¹ : GL (Fin d.n) (AE F E)) : Matrix (Fin d.n) (Fin d.n) (AE F E))ᵀ =
      eInf F • (1 : Matrix (Fin d.n) (Fin d.n) (AE F E)) := by
    have h1 : eInf F • ((a'⁻¹ : GL (Fin d.n) (AE F E)) : Matrix (Fin d.n) (Fin d.n) (AE F E)) =
        eInf F • (1 : Matrix (Fin d.n) (Fin d.n) (AE F E)) := by
      calc eInf F • ((a'⁻¹ : GL (Fin d.n) (AE F E)) : Matrix (Fin d.n) (Fin d.n) (AE F E))
          = (eInf F • (1 : Matrix (Fin d.n) (Fin d.n) (AE F E))) *
              ((a'⁻¹ : GL (Fin d.n) (AE F E)) : Matrix (Fin d.n) (Fin d.n) (AE F E)) := by
            rw [Matrix.smul_mul, Matrix.one_mul]
        _ = (eInf F • a'.1) * ((a'⁻¹ : GL (Fin d.n) (AE F E)) : Matrix (Fin d.n) (Fin d.n) (AE F E)) := by
            rw [ha]
        _ = eInf F • (a'.1 * ((a'⁻¹ : GL (Fin d.n) (AE F E)) : Matrix (Fin d.n) (Fin d.n) (AE F E))) := by
            rw [Matrix.smul_mul]
        _ = eInf F • (1 : Matrix (Fin d.n) (Fin d.n) (AE F E)) := by
            rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [← Matrix.transpose_smul, h1, Matrix.transpose_smul, Matrix.transpose_one]
  obtain ⟨c, hc⟩ : ∃ c : ℂ, ∀ Φ ∈ d.sch, ∀ X : Mx F E d.m d.n, d.T (d.om x Φ) X =
      c * d.T Φ (X * ((a'⁻¹ : GL (Fin d.n) (AE F E)) : Matrix (Fin d.n) (Fin d.n) (AE F E))ᵀ) :=
    ⟨_, fun Φ hΦ X => (hT.2.1 F E σ d Φ hΦ).2.1 x a a' hx X⟩
  refine ⟨fun G X => c * G (X * ((a'⁻¹ : GL (Fin d.n) (AE F E)) : Matrix (Fin d.n) (Fin d.n) (AE F E))ᵀ),
    fun f hf => hf, fun G hG => ⟨?_, ?_⟩⟩
  · intro X Z hZ
    show c * G ((X + Z) * ((a'⁻¹ : GL (Fin d.n) (AE F E)) : Matrix (Fin d.n) (Fin d.n) (AE F E))ᵀ) =
      c * G (X * ((a'⁻¹ : GL (Fin d.n) (AE F E)) : Matrix (Fin d.n) (Fin d.n) (AE F E))ᵀ)
    rw [Matrix.add_mul, hG _ _ (by rw [← Matrix.smul_mul, hZ, Matrix.zero_mul])]
  · intro f hf Φ hΦ hTΦ
    funext X
    have hfX : f (X * ((a'⁻¹ : GL (Fin d.n) (AE F E)) : Matrix (Fin d.n) (Fin d.n) (AE F E))ᵀ) = f X := by
      have e1 : X * ((a'⁻¹ : GL (Fin d.n) (AE F E)) : Matrix (Fin d.n) (Fin d.n) (AE F E))ᵀ - X =
          X * (((a'⁻¹ : GL (Fin d.n) (AE F E)) : Matrix (Fin d.n) (Fin d.n) (AE F E))ᵀ - 1) := by
        rw [Matrix.mul_sub, Matrix.mul_one]
      have h0 : eInf F • (X * ((a'⁻¹ : GL (Fin d.n) (AE F E)) : Matrix (Fin d.n) (Fin d.n) (AE F E))ᵀ - X) = 0 := by
        rw [e1, ← Matrix.mul_smul, smul_sub, hinv, sub_self, Matrix.mul_zero]
      have := hf X _ ((cw_zero_iff d _).2 h0)
      rwa [add_sub_cancel] at this
    rw [hc Φ hΦ X, hTΦ]
    simp only [id]
    rw [hfX]
    ring

end SDf

end PositivityTheory.SiegelWeilFormula.KAway

end
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AwayActions.StepW
section
noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KAway

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

namespace SDf

variable (d : SD σ)

theorem stepW (hT : TAll) (hA : AuxiliaryPrimeFunction) (ε : ℤˣ) (w : d.G) (hw : d.IsW ε w) : ∃ A B, StepF d w A B := by
  obtain ⟨⟨ν, hν⟩, -, -⟩ := hA F E σ d
  have := hν.1
  obtain ⟨i1, i2, i3, i4⟩ := (PositivityTheory.ThKCT.ideleTop F E).1
  haveI : BorelSpace (AE F E) := ⟨rfl⟩
  haveI : IsTopologicalAddGroup (Mx F E d.m d.n) := inferInstanceAs (IsTopologicalAddGroup (Fin d.m → Fin d.n → AE F E))
  haveI : LocallyCompactSpace (Mx F E d.m d.n) := inferInstanceAs (LocallyCompactSpace (Fin d.m → Fin d.n → AE F E))
  haveI : SecondCountableTopology (Mx F E d.m d.n) :=
    inferInstanceAs (SecondCountableTopology (Fin d.m → Fin d.n → AE F E))
  haveI : BorelSpace (Mx F E d.m d.n) := inferInstanceAs (BorelSpace (Fin d.m → Fin d.n → AE F E))
  have hsm : ∀ c : AF F, Continuous fun Z : Mx F E d.m d.n => c • Z := fun c =>
    continuous_pi fun i => continuous_pi fun j =>
      Continuous.fun_smul (f := fun _ : Mx F E d.m d.n => c) (g := fun Z : Mx F E d.m d.n => Z i j) continuous_const
        ((continuous_apply j).comp (continuous_apply i))
  let VI : AddSubgroup (Mx F E d.m d.n) :=
    { carrier := {Z | finOne F • Z = 0}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at *
        rw [smul_add, ha, hb, add_zero]
      zero_mem' := by simp
      neg_mem' := fun {a} ha => by
        simp only [Set.mem_setOf_eq] at *
        rw [smul_neg, ha, neg_zero] }
  let VF : AddSubgroup (Mx F E d.m d.n) :=
    { carrier := {Z | eInf F • Z = 0}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at *
        rw [smul_add, ha, hb, add_zero]
      zero_mem' := by simp
      neg_mem' := fun {a} ha => by
        simp only [Set.mem_setOf_eq] at *
        rw [smul_neg, ha, neg_zero] }
  have hVI : IsClosed ((VI : AddSubgroup (Mx F E d.m d.n)) : Set (Mx F E d.m d.n)) :=
    isClosed_eq (hsm (finOne F)) continuous_const
  have hVF : IsClosed ((VF : AddSubgroup (Mx F E d.m d.n)) : Set (Mx F E d.m d.n)) :=
    isClosed_eq (hsm (eInf F)) continuous_const
  haveI : LocallyCompactSpace VI := hVI.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : LocallyCompactSpace VF := hVF.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology VI :=
    TopologicalSpace.Subtype.secondCountableTopology ((VI : AddSubgroup (Mx F E d.m d.n)) : Set (Mx F E d.m d.n))
  haveI : SecondCountableTopology VF :=
    TopologicalSpace.Subtype.secondCountableTopology ((VF : AddSubgroup (Mx F E d.m d.n)) : Set (Mx F E d.m d.n))
  haveI : BorelSpace VI := Subtype.borelSpace (fun x' => x' ∈ ((VI : AddSubgroup (Mx F E d.m d.n)) : Set (Mx F E d.m d.n)))
  haveI : BorelSpace VF := Subtype.borelSpace (fun x' => x' ∈ ((VF : AddSubgroup (Mx F E d.m d.n)) : Set (Mx F E d.m d.n)))
  have h₁ : ∀ Z : Mx F E d.m d.n, eInf F • Z ∈ VI := fun Z => by
    show finOne F • eInf F • Z = 0
    rw [smul_smul, finOne_mul_eInf, zero_smul]
  have h₂ : ∀ Z : Mx F E d.m d.n, finOne F • Z ∈ VF := fun Z => by
    show eInf F • finOne F • Z = 0
    rw [smul_smul, eInf_mul_finOne, zero_smul]
  let Φs : VI × VF ≃ₜ+ Mx F E d.m d.n :=
    { toFun := fun p => p.1.1 + p.2.1
      invFun := fun Z => (⟨eInf F • Z, h₁ Z⟩, ⟨finOne F • Z, h₂ Z⟩)
      left_inv := fun p => by
        obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := p
        have ha' : finOne F • a = 0 := ha
        have hb' : eInf F • b = 0 := hb
        have ea : eInf F • a = a := by
          conv_rhs => rw [← smul_split a]
          rw [ha', add_zero]
        have eb : finOne F • b = b := by
          conv_rhs => rw [← smul_split b]
          rw [hb', zero_add]
        refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
        · show eInf F • (a + b) = a
          rw [smul_add, ea, hb', add_zero]
        · show finOne F • (a + b) = b
          rw [smul_add, eb, ha', zero_add]
      right_inv := fun Z => smul_split Z
      map_add' := fun p q => by
        show p.1.1 + q.1.1 + (p.2.1 + q.2.1) = p.1.1 + p.2.1 + (q.1.1 + q.2.1)
        abel
      continuous_toFun := (continuous_subtype_val.comp continuous_fst).add (continuous_subtype_val.comp continuous_snd)
      continuous_invFun := ((hsm (eInf F)).subtype_mk h₁).prodMk ((hsm (finOne F)).subtype_mk h₂) }
  obtain ⟨C, -, hC⟩ := KFock.integral_split ν (Measure.addHaar : Measure VI) (Measure.addHaar : Measure VF) Φs
  refine ⟨fun f X => (C : ℂ) * ∫ a : VI, d.B.ψ (((ε : ℤ) : AF F) * d.tt (d.gram X a.1)) * f a.1 ∂Measure.addHaar,
    fun G X => ∫ b : VF, d.B.ψ (((ε : ℤ) : AF F) * d.tt (d.gram X b.1)) * G b.1 ∂Measure.addHaar, fun f hf => ?_,
    fun G hG => ⟨?_, fun f hf Φ hΦ hTΦ => ?_⟩⟩
  · intro X Z hZ
    have hZ' := (cw_zero_iff d Z).1 hZ
    dsimp only
    congr 2
    funext a
    rw [gram_add_left, gram_fin_inf d hZ' a.2, add_zero]
  · intro X Z hZ
    dsimp only
    congr 1
    funext b
    rw [gram_add_left, gram_inf_fin d hZ b.2, add_zero]
  · funext X
    rw [(hT.2.2.1 F E σ d) ν hν ε w hw Φ hΦ X, hTΦ, hC]
    have hpt : ∀ p : VI × VF, d.B.ψ (((ε : ℤ) : AF F) * d.tt (d.gram X (Φs p))) * (f (Φs p) * G (Φs p)) =
        (d.B.ψ (((ε : ℤ) : AF F) * d.tt (d.gram X p.1.1)) * f p.1.1) * (d.B.ψ (((ε : ℤ) : AF F) * d.tt (d.gram X p.2.1)) * G p.2.1) := by
      intro p
      have e1 : Φs p = p.1.1 + p.2.1 := rfl
      have hf' : f (p.1.1 + p.2.1) = f p.1.1 := hf p.1.1 p.2.1 ((cw_zero_iff d _).2 p.2.2)
      have hG' : G (p.1.1 + p.2.1) = G p.2.1 := by rw [add_comm]; exact hG p.2.1 p.1.1 p.1.2
      rw [e1, hf', hG', gram_add_right, tt_add, mul_add, AddChar.map_add_eq_mul]
      ring
    simp only [hpt]
    rw [integral_prod_mul (μ := (Measure.addHaar : Measure VI)) (ν := (Measure.addHaar : Measure VF))
      (fun a : VI => d.B.ψ (((ε : ℤ) : AF F) * d.tt (d.gram X a.1)) * f a.1)
      (fun b : VF => d.B.ψ (((ε : ℤ) : AF F) * d.tt (d.gram X b.1)) * G b.1)]
    ring

end SDf

end PositivityTheory.SiegelWeilFormula.KAway

end
end

