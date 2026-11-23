module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.Bundle0003
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.Bundle0003
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.Bundle0001

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.HBlock
section
noncomputable section

namespace PIW.MassDataColumns

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.TypedSets Formalism.L2.SG.Measures Formalism.L2.SG.Sub
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain Formalism.FourierDecayAlt.S3
open scoped Matrix

section GlobalTheory

variable {A : Type} [CommRing A] (r k : ℕ)

def hEmbGL : GL (Fin k) A →* GL (Idx r k) A where
  toFun g := ⟨hEmb r (g : Matrix (Fin k) (Fin k) A), hEmb r ((g⁻¹ : GL (Fin k) A) : Matrix (Fin k) (Fin k) A),
    by rw [MassDataIdxStIm.hEmb_mul, Units.mul_inv, MassDataIdxStIm.hEmb_one],
    by rw [MassDataIdxStIm.hEmb_mul, Units.inv_mul, MassDataIdxStIm.hEmb_one]⟩
  map_one' := Units.ext (by simp [MassDataIdxStIm.hEmb_one])
  map_mul' g h := Units.ext (by simp [MassDataIdxStIm.hEmb_mul])

theorem hEmbGL_val (g : GL (Fin k) A) :
    ((hEmbGL r k g : GL (Idx r k) A) : Matrix (Idx r k) (Idx r k) A) = hEmb r (g : Matrix (Fin k) (Fin k) A) := rfl

theorem hEmbGL_injective : Function.Injective (hEmbGL (A := A) r k) :=
  fun g h e => Units.ext (MassDataIdxStIm.hEmb_inj (congrArg Units.val e))

theorem hEmb_sub_one_mem_iff (I : Ideal A) (B : Matrix (Fin k) (Fin k) A) :
    (∀ a b, (hEmb r B - 1) a b ∈ I) ↔ ∀ i j, (B - 1) i j ∈ I := by
  constructor
  · intro h i j
    have := h (Sum.inr (Sum.inl (Sum.inl i))) (Sum.inr (Sum.inl (Sum.inl j)))
    simpa [hEmb, midEmb, Matrix.one_apply] using this
  · intro h a b
    rcases a with a | ((a | a) | a) <;> rcases b with b | ((b | b) | b) <;>
      simp [hEmb, midEmb, Matrix.one_apply] <;>
      exact h a b

variable {n : Type} [Fintype n] [DecidableEq n]

theorem entries_mul_mem (I : Ideal A) (P M Q : Matrix n n A) (hM : ∀ a b, M a b ∈ I) :
    ∀ a b, (P * M * Q) a b ∈ I := by
  intro a b
  rw [Matrix.mul_apply]
  refine Ideal.sum_mem _ fun l _ => Ideal.mul_mem_right _ _ ?_
  rw [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun m _ => Ideal.mul_mem_left _ _ (hM m l)

theorem conj_sub_one_mem_iff (I : Ideal A) (c : GL n A) (M : Matrix n n A) :
    (∀ a b, (((c⁻¹ : GL n A) : Matrix n n A) * M * (c : Matrix n n A) - 1) a b ∈ I) ↔ ∀ a b, (M - 1) a b ∈ I := by
  have e : ((c⁻¹ : GL n A) : Matrix n n A) * M * (c : Matrix n n A) - 1 =
      ((c⁻¹ : GL n A) : Matrix n n A) * (M - 1) * (c : Matrix n n A) := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Units.inv_mul]
  rw [e]
  constructor
  · intro h
    have h2 := entries_mul_mem I (c : Matrix n n A) _ ((c⁻¹ : GL n A) : Matrix n n A) h
    have e2 : (c : Matrix n n A) * (((c⁻¹ : GL n A) : Matrix n n A) * (M - 1) * (c : Matrix n n A)) *
        ((c⁻¹ : GL n A) : Matrix n n A) = M - 1 := by
      simp only [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
      rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
    rwa [e2] at h2
  · intro h
    exact entries_mul_mem I _ _ _ h

end GlobalTheory

variable {D : D7}

def HModel (X : HidaSetting D) (u : D.what₂.Word) (p : TypX X) : Prop :=
  ∃ (ψ : KvA X p.1 →* GL (Idx D.R.rS D.R.k) (MassDataIdxSteps.Op X p)) (c : GL (Idx D.R.rS D.R.k) (MassDataIdxSteps.Op X p)),
    Function.Surjective ψ ∧
    (∀ x : KvA X p.1, (∀ i j, ((ψ x : Matrix (Idx D.R.rS D.R.k) (Idx D.R.rS D.R.k) (MassDataIdxSteps.Op X p)) - 1) i j ∈
      Ideal.span {((gOf p : ℕ) : MassDataIdxSteps.Op X p)}) ↔ (x : HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J) ∈ MassDataIdxSteps.KgX X p) ∧
    ∀ x : KvA X p.1, (x : HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J) ∈ Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X u) ↔
      c⁻¹ * ψ x * c ∈ (hEmbGL (A := MassDataIdxSteps.Op X p) D.R.rS D.R.k).range

def inclH (X : HidaSetting D) (u : D.what₂.Word) (p : TypX X) : KvH X u p.1 →* KvA X p.1 where
  toFun x := ⟨((x : Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X u)) :
    HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J), x.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem psiH_exists (X : HidaSetting D) (u : D.what₂.Word) (p : TypX X)
    (ψ : KvA X p.1 →* GL (Idx D.R.rS D.R.k) (MassDataIdxSteps.Op X p)) (c : GL (Idx D.R.rS D.R.k) (MassDataIdxSteps.Op X p))
    (hs : Function.Surjective ψ)
    (hk : ∀ x : KvA X p.1, (∀ i j, ((ψ x : Matrix (Idx D.R.rS D.R.k) (Idx D.R.rS D.R.k) (MassDataIdxSteps.Op X p)) - 1) i j ∈
      Ideal.span {((gOf p : ℕ) : MassDataIdxSteps.Op X p)}) ↔ (x : HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J) ∈ MassDataIdxSteps.KgX X p)
    (hH : ∀ x : KvA X p.1, (x : HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J) ∈ Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X u) ↔
      c⁻¹ * ψ x * c ∈ (hEmbGL (A := MassDataIdxSteps.Op X p) D.R.rS D.R.k).range) :
    ∃ ψH : KvH X u p.1 →* GL (Fin D.R.k) (MassDataIdxSteps.Op X p), Function.Surjective ψH ∧
      (∀ x, hEmbGL D.R.rS D.R.k (ψH x) = c⁻¹ * ψ (inclH X u p x) * c) ∧
      ∀ x : KvH X u p.1, (∀ i j, ((ψH x : Matrix (Fin D.R.k) (Fin D.R.k) (MassDataIdxSteps.Op X p)) - 1) i j ∈
        Ideal.span {((gOf p : ℕ) : MassDataIdxSteps.Op X p)}) ↔ x ∈ KgH X u p := by
  let φ : KvH X u p.1 →* GL (Idx D.R.rS D.R.k) (MassDataIdxSteps.Op X p) :=
    (MulAut.conj c⁻¹).toMonoidHom.comp (ψ.comp (inclH X u p))
  have hφv : ∀ x, φ x = c⁻¹ * ψ (inclH X u p x) * c := fun x => by
    show c⁻¹ * ψ (inclH X u p x) * c⁻¹⁻¹ = _
    rw [inv_inv]
  have hφ : ∀ x, φ x ∈ (hEmbGL (A := MassDataIdxSteps.Op X p) D.R.rS D.R.k).range := fun x => by
    rw [hφv]
    exact (hH (inclH X u p x)).1 (x : Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X u)).2
  let e := MonoidHom.ofInjective (hEmbGL_injective (A := MassDataIdxSteps.Op X p) D.R.rS D.R.k)
  let ψH : KvH X u p.1 →* GL (Fin D.R.k) (MassDataIdxSteps.Op X p) :=
    e.symm.toMonoidHom.comp (φ.codRestrict _ hφ)
  have key : ∀ x, hEmbGL D.R.rS D.R.k (ψH x) = φ x := fun x => by
    rw [← MonoidHom.ofInjective_apply (hEmbGL_injective (A := MassDataIdxSteps.Op X p) D.R.rS D.R.k) (x := ψH x)]
    show ((e (e.symm ⟨φ x, hφ x⟩) : (hEmbGL D.R.rS D.R.k).range) : GL (Idx D.R.rS D.R.k) (MassDataIdxSteps.Op X p)) = φ x
    rw [MulEquiv.apply_symm_apply]
  refine ⟨ψH, fun B => ?_, fun x => by rw [key, hφv], fun x => ?_⟩
  · obtain ⟨x', hx'⟩ := hs (c * hEmbGL D.R.rS D.R.k B * c⁻¹)
    have hconj : c⁻¹ * ψ x' * c = hEmbGL D.R.rS D.R.k B := by rw [hx']; group
    have hxH : (x' : HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J) ∈
        Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X u) := (hH x').2 ⟨B, hconj.symm⟩
    let x : KvH X u p.1 := ⟨⟨(x' : HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J), hxH⟩, x'.2⟩
    refine ⟨x, hEmbGL_injective D.R.rS D.R.k ?_⟩
    rw [key, hφv]
    have : inclH X u p x = x' := rfl
    rw [this, hconj]
  · have h1 := hEmb_sub_one_mem_iff (A := MassDataIdxSteps.Op X p) D.R.rS D.R.k
      (Ideal.span {((gOf p : ℕ) : MassDataIdxSteps.Op X p)}) (ψH x : Matrix (Fin D.R.k) (Fin D.R.k) (MassDataIdxSteps.Op X p))
    rw [← h1, ← hEmbGL_val, key, hφv, Units.val_mul, Units.val_mul, conj_sub_one_mem_iff, hk]
    rfl

theorem hLatGL_of_model (X : HidaSetting D) (u : D.what₂.Word) (p : TypX X) (h : HModel X u p) : HLatGL X u p := by
  obtain ⟨ψ, c, hs, hk, hH⟩ := h
  obtain ⟨ψH, hsH, -, hkH⟩ := psiH_exists X u p ψ c hs hk hH
  exact ⟨ψH, hsH, hkH⟩

end PIW.MassDataColumns
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.Unfold
section
noncomputable section

namespace PIW.MassDataColumns

open MeasureTheory
open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.TypedSets Formalism.L2.SG.Measures Formalism.L2.SG.Sub
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

def MassUnfoldGen : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (u : D.what₂.Word),
    (X.measW u).IsTextNorm →
    CompactSpace (Hsub (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u)) →
    ∀ U : Subgroup ↥(Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u)),
      IsCompact (U : Set ↥(Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u))) →
      IsOpen (U : Set ↥(Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u))) →
      MassFinite (GamHA X u) U →
      ∀ 𝓕 : Set ↥(Hsub (AF X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u)),
        IsFundamentalDomain (ratOf (K := Hsub (AF X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u))) 𝓕 (X.measW u).μH →
        (X.measW u).μH 𝓕 = (X.measW u).μHinf Set.univ *
          (X.measW u).μHf (U : Set ↥(Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u))) *
          ENNReal.ofReal (massCl (GamHA X u) U)

theorem massCl_nonneg {G : Type} [Group G] (Γ K : Subgroup G) : 0 ≤ massCl Γ K := by
  unfold massCl
  exact finsum_nonneg fun _ => inv_nonneg.mpr (Nat.cast_nonneg _)

theorem unfoldGenStep_of (hM : MassUnfoldGen) (hH : MassDataMassesW.HinfCompact) (hF : MassDataMassesW.FDExistsH)
    (hV : MassDataMassesW.VolHTie) : UnfoldGenStep := by
  unfold UnfoldGenStep
  intro D X hb u hT U hUo hUc hMF
  have hN : (X.measW u).IsTextNorm := by
    exact X.measW_norm u
  have hC := hH X u
  have key := hM X u hN hC U hUc hUo hMF
  have hV' := hV X hb u hT
  obtain ⟨𝓕, h𝓕⟩ := hF X u
  have hex : ∃ 𝓕 : Set ↥(Hsub (AF X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u)),
      IsFundamentalDomain (ratOf (K := Hsub (AF X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u))) 𝓕
        (X.measW u).μH := ⟨𝓕, h𝓕⟩
  have hcov : covol (X.measW u).μH = ((X.measW u).μH hex.choose).toReal := by
    unfold covol
    exact dif_pos hex
  obtain ⟨-, hHi, hHf, -⟩ := hN
  haveI := hHi
  haveI := hHf
  have h1 : (X.measW u).μHinf Set.univ ≠ 0 := isOpen_univ.measure_ne_zero _ Set.univ_nonempty
  have h2 : (X.measW u).μHinf Set.univ ≠ ⊤ := (hHi.toIsFiniteMeasureOnCompacts.lt_top_of_isCompact (@isCompact_univ _ _ hC)).ne
  have h3 : (X.measW u).μHf (U : Set ↥(Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u))) ≠ 0 := IsOpen.measure_ne_zero (X.measW u).μHf hUo ⟨1, U.one_mem⟩
  have h4 : (X.measW u).μHf (U : Set ↥(Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u))) ≠ ⊤ := (hHf.toIsFiniteMeasureOnCompacts.lt_top_of_isCompact hUc).ne
  refine ⟨?_, ?_⟩
  · rw [hcov, key hex.choose hex.choose_spec, hV', ENNReal.toReal_mul, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (massCl_nonneg _ _)]
  · rw [hV']
    exact mul_ne_zero (ENNReal.toReal_ne_zero.mpr ⟨h1, h2⟩) (ENNReal.toReal_ne_zero.mpr ⟨h3, h4⟩)

end PIW.MassDataColumns
end
end

