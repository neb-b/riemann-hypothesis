module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0037
public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIntegerUnitSplitPlaceConjugatePrime
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0017

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AbsoluteGaloisAbelianizationEqOneOfMemOpenSubgro
section
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.NormCompat

namespace GlobalTheory.GabSep

theorem eq_one_of_forall_isOpen_subgroup : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    (g : Gab E Ω), (∀ U : Subgroup (Gab E Ω), IsOpen (U : Set (Gab E Ω)) → g ∈ U) → g = 1 := by
  intro E Ω _ _ _ _ g hg
  by_contra hne
  haveI : IsClosed ((commutator (G E Ω)).topologicalClosure : Set (G E Ω)) :=
    Subgroup.isClosed_topologicalClosure _
  have hT1 : T1Space (Gab E Ω) := inferInstance
  have hopen : IsOpen ({g}ᶜ : Set (Gab E Ω)) := isOpen_compl_singleton
  have hmem : ((QuotientGroup.mk : G E Ω → Gab E Ω) ⁻¹' {g}ᶜ) ∈ nhds (1 : G E Ω) := by
    refine (hopen.preimage QuotientGroup.continuous_mk).mem_nhds ?_
    simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff, QuotientGroup.mk_one]
    exact fun h => hne h.symm
  obtain ⟨L, hL, hsub⟩ := (krullTopology_mem_nhds_one_iff E Ω _).mp hmem
  let V : Subgroup (Gab E Ω) := L.fixingSubgroup.map (QuotientGroup.mk' _)
  have hV : IsOpen (V : Set (Gab E Ω)) := by
    have : (V : Set (Gab E Ω)) = (QuotientGroup.mk : G E Ω → Gab E Ω) '' (L.fixingSubgroup : Set (G E Ω)) := by
      simp [V, Subgroup.coe_map]
    rw [this]
    exact QuotientGroup.isOpenMap_coe _ (IntermediateField.fixingSubgroup_isOpen L)
  obtain ⟨σ, hσ, e⟩ := Subgroup.mem_map.mp (hg V hV)
  exact hsub hσ (by simpa using e)

end GlobalTheory.GabSep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CayleyTransformMemRationalUnitaryGroup
section
open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW

namespace GlobalTheory.CayleyRat

theorem exists_mem_GQ0_eq_cayley_of_skew_hermitian : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (S : Matrix (Fin n) (Fin n) L), S + (S.map (IsCMField.complexConj L : L →+* L))ᵀ = 0 → (1 - S).det ≠ 0 → ∃ γ₀ : GL (Fin n) L, γ₀ ∈ GQ0 L n ∧ (γ₀ : Matrix (Fin n) (Fin n) L) = (1 + S) * (1 - S)⁻¹ := by
  intro L _ _ _ n S hS hdet
  set c : L →+* L := (IsCMField.complexConj L : L →+* L) with hc
  set T : Matrix (Fin n) (Fin n) L := 1 - S with hT
  set U : Matrix (Fin n) (Fin n) L := 1 + S with hU
  have hSc : conjT c S = -S := by
    unfold conjT; exact (neg_eq_of_add_eq_zero_right hS).symm
  have hcT : conjT c T = U := by
    have : conjT c T = conjT c 1 - conjT c S := by
      simp [conjT, hT, Matrix.map_sub, Matrix.transpose_sub]
    rw [this, conjT_one, hSc, hU, sub_neg_eq_add]
  have hcU : conjT c U = T := by
    have : conjT c U = conjT c 1 + conjT c S := by
      simp [conjT, hU, Matrix.map_add (f := _), Matrix.transpose_add]
    rw [this, conjT_one, hSc, hT, sub_eq_add_neg]
  have hdetU : U.det ≠ 0 := by
    have : U.det = c T.det := by
      rw [← hcT, conjT, Matrix.det_transpose, RingHom.map_det]; rfl
    rw [this]; exact (map_ne_zero c).mpr hdet
  have huT : IsUnit T.det := isUnit_iff_ne_zero.mpr hdet
  have huU : IsUnit U.det := isUnit_iff_ne_zero.mpr hdetU
  have hcTinv : conjT c T⁻¹ = U⁻¹ := by
    have h1 : U * conjT c T⁻¹ = 1 := by
      rw [← hcT, ← conjT_mul, Matrix.nonsing_inv_mul _ huT, conjT_one]
    exact (Matrix.inv_eq_right_inv h1).symm
  have hcomm : U * T = T * U := by
    simp [hU, hT, mul_sub, sub_mul, mul_add, add_mul]; abel
  have hinv : T⁻¹ * U⁻¹ = U⁻¹ * T⁻¹ := by
    rw [← Matrix.mul_inv_rev, ← Matrix.mul_inv_rev, hcomm]
  have hdetγ : IsUnit (U * T⁻¹).det := by
    rw [Matrix.det_mul]; exact huU.mul (Matrix.isUnit_nonsing_inv_det T huT)
  refine ⟨Matrix.nonsingInvUnit (U * T⁻¹) hdetγ, ?_, rfl⟩
  show (U * T⁻¹) * conjT c (U * T⁻¹) = 1
  rw [conjT_mul, hcTinv, hcU, Matrix.mul_assoc, ← Matrix.mul_assoc T⁻¹, hinv, ← Matrix.mul_assoc,
    ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ huU, Matrix.one_mul, Matrix.nonsing_inv_mul _ huT]

end GlobalTheory.CayleyRat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CommuteOfLocEqOne
section
open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2

noncomputable section

namespace GlobalTheory.SplitLocComm

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

theorem map_compAt_eq_one {n : ℕ} (s : SplitPlace L) (x : GA L n) (hx : s.loc n x = 1) :
    (x.1 : Matrix (Fin n) (Fin n) (AL L)).map (compAt L s.v) = 1 := by
  have hx' : s.loc n x⁻¹ = 1 := by rw [map_inv, hx, inv_one]
  ext i j
  have hconj : conjAL L ((x.1 : Matrix (Fin n) (Fin n) (AL L)) i j) =
      (((x⁻¹ : GA L n).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) j i := by
    have hm := x.2
    simp only [GA, UGroup, Subgroup.mem_mk] at hm
    have h1 : ((x.1⁻¹ : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) = conjT (conjAL L) x.1 :=
      Units.inv_eq_of_mul_eq_one_right hm
    simp only [InvMemClass.coe_inv, h1, conjT, Matrix.transpose_apply, Matrix.map_apply]
  have hz : compAt L s.v ((x.1 : Matrix (Fin n) (Fin n) (AL L)) i j - (1 : Matrix (Fin n) (Fin n) (AL L)) i j) = 0 := by
    have exists_imag : ∃ θ : L, θ ≠ 0 ∧ IsCMField.complexConj L θ = -θ := by
      have h := IsCMField.complexConj_ne_one L
      obtain ⟨x, hx⟩ : ∃ x : L, IsCMField.complexConj L x ≠ x := by
        by_contra hc
        push Not at hc
        exact h (AlgEquiv.ext hc)
      refine ⟨x - IsCMField.complexConj L x, sub_ne_zero.mpr hx.symm, ?_⟩
      rw [map_sub, IsCMField.complexConj_apply_apply]; ring
    have exists_real_add (θ : L) (h0 : θ ≠ 0) (hθ : IsCMField.complexConj L θ = -θ) (x : L) :
        ∃ a b : maximalRealSubfield L, x = a • (1 : L) + b • θ := by
      have h2 : IsCMField.complexConj L (2 : L) = 2 := map_ofNat _ 2
      have ha : (x + IsCMField.complexConj L x) / 2 ∈ maximalRealSubfield L := by
        rw [← IsCMField.complexConj_eq_self_iff, map_div₀, map_add (f := _), IsCMField.complexConj_apply_apply, h2]
        ring
      have hb : (x - IsCMField.complexConj L x) / (2 * θ) ∈ maximalRealSubfield L := by
        rw [← IsCMField.complexConj_eq_self_iff, map_div₀, map_sub, map_mul,
          IsCMField.complexConj_apply_apply, h2, hθ]
        field_simp
        ring
      refine ⟨⟨_, ha⟩, ⟨_, hb⟩, ?_⟩
      change x = (x + IsCMField.complexConj L x) / 2 * 1 + (x - IsCMField.complexConj L x) / (2 * θ) * θ
      field_simp
      ring
    have exists_tmul_add (θ : L) (h0 : θ ≠ 0) (hθ : IsCMField.complexConj L θ = -θ) (z : AL L) :
        ∃ a b : AFplus L, z = (1 : L) ⊗ₜ[maximalRealSubfield L] a + θ ⊗ₜ[maximalRealSubfield L] b := by
      induction z using TensorProduct.induction_on with
      | zero => exact ⟨0, 0, by simp⟩
      | tmul x c =>
        obtain ⟨a, b, rfl⟩ := exists_real_add θ h0 hθ x
        exact ⟨a • c, b • c, by rw [TensorProduct.add_tmul, TensorProduct.smul_tmul, TensorProduct.smul_tmul]⟩
      | add x y hx hy =>
        obtain ⟨a, b, rfl⟩ := hx
        obtain ⟨a', b', rfl⟩ := hy
        exact ⟨a + a', b + b', by rw [TensorProduct.tmul_add, TensorProduct.tmul_add]; abel⟩
    have compAt_eq_zero (z : AL L) (h1 : s.proj z = 0) (h2 : s.proj (conjAL L z) = 0) : compAt L s.v z = 0 := by
      obtain ⟨θ, h0, hθ⟩ := exists_imag
      obtain ⟨a, b, rfl⟩ := exists_tmul_add θ h0 hθ z
      have e1 : evalAt L s.v a + s.i θ * evalAt L s.v b = 0 := by
        simpa [SplitPlace.proj] using h1
      have e2 : evalAt L s.v a - s.i θ * evalAt L s.v b = 0 := by
        simpa [SplitPlace.proj, conjAL, hθ, TensorProduct.neg_tmul, sub_eq_add_neg] using h2
      have hi : s.i θ ≠ 0 := (map_ne_zero s.i).mpr h0
      have : CharZero (s.v.adicCompletion (maximalRealSubfield L)) := algebraRat.charZero _
      have ha : evalAt L s.v a = 0 := by linear_combination (e1 + e2) / 2
      have hb : evalAt L s.v b = 0 := by
        rw [ha, zero_add] at e1
        exact (mul_eq_zero.mp e1).resolve_left hi
      simp [compAt, ha, hb]
    apply compAt_eq_zero
    · have e1 : s.proj ((x.1 : Matrix (Fin n) (Fin n) (AL L)) i j) =
          ((s.loc n x : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) i j := rfl
      rw [map_sub, e1, hx]
      by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
    · have e1 : s.proj ((((x⁻¹ : GA L n).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) j i) =
          ((s.loc n x⁻¹ : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) j i := rfl
      rw [map_sub, map_sub, hconj, e1, hx']
      by_cases hij : i = j <;> simp [Matrix.one_apply, hij, eq_comm]
  rw [map_sub, sub_eq_zero] at hz
  rw [Matrix.map_apply, hz]
  by_cases hij : i = j <;> simp [Matrix.one_apply, hij]

theorem commute_of_loc_eq_one : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (s : SplitPlace L)
    (x y : GAf L n), s.loc n x = 1 → TrivOutside {s.v} y → Commute x y := by
  intro L _ _ _ n s x y hx hy
  refine Subtype.ext (Units.ext ?_)
  change (x.1 : Matrix (Fin n) (Fin n) (AL L)) * (y.1 : Matrix (Fin n) (Fin n) (AL L)) =
    (y.1 : Matrix (Fin n) (Fin n) (AL L)) * (x.1 : Matrix (Fin n) (Fin n) (AL L))
  ext i j
  rw [← sub_eq_zero]
  refine GlobalTheory.AdelicComp.eq_zero_of_compAt_eq_zero L _ fun w => ?_
  have h : ((x.1 : Matrix (Fin n) (Fin n) (AL L)) * (y.1 : Matrix (Fin n) (Fin n) (AL L))).map (compAt L w) =
      ((y.1 : Matrix (Fin n) (Fin n) (AL L)) * (x.1 : Matrix (Fin n) (Fin n) (AL L))).map (compAt L w) := by
    rw [Matrix.map_mul, Matrix.map_mul]
    by_cases hw : w = s.v
    · subst hw
      rw [map_compAt_eq_one s x hx, one_mul, mul_one]
    · rw [hy w (by simpa using hw), one_mul, mul_one]
  rw [map_sub, sub_eq_zero]
  exact congrFun (congrFun h i) j

end GlobalTheory.SplitLocComm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CongOfLoc
section
open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2

noncomputable section

namespace GlobalTheory.CongSplit

theorem conj_entry {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} (x : GA L n) (i j : Fin n) :
    conjAL L ((x.1 : Matrix (Fin n) (Fin n) (AL L)) i j) =
      (((x⁻¹ : GA L n).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) j i := by
  have hm := x.2
  simp only [GA, UGroup, Subgroup.mem_mk] at hm
  have h1 : ((x.1⁻¹ : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) = conjT (conjAL L) x.1 :=
    Units.inv_eq_of_mul_eq_one_right hm
  simp only [InvMemClass.coe_inv, h1, conjT, Matrix.transpose_apply, Matrix.map_apply]

theorem cong_of_loc : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (s : SplitPlace L) (N : ℕ), 0 < N →
    ∀ x : GAf L n, TrivOutside {s.v} x →
    (∀ i j, Valued.v (((s.loc n x : GL (Fin n) (s.v.adicCompletion (NumberField.maximalRealSubfield L))) :
        Matrix (Fin n) (Fin n) (s.v.adicCompletion (NumberField.maximalRealSubfield L))) i j -
        (1 : Matrix (Fin n) (Fin n) (s.v.adicCompletion (NumberField.maximalRealSubfield L))) i j) ≤
      Valued.v ((N : s.v.adicCompletion (NumberField.maximalRealSubfield L)))) →
    (∀ i j, Valued.v (((s.loc n x⁻¹ : GL (Fin n) (s.v.adicCompletion (NumberField.maximalRealSubfield L))) :
        Matrix (Fin n) (Fin n) (s.v.adicCompletion (NumberField.maximalRealSubfield L))) i j -
        (1 : Matrix (Fin n) (Fin n) (s.v.adicCompletion (NumberField.maximalRealSubfield L))) i j) ≤
      Valued.v ((N : s.v.adicCompletion (NumberField.maximalRealSubfield L)))) →
    NG.Cong L n N x := by
  intro L _ _ _ n s N hN x hx h1 h2
  obtain ⟨e, he, he'⟩ := GlobalTheory.SplitSep.exists_sep L s
  have hNL : (N : L) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  obtain ⟨u, hu⟩ : ∃ u : AL L, (N : AL L) * u = 1 := ⟨algebraMap L (AL L) (N : L)⁻¹, by
    rw [← map_natCast (algebraMap L (AL L)), ← map_mul, mul_inv_cancel₀ hNL, map_one]⟩
  have key : ∀ (f : AL L →+* s.v.adicCompletion (maximalRealSubfield L)) (z : AL L),
      Valued.v (f z) ≤ Valued.v ((N : s.v.adicCompletion (maximalRealSubfield L))) → Valued.v (f (u * z)) ≤ 1 := by
    intro f z hz
    have h := congrArg (fun t => Valued.v (f t)) hu
    simp only [map_mul, map_natCast, map_one] at h
    rw [map_mul, map_mul, ← h, mul_comm]
    exact mul_le_mul_left hz _
  suffices H : ∀ i j : Fin n, ∃ y ∈ ALint L, (x.1 : Matrix (Fin n) (Fin n) (AL L)) i j -
      (1 : Matrix (Fin n) (Fin n) (AL L)) i j = (N : AL L) * y by
    refine ⟨fun i j => ?_, H⟩
    obtain ⟨y, hy, hxy⟩ := H i j
    rw [sub_eq_iff_eq_add.1 hxy]
    refine add_mem (mul_mem (natCast_mem _ N) hy) ?_
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij, Subring.one_mem, Subring.zero_mem]
  intro i j
  refine ⟨u * ((x.1 : Matrix (Fin n) (Fin n) (AL L)) i j - (1 : Matrix (Fin n) (Fin n) (AL L)) i j), ?_, ?_⟩
  · apply GlobalTheory.mem_ALint_of_supported_at_split L s e he he'
    · intro w hw
      have := congrFun (congrFun (hx w (by simpa using hw)) i) j
      simp only [Matrix.map_apply] at this
      rw [map_mul, map_sub, this]
      by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
    · apply key
      have e1 : s.proj ((x.1 : Matrix (Fin n) (Fin n) (AL L)) i j) =
          ((s.loc n x : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) i j := rfl
      have e2 : s.proj ((1 : Matrix (Fin n) (Fin n) (AL L)) i j) =
          (1 : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) i j := by
        by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
      rw [map_sub, e1, e2]
      exact h1 i j
    · apply key (s.proj.comp (conjAL L))
      have e1 : s.proj ((((x⁻¹ : GA L n).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) j i) =
          ((s.loc n x⁻¹ : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) j i := rfl
      have e2 : (s.proj.comp (conjAL L)) ((1 : Matrix (Fin n) (Fin n) (AL L)) i j) =
          (1 : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) j i := by
        by_cases hij : i = j
        · simp [Matrix.one_apply, hij]
        · simp [Matrix.one_apply, hij, Ne.symm hij]
      rw [map_sub, e2, RingHom.comp_apply, conj_entry, e1]
      exact h2 j i
  · rw [← mul_assoc, hu, one_mul]

end GlobalTheory.CongSplit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjugateNeSelf
section
noncomputable section

open NumberField Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP Matrix

namespace GlobalTheory.AlgWtHW

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem exists_gq (γ₀ : GL (Fin n) L) (h : γ₀ ∈ GQ0 L n) :
    ∃ γ : GQ L n, (((γ : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) =
      (γ₀ : Matrix (Fin n) (Fin n) L).map (Algebra.TensorProduct.includeLeftRingHom) := by
  set g := Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* AL L) γ₀ with hgdef
  have hg : g ∈ GA L n := by
    show g.val * conjT (conjAL L) g.val = 1
    have e : conjT (conjAL L) g.val =
        (conjT (IsCMField.complexConj L : L →+* L) γ₀.val).map
          (Algebra.TensorProduct.includeLeftRingHom : L →+* AL L) := by
      ext i j
      simp [conjT, g, conjAL, Algebra.TensorProduct.map_tmul]
    rw [e]
    have h' : γ₀.val * conjT (IsCMField.complexConj L : L →+* L) γ₀.val = 1 := h
    show γ₀.val.map (Algebra.TensorProduct.includeLeftRingHom : L →+* AL L) * _ = 1
    rw [← Matrix.map_mul, h', Matrix.map_one _ (map_zero _) (map_one _)]
  exact ⟨⟨⟨g, hg⟩, Subgroup.mem_subgroupOf.2 ⟨γ₀, h, rfl⟩⟩, rfl⟩

theorem conj_conj (φ : L →+* ℂ) :
    ComplexEmbedding.conjugate (ComplexEmbedding.conjugate φ) = φ := by
  ext x; simp

theorem conjugate_ne_self (τ : L →+* ℂ) : ComplexEmbedding.conjugate τ ≠ τ := fun h =>
  IsTotallyComplex.complexEmbedding_not_isReal τ (ComplexEmbedding.isReal_iff.2 h)

theorem isUPt_ratPt (γ₀ : GL (Fin n) L) (h : γ₀ ∈ GQ0 L n) : IsUPt (ratPt γ₀.val) := by
  intro σ
  have h' : γ₀.val * conjT (IsCMField.complexConj L : L →+* L) γ₀.val = 1 := h
  have e : ratPt γ₀.val (ComplexEmbedding.conjugate σ) = (γ₀.val.map (IsCMField.complexConj L : L →+* L)).map σ := by
    ext i j
    simp [ratPt, IsCMField.complexEmbedding_complexConj]
  rw [e]
  have := congrArg (fun M => M.map σ) h'
  simpa [ratPt, conjT, Matrix.map_mul, Matrix.transpose_map] using this

open scoped Classical in
open Classical in
def tauPt (τ : L →+* ℂ) (B : GL (Fin n) ℂ) : (L →+* ℂ) → Matrix (Fin n) (Fin n) ℂ := fun σ =>
  if σ = τ then B.val else if σ = ComplexEmbedding.conjugate τ then (B⁻¹).valᵀ else 1

theorem evPt_eq_upt (τ : L →+* ℂ) (B : GL (Fin n) ℂ) :
    Formalism.L2.NG.evPt τ B = upt (tauPt τ B) := by
  funext p
  simp only [Formalism.L2.NG.evPt, upt, tauPt]
  split_ifs <;> simp [Matrix.one_apply, *]

theorem isUPt_tauPt (τ : L →+* ℂ) (B : GL (Fin n) ℂ) : IsUPt (tauPt τ B) := by
  intro σ
  have hne := conjugate_ne_self τ
  by_cases h1 : σ = τ
  · subst h1
    simp [tauPt, hne, Matrix.transpose_transpose]
  · by_cases h2 : σ = ComplexEmbedding.conjugate τ
    · subst h2
      simp only [tauPt, if_neg h1, conj_conj, if_true]
      rw [← Matrix.transpose_transpose (B.val), ← Matrix.transpose_mul, Matrix.transpose_transpose,
        ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.transpose_one]
    · have h3 : ComplexEmbedding.conjugate σ ≠ τ := fun e => h2 (by rw [← e, conj_conj])
      have h4 : ComplexEmbedding.conjugate σ ≠ ComplexEmbedding.conjugate τ := fun e => h1 (by
        simpa using congrArg ComplexEmbedding.conjugate e)
      simp [tauPt, h1, h2, h3, h4]

end GlobalTheory.AlgWtHW
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DominanceOrderLEOfMemSpanWeightVectorsDominatedB
section
open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW

namespace GlobalTheory.AlgWtHW.DomLEOfSle

noncomputable def diagU {n : ℕ} (u : Fin n → ℂˣ) : GL (Fin n) ℂ :=
  ⟨Matrix.diagonal (fun i => (u i : ℂ)), Matrix.diagonal (fun i => ((u i)⁻¹ : ℂˣ)),
    by simp [Matrix.diagonal_mul_diagonal], by simp [Matrix.diagonal_mul_diagonal]⟩

lemma diag_commute {n : ℕ} (D E : GL (Fin n) ℂ) (hD : D.val.IsDiag) (hE : E.val.IsDiag) :
    D * E = E * D := by
  ext1
  simp only [Units.val_mul]
  rw [← hD.diagonal_diag, ← hE.diagonal_diag, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_comm _ _

lemma two_zpow_inj {a b : ℤ} (h : (2 : ℂ) ^ a = (2 : ℂ) ^ b) : a = b := by
  have h' : ((2 : ℝ) ^ a : ℝ) = (2 : ℝ) ^ b := by
    have := congrArg Complex.re h
    have ha : ((2 : ℂ) ^ a) = (((2 : ℝ) ^ a : ℝ) : ℂ) := by push_cast; rfl
    have hb : ((2 : ℂ) ^ b) = (((2 : ℝ) ^ b : ℝ) : ℂ) := by push_cast; rfl
    rw [ha, hb] at h
    exact_mod_cast h
  exact zpow_right_injective₀ (by norm_num : (0:ℝ) < 2) (by norm_num : (2:ℝ) ≠ 1) h'

end GlobalTheory.AlgWtHW.DomLEOfSle

namespace GlobalTheory.AlgWtHW.DomLEOfSle

theorem domLE_of_mem_Sle : ∀ (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι]
    (Φ : GL (Fin n) ℂ → Matrix ι ι ℂ), IsPolyRep Φ → ∀ (μ lam : Fin n → ℤ) (w : ι → ℂ),
    IsWtVec Φ μ w → w ≠ 0 → w ∈ Sle Φ lam → DomLE μ lam := by
  intro n ι _ _ Φ hΦ μ lam w hw hw0 hS
  by_contra hnot
  let J := {D : GL (Fin n) ℂ // D.val.IsDiag}
  let T : J → Module.End ℂ (ι → ℂ) := fun D => Matrix.toLin' (Φ D.1)
  have hc : ∀ a b : J, Commute (T a) (T b) := by
    intro a b
    show T a * T b = T b * T a
    have e : ∀ A B : Matrix ι ι ℂ, Matrix.toLin' A * Matrix.toLin' B = Matrix.toLin' (A * B) :=
      fun A B => by rw [Matrix.toLin'_mul]; rfl
    simp only [T]
    rw [e, e, ← hΦ.mul, ← hΦ.mul, diag_commute a.1 b.1 a.2 b.2]
  have hind := Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo T
    (fun i j φ => Module.End.mapsTo_maxGenEigenspace_of_comm (hc j i) φ)
  let χ : (Fin n → ℤ) → J → ℂ := fun ν D => ∏ i, (D.1.val i i) ^ (ν i)
  let E : (J → ℂ) → Submodule ℂ (ι → ℂ) := fun c => ⨅ D, (T D).maxGenEigenspace (c D)
  have hmem : ∀ ν v, IsWtVec Φ ν v → v ∈ E (χ ν) := by
    intro ν v hv
    refine Submodule.mem_iInf _ |>.mpr fun D => ?_
    apply Module.End.eigenspace_le_maxGenEigenspace
    rw [Module.End.mem_eigenspace_iff]
    simp only [T, Matrix.toLin'_apply]
    exact hv D.1 D.2
  have hχinj : ∀ ν ν', χ ν = χ ν' → ν = ν' := by
    intro ν ν' h
    funext i
    let u : Fin n → ℂˣ := Function.update 1 i (Units.mk0 2 two_ne_zero)
    have hD : (diagU u).val.IsDiag := by
      show (Matrix.diagonal _).IsDiag
      exact Matrix.isDiag_diagonal _
    have key := congrFun h ⟨diagU u, hD⟩
    have hprod : ∀ ν'' : Fin n → ℤ, χ ν'' ⟨diagU u, hD⟩ = (2 : ℂ) ^ (ν'' i) := by
      intro ν''
      simp only [χ, diagU, Matrix.diagonal_apply_eq]
      rw [Finset.prod_eq_single i]
      · simp [u]
      · intro j _ hj
        simp [u, Function.update_of_ne hj]
      · simp
    rw [hprod, hprod] at key
    exact two_zpow_inj key
  have hle : Sle Φ lam ≤ ⨆ (c : J → ℂ) (_ : c ≠ χ μ), E c := by
    unfold Sle
    rw [Submodule.span_le]
    rintro v ⟨ν, hν, hv⟩
    have hne : χ ν ≠ χ μ := by
      intro h
      have := hχinj _ _ h
      subst this
      exact hnot hν
    exact (le_iSup₂ (f := fun (c : J → ℂ) (_ : c ≠ χ μ) => E c) (χ ν) hne) (hmem ν v hv)
  have hdis := hind (χ μ)
  have h1 : w ∈ E (χ μ) := hmem μ w hw
  have h2 : w ∈ ⨆ (c : J → ℂ) (_ : c ≠ χ μ), E c := hle hS
  exact hw0 ((Submodule.disjoint_def.mp hdis) w h1 h2)

end GlobalTheory.AlgWtHW.DomLEOfSle
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFinsetPlacesOverFinsetPlaces
section
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.NormCompat

namespace GlobalTheory.PlacesOver

theorem finite_fibre (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K]
    (v : HeightOneSpectrum (𝓞 E)) :
    {w : HeightOneSpectrum (𝓞 K) | w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v.asIdeal}.Finite := by
  have hne : Ideal.map (algebraMap (𝓞 E) (𝓞 K)) v.asIdeal ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot v.ne_bot
  refine (Ideal.finite_factors hne).subset ?_
  intro w hw
  simp only [Set.mem_setOf_eq] at hw ⊢
  rw [Ideal.dvd_iff_le, Ideal.map_le_iff_le_comap, hw]

theorem places_over_finset (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K]
    (S : Finset (HeightOneSpectrum (𝓞 E))) :
    ∃ T : Finset (HeightOneSpectrum (𝓞 K)), ∀ w, w ∈ T ↔ ∃ v ∈ S,
      w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v.asIdeal := by
  have hfin : (⋃ v ∈ S, {w : HeightOneSpectrum (𝓞 K) |
      w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v.asIdeal}).Finite :=
    S.finite_toSet.biUnion fun v _ => finite_fibre E K v
  refine ⟨hfin.toFinset, fun w => ?_⟩
  simp

end GlobalTheory.PlacesOver
end

