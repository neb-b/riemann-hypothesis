module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.Bundle0015
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.Bundle0012

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.FirstRaisingMemEquivariant
section
noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.TypedSets NumberField IsDedekindDomain Formalism.BasicNotions
  Formalism.L2.SG.HidaSetting
open scoped TensorProduct

section Loc

variable {D : D7} (X : HidaSetting D) (p : TypX X) (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p)

def UnitElt : Prop :=
  ∃ a : 𝓞 X.B.I.E, ∃ w ∈ OpX X p, w * (iota1 X p θ (a : X.B.I.E) - iota2 X p θ (a : X.B.I.E)) = 1

theorem firstSplitCoord_smul (c : FpX X p) (t : TpX X p) : th1 X p θ (c • t) = c * th1 X p θ t := by
  show (θ (c • t)).1 = c * (θ t).1
  rw [map_smul]
  rfl

theorem secondSplitCoord_smul (c : FpX X p) (t : TpX X p) : th2 X p θ (c • t) = c * th2 X p θ t := by
  show (θ (c • t)).2 = c * (θ t).2
  rw [map_smul]
  rfl

theorem osmul_eq (c : OpX X p) (t : TpX X p) : c • t = (c : FpX X p) • t := rfl

theorem th_incl (e : X.B.I.E) : θ (inclR (FpX X p) e) = (iota1 X p θ e, iota2 X p θ e) := rfl

theorem first_raising_mem_equivariant (h : UnitElt X p θ) (l : Fin X.B.I.n → X.B.I.E) (hl : l ∈ X.B.I.L) :
    (fun j => θ.symm (iota1 X p θ (l j), 0)) ∈
      latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) := by
  obtain ⟨a, w, hw, hwa⟩ := h
  have hc2 : iota2 X p θ (a : X.B.I.E) ∈ OpX X p := MassDataIdxLatFree.int_mem (OpX X p) (iota2 X p θ) a
  have heq : (fun j => θ.symm (iota1 X p θ (l j), 0)) =
      (⟨w, hw⟩ : OpX X p) • (ratV (F := X.B.I.F) (FpX X p) (a • l) -
        (⟨iota2 X p θ (a : X.B.I.E), hc2⟩ : OpX X p) • ratV (F := X.B.I.F) (FpX X p) l) := by
    funext j
    apply θ.injective
    rw [AlgEquiv.apply_symm_apply]
    show _ = θ ((w : FpX X p) • (inclR (FpX X p) ((a : X.B.I.E) * l j) -
      (iota2 X p θ (a : X.B.I.E)) • inclR (FpX X p) (l j)))
    rw [map_smul, map_sub, map_smul, map_mul, map_mul]
    simp only [th_incl]
    refine Prod.ext ?_ ?_
    · show iota1 X p θ (l j) = w * (iota1 X p θ (a : X.B.I.E) * iota1 X p θ (l j) -
        iota2 X p θ (a : X.B.I.E) * iota1 X p θ (l j))
      linear_combination (-(iota1 X p θ (l j))) * hwa
    · show (0 : FpX X p) = w * (iota2 X p θ (a : X.B.I.E) * iota2 X p θ (l j) -
        iota2 X p θ (a : X.B.I.E) * iota2 X p θ (l j))
      ring
  rw [heq]
  refine Submodule.smul_mem _ _ (Submodule.sub_mem _ ?_ (Submodule.smul_mem _ _ ?_))
  · exact Submodule.subset_span ⟨a • l, X.B.I.L.smul_mem a hl, rfl⟩
  · exact Submodule.subset_span ⟨l, hl, rfl⟩

theorem firstLattice_mem_local (h : UnitElt X p θ) (y : Fin X.B.I.n → FpX X p) (hy : y ∈ Mlat1 X p θ) :
    (fun j => θ.symm (y j, 0)) ∈ latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨l, hl, rfl⟩ := hy
    exact first_raising_mem_equivariant X p θ h l hl
  | zero =>
    convert Submodule.zero_mem (latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))) using 1 <;> funext j <;> simp
  | add y y' _ _ hy hy' =>
    convert Submodule.add_mem _ hy hy' using 1
    funext j
    simp only [Pi.add_apply]
    rw [← map_add, Prod.mk_add_mk, add_zero]
  | smul c y _ hy =>
    convert Submodule.smul_mem _ c hy using 1
    funext j
    simp only [Pi.smul_apply, osmul_eq X p]
    rw [← map_smul, Prod.smul_mk, smul_zero]
    rfl

theorem secondLattice_mem_local (h : UnitElt X p θ) (z : Fin X.B.I.n → FpX X p) (hz : z ∈ Mlat2 X p θ) :
    (fun j => θ.symm (0, z j)) ∈ latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨l, hl, rfl⟩ := hz
    have h1 := first_raising_mem_equivariant X p θ h l hl
    have h2 : ratV (F := X.B.I.F) (FpX X p) l ∈ latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) :=
      Submodule.subset_span ⟨l, hl, rfl⟩
    convert Submodule.sub_mem _ h2 h1 using 1
    funext j
    apply θ.injective
    change θ (θ.symm (0, iota2 X p θ (l j))) = θ (inclR (FpX X p) (l j) - θ.symm (iota1 X p θ (l j), 0))
    rw [map_sub, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply, th_incl]
    ext <;> simp
  | zero =>
    convert Submodule.zero_mem (latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))) using 1 <;> funext j <;> simp
  | add y y' _ _ hy hy' =>
    convert Submodule.add_mem _ hy hy' using 1
    funext j
    simp only [Pi.add_apply]
    rw [← map_add, Prod.mk_add_mk, zero_add]
  | smul c y _ hy =>
    convert Submodule.smul_mem _ c hy using 1
    funext j
    simp only [Pi.smul_apply, osmul_eq X p]
    rw [← map_smul, Prod.smul_mk, smul_zero]
    rfl

theorem latSplit_of (h : UnitElt X p θ) : LatSplitP X p θ := by
  unfold LatSplitP
  intro x
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨l, hl, rfl⟩ := hx
      exact ⟨Submodule.subset_span ⟨l, hl, rfl⟩, Submodule.subset_span ⟨l, hl, rfl⟩⟩
    | zero =>
      simp only [Pi.zero_apply, map_zero]
      exact ⟨Submodule.zero_mem _, Submodule.zero_mem _⟩
    | add x y _ _ hx hy =>
      simp only [Pi.add_apply, map_add (f := _)]
      exact ⟨Submodule.add_mem _ hx.1 hy.1, Submodule.add_mem _ hx.2 hy.2⟩
    | smul c x _ hx =>
      simp only [Pi.smul_apply, osmul_eq X p, firstSplitCoord_smul, secondSplitCoord_smul]
      exact ⟨Submodule.smul_mem _ c hx.1, Submodule.smul_mem _ c hx.2⟩
  · rintro ⟨h1, h2⟩
    have hx : x = (fun j => θ.symm (th1 X p θ (x j), 0)) + (fun j => θ.symm (0, th2 X p θ (x j))) := by
      funext j
      simp only [Pi.add_apply]
      rw [← map_add (f := _), Prod.mk_add_mk, add_zero, zero_add]
      apply θ.injective
      rw [AlgEquiv.apply_symm_apply]
      rfl
    rw [hx]
    exact Submodule.add_mem _ (firstLattice_mem_local X p θ h _ h1) (secondLattice_mem_local X p θ h _ h2)

end Loc

end MassDataIdxSteps
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.ImAGOthNotDvd
section
noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting

variable {D : D7} (X : HidaSetting D)


open Classical in
def gOth (p : TypX X) : ℕ := if ((D.host.g 0 : ℕ) : 𝓞 X.B.I.F) ∈ p.1.asIdeal then D.host.g 1 else D.host.g 0

theorem imA_g_eq_mul (p : TypX X) : X.B.g = gOf p * gOth X p := by
  rw [X.g_eq]; unfold gOf gOth; split_ifs
  · rfl
  · exact mul_comm _ _

private theorem gOf_coprime_gOth (p : TypX X) : Nat.Coprime (gOf p) (gOth X p) := by
  have h0 := D.host.g_prime 0
  have h1 := D.host.g_prime 1
  have hne := D.host.g_ne
  unfold gOth gOf
  split_ifs
  · exact (Nat.coprime_primes h0 h1).2 hne
  · exact (Nat.coprime_primes h1 h0).2 hne.symm

private theorem le_exp_sub_one_of_lt_exp' (y : WithZero (Multiplicative ℤ)) (k : ℤ) (h : y < WithZero.exp k) :
    y ≤ WithZero.exp (k - 1) := by
  rcases eq_or_ne y 0 with rfl | hy
  · exact zero_le'
  · rw [← WithZero.exp_log hy] at h ⊢
    rw [WithZero.exp_lt_exp] at h
    rw [WithZero.exp_le_exp]
    omega

private theorem exp_add_one_le_of_exp_lt (y : WithZero (Multiplicative ℤ)) (k : ℤ) (h : WithZero.exp k < y) :
    WithZero.exp (k + 1) ≤ y := by
  have hy : y ≠ 0 := (lt_of_le_of_lt zero_le' h).ne'
  rw [← WithZero.exp_log hy] at h ⊢
  rw [WithZero.exp_lt_exp] at h
  rw [WithZero.exp_le_exp]
  omega

theorem imA_span_g_max (p : TypX X) :
    Ideal.span {((gOf p : ℕ) : p.1.adicCompletionIntegers X.B.I.F)} =
      IsLocalRing.maximalIdeal (p.1.adicCompletionIntegers X.B.I.F) := by
  have hmem : ((gOf p : ℕ) : 𝓞 X.B.I.F) ∈ p.1.asIdeal := by
    have hty := (mem_typSet X.B.I.F (D.host.g 0) (D.host.g 1) (D.host.g_prime 0).ne_zero
      (D.host.g_prime 1).ne_zero p.1).1 p.2
    unfold gOf
    split_ifs with h
    · exact h
    · exact hty.resolve_left h
  have hgp : Fact (gOf p).Prime := ⟨gOf_prime X p⟩
  have hsplit : {w : IsDedekindDomain.HeightOneSpectrum (𝓞 X.B.I.E) |
      ((gOf p : ℕ) : 𝓞 X.B.I.E) ∈ w.asIdeal}.ncard = Module.finrank ℚ X.B.I.E := by
    unfold gOf
    split_ifs
    · exact MassDataIdxRes.split_transport X.ιE _ (D.nd.g_split 0)
    · exact MassDataIdxRes.split_transport X.ιE _ (D.nd.g_split 1)
  obtain ⟨he, hf⟩ := MassDataIdxRes.locDeg_one_below (F := X.B.I.F) (E := X.B.I.E) (gOf p) hsplit p.1 hmem
  obtain ⟨_, hnot⟩ := MassDataIdxRes.arith_of_loc (gOf p) p.1 hmem he hf
  have hvg : Valued.v (((gOf p : ℕ) : p.1.adicCompletionIntegers X.B.I.F) : p.1.adicCompletion X.B.I.F) =
      p.1.intValuation ((gOf p : ℕ) : 𝓞 X.B.I.F) := by
    have e : (((gOf p : ℕ) : p.1.adicCompletionIntegers X.B.I.F) : p.1.adicCompletion X.B.I.F) =
        (((gOf p : ℕ) : X.B.I.F) : p.1.adicCompletion X.B.I.F) := by
      first
        | rfl
        | exact (map_natCast (algebraMap X.B.I.F (p.1.adicCompletion X.B.I.F)) (gOf p)).symm
        | norm_cast
        | simp
    rw [e, IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
      ← map_natCast (algebraMap (𝓞 X.B.I.F) X.B.I.F) (gOf p),
      IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
  have hle1 : p.1.intValuation ((gOf p : ℕ) : 𝓞 X.B.I.F) ≤ WithZero.exp (-1 : ℤ) := by
    have := (IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem p.1
      ((gOf p : ℕ) : 𝓞 X.B.I.F) 1).2 (by simpa using hmem)
    simpa using this
  have hgt2 : WithZero.exp (-2 : ℤ) < p.1.intValuation ((gOf p : ℕ) : 𝓞 X.B.I.F) := by
    by_contra hc
    push_neg at hc
    exact hnot ((IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem p.1
      ((gOf p : ℕ) : 𝓞 X.B.I.F) 2).1 (by simpa using hc))
  have hge1 : WithZero.exp (-1 : ℤ) ≤ p.1.intValuation ((gOf p : ℕ) : 𝓞 X.B.I.F) := by
    have := exp_add_one_le_of_exp_lt _ (-2) hgt2
    norm_num at this
    exact this
  have hg0 : (((gOf p : ℕ) : p.1.adicCompletionIntegers X.B.I.F) : p.1.adicCompletion X.B.I.F) ≠ 0 := by
    intro h
    have h' := hvg
    rw [h, map_zero] at h'
    exact (lt_of_le_of_lt zero_le' hgt2).ne' h'.symm
  apply le_antisymm
  · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, ReciprocityTheory.Aut.mem_maxIdeal_iff, hvg]
    refine lt_of_le_of_lt hle1 ?_
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
    norm_num
  · intro x hx
    rw [ReciprocityTheory.Aut.mem_maxIdeal_iff] at hx
    rw [Ideal.mem_span_singleton]
    have hx1 : Valued.v (x : p.1.adicCompletion X.B.I.F) ≤ WithZero.exp (-1 : ℤ) := by
      have := le_exp_sub_one_of_lt_exp' _ 0 (by rwa [WithZero.exp_zero])
      norm_num at this
      exact this
    have hq : Valued.v ((x : p.1.adicCompletion X.B.I.F) /
        (((gOf p : ℕ) : p.1.adicCompletionIntegers X.B.I.F) : p.1.adicCompletion X.B.I.F)) ≤ 1 := by
      rw [map_div₀, hvg, div_le_one₀ (lt_of_le_of_lt zero_le' hgt2)]
      exact hx1.trans hge1
    refine ⟨⟨(x : p.1.adicCompletion X.B.I.F) /
        (((gOf p : ℕ) : p.1.adicCompletionIntegers X.B.I.F) : p.1.adicCompletion X.B.I.F),
      (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 hq⟩, ?_⟩
    apply Subtype.ext
    show (x : p.1.adicCompletion X.B.I.F) =
      (((gOf p : ℕ) : p.1.adicCompletionIntegers X.B.I.F) : p.1.adicCompletion X.B.I.F) *
        ((x : p.1.adicCompletion X.B.I.F) /
          (((gOf p : ℕ) : p.1.adicCompletionIntegers X.B.I.F) : p.1.adicCompletion X.B.I.F))
    field_simp

theorem imA_gOth_unit (p : TypX X) : IsUnit ((gOth X p : ℕ) : p.1.adicCompletionIntegers X.B.I.F) := by
  by_contra hnu
  have hm : ((gOth X p : ℕ) : p.1.adicCompletionIntegers X.B.I.F) ∈
      IsLocalRing.maximalIdeal (p.1.adicCompletionIntegers X.B.I.F) :=
    (IsLocalRing.mem_maximalIdeal _).2 (mem_nonunits_iff.2 hnu)
  rw [← imA_span_g_max X p, Ideal.mem_span_singleton] at hm
  have hc : IsCoprime ((gOf p : ℕ) : p.1.adicCompletionIntegers X.B.I.F)
      ((gOth X p : ℕ) : p.1.adicCompletionIntegers X.B.I.F) := by
    have hz : IsCoprime ((gOf p : ℕ) : ℤ) ((gOth X p : ℕ) : ℤ) :=
      Nat.isCoprime_iff_coprime.2 (gOf_coprime_gOth X p)
    simpa using hz.map (Int.castRingHom (p.1.adicCompletionIntegers X.B.I.F))
  have hu : IsUnit ((gOf p : ℕ) : p.1.adicCompletionIntegers X.B.I.F) := hc.isUnit_of_dvd' dvd_rfl hm
  have htop := (IsLocalRing.maximalIdeal.isMaximal (p.1.adicCompletionIntegers X.B.I.F)).ne_top
  rw [← imA_span_g_max X p, Ne, Ideal.span_singleton_eq_top] at htop
  exact htop hu

theorem imA_span_Bg (p : TypX X) :
    Ideal.span {((X.B.g : ℕ) : p.1.adicCompletionIntegers X.B.I.F)} =
      Ideal.span {((gOf p : ℕ) : p.1.adicCompletionIntegers X.B.I.F)} := by
  rw [imA_g_eq_mul X p, Nat.cast_mul]
  exact Ideal.span_singleton_mul_right_unit (imA_gOth_unit X p) _

end MassDataIdxSteps
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.ParabolicImageOfBasisAdapted
section
noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge MassDataIdxStIm MassDataIdxRed MassDataIdxSpl Matrix

section Loc

variable {D : D7} (X : HidaSetting D)

def reindex₂ (p : TypX X) (Q : GL (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (FpX X p)) : GL (Fin X.B.I.n) (FpX X p) :=
  Units.map (Matrix.reindexAlgEquiv (FpX X p) (FpX X p) (idxEquiv X).symm).toMonoidHom Q

def StLatGLx (p : TypX X) (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p)
    (Q : GL (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (FpX X p)) : Prop :=
  ∀ K : Subgroup (HAp X p), (K : Set (HAp X p)) = KvX X p →
    ∃ ψ : K →* GL (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Op X p), Function.Surjective ψ ∧
      (∀ x : K, (∀ i j, ((ψ x : Matrix (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Op X p))
        - 1) i j ∈ Ideal.span {((gOf p : ℕ) : Op X p)}) ↔ (x : HAp X p) ∈ KgX X p) ∧
      ∀ x : K, ((glRed (algebraMap (Op X p) (FpX X p)) (ψ x) : GL (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (FpX X p)) :
          Matrix (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (FpX X p)) =
        ((Q⁻¹ : GL (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (FpX X p)) :
          Matrix (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (FpX X p)) *
          Matrix.reindex (idxEquiv X) (idxEquiv X) (cmp1 X.B.I.cm.sig X.B.I.J θ (x : HAp X p)) *
          (Q : Matrix (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (FpX X p))

end Loc

def LatCoreX : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (p : TypX X) (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p),
    IsSplitEquiv X p θ → ∀ Q, LatBasis X p θ (reindex₂ X p Q) → StLatGLx X p θ Q

section Loc2

variable {D : D7} (X : HidaSetting D)

def StAdaptQ (u : D.what₂.Word) (p : TypX X) : Prop :=
  ∃ θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p, IsSplitEquiv X p θ ∧
    ∃ (Q : GL (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (FpX X p)) (l : Fin (D.R.rS + 1) → FpX X p), (∀ b, l b ≠ 0) ∧
      (∀ b, ((Q⁻¹ : GL (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (FpX X p)) :
          Matrix (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (FpX X p)) *ᵥ
        (pr1 θ (ratV (F := X.B.I.F) (FpX X p) (F0 (frameOf X u) b)) ∘ (idxEquiv X).symm) = Pi.single (pe b) 1) ∧
      (∀ b, (Q : Matrix (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (FpX X p))ᵀ *ᵥ
        ((Matrix.reindex (idxEquiv X) (idxEquiv X) (jm1 X.B.I.J θ))ᵀ *ᵥ
          (pr2 θ (ratV (F := X.B.I.F) (FpX X p) (F0 (frameOf X u) b)) ∘ (idxEquiv X).symm)) =
        l b • Pi.single (pf b) 1) ∧
      LatBasis X p θ (reindex₂ X p Q)

theorem stAdaptB_of (hC : LatCoreX) (u : D.what₂.Word) (p : TypX X) (h : StAdaptQ X u p) : StAdaptB X u p := by
  obtain ⟨θ, hθ, Q, l, hl, h1, h2, hL⟩ := h
  have hG := hC X p θ hθ Q hL
  let K : Subgroup (HAp X p) :=
    { carrier := KvX X p
      mul_mem' := by
        intro a b ha hb
        simp only [KvX, Formalism.L2.SG.TypedSets.Kv, Set.mem_setOf_eq] at ha hb ⊢
        exact Subgroup.mul_mem _ ha hb
      one_mem' := by
        simp only [KvX, Formalism.L2.SG.TypedSets.Kv, Set.mem_setOf_eq]
        exact Subgroup.one_mem _
      inv_mem' := by
        intro a ha
        simp only [KvX, Formalism.L2.SG.TypedSets.Kv, Set.mem_setOf_eq] at ha ⊢
        exact Subgroup.inv_mem _ ha }
  obtain ⟨ψ, hψs, hψ1, hψ2⟩ := hG K rfl
  exact ⟨θ, hθ, idxEquiv X, Q, l, hl, h1, h2, K, rfl, ψ, hψs, hψ1, hψ2⟩

theorem parabolic_image_of_basis_adapted (hC : LatCoreX) (u : D.what₂.Word) (p : TypX X) (h : StAdaptQ X u p) :
    ParabolicReductionImage X u p :=
  parabolic_image_of_adapted X u p (stAdaptB_of X hC u p h)

end Loc2

end MassDataIdxSteps
end
end

