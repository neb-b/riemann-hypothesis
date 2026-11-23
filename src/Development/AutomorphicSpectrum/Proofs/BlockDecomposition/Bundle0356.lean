module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0335
public import Mathlib
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanCriterion.Zj
public import GroundTheory.AutomorphicForms.SupercuspidalCoefficients
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.GKLocal
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipotentDerivatives.DerUnipLeUnipB
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CentredSegments.IrreducibleUnif
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyInterleaving.LInjective
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0050

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StandardBlocksReindexStrictMono
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos

namespace GlobalTheory.CompanionTheory.StdCompat

theorem sum_castLE_eq_sum_filter {s : ℕ} (f : Fin s → ℕ) (c : Fin s) :
    ∑ b : Fin (c : ℕ), f (Fin.castLE c.2.le b) = ∑ j ∈ Finset.univ.filter (· < c), f j := by
  refine Finset.sum_bij (fun b _ => Fin.castLE c.2.le b) ?_ ?_ ?_ ?_
  · intro b _
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, b.2⟩
  · intro x _ y _ h
    exact Fin.castLE_injective _ h
  · intro j hj
    have hj' : (j : ℕ) < c := (Finset.mem_filter.1 hj).2
    exact ⟨⟨j, hj'⟩, Finset.mem_univ _, Fin.ext rfl⟩
  · intro _ _
    rfl

theorem partial_sum_drop_empty {r r' : ℕ} (d : Fin r → ℕ) (o : Fin r' → Fin r)
    (ho : StrictMono o) (hr : ∀ j, d j ≠ 0 → j ∈ Set.range o) (a : Fin r') :
    ∑ b ∈ Finset.univ.filter (· < a), d (o b) = ∑ j ∈ Finset.univ.filter (· < o a), d j := by
  rw [← Finset.sum_image (s := Finset.univ.filter (· < a)) (g := o) (f := d)
    (fun x _ y _ h => ho.injective h)]
  refine Finset.sum_subset ?_ ?_
  · intro j hj
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hj
    have hb' : b < a := (Finset.mem_filter.1 hb).2
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, ho hb'⟩
  · intro j hj hj'
    by_contra hne
    obtain ⟨b, rfl⟩ := hr j hne
    have hlt : o b < o a := (Finset.mem_filter.1 hj).2
    exact hj' (Finset.mem_image.2
      ⟨b, Finset.mem_filter.2 ⟨Finset.mem_univ _, ho.lt_iff_lt.1 hlt⟩, rfl⟩)

theorem stdBlocks_drop_empty : ∀ {r r' N : ℕ} (d : Fin r → ℕ) (hd : ∑ a, d a = N)
    (o : Fin r' → Fin r), StrictMono o → (∀ j, d j ≠ 0 → j ∈ Set.range o) →
    ∀ (hd' : ∑ a, d (o a) = N) (a : Fin r') (t : Fin (d (o a))),
      stdBlocks (fun a => d (o a)) hd' ⟨a, t⟩ = stdBlocks d hd ⟨o a, t⟩ := by
  intro r r' N d hd o ho hr hd' a t
  apply Fin.ext
  have h1 := stdBlocks_val (fun a => d (o a)) hd' a t
  have h2 := stdBlocks_val d hd (o a) t
  have h3 := sum_castLE_eq_sum_filter (fun a => d (o a)) a
  have h4 := sum_castLE_eq_sum_filter d (o a)
  have h5 := partial_sum_drop_empty d o ho hr a
  rw [h1, h2]
  rw [h3, h4, h5]

end GlobalTheory.CompanionTheory.StdCompat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubquotientNontrivialExistsMem
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult

namespace GlobalTheory.CompanionTheory.SubQuotNe

theorem exists_mem_not_mem_of_subQuot_equiv :
    ∀ {M W X : Type} [Group M] [AddCommGroup W] [Module ℂ W] [AddCommGroup X] [Module ℂ X]
      (ρ : Representation ℂ M W) (σ : Representation ℂ M X) (S T : Subrepresentation ρ),
      Nonempty ((subQuot S T).Equiv σ) → Nontrivial X →
        ∃ s ∈ S.toSubmodule, s ∉ T.toSubmodule := by
  intro M W X _ _ _ _ _ ρ σ S T hE hX
  obtain ⟨e⟩ := hE
  by_contra h
  push_neg at h
  have hle : S.toSubmodule ≤ T.toSubmodule := fun s hs => h s hs
  haveI : Subsingleton (S.toSubmodule ⧸ T.toSubmodule.comap S.toSubmodule.subtype) :=
    Submodule.Quotient.subsingleton_iff.mpr (Submodule.comap_subtype_eq_top.mpr hle)
  exact not_subsingleton X e.toLinearEquiv.symm.injective.subsingleton

end GlobalTheory.CompanionTheory.SubQuotNe
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubquotientScalarActionMod
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult

namespace GlobalTheory.CompanionTheory.SubQuotScalar

theorem sub_smul_mem_of_equiv_subQuot :
    ∀ {M W X : Type} [Group M] [AddCommGroup W] [Module ℂ W] [AddCommGroup X] [Module ℂ X]
      (ρ : Representation ℂ M W) (σ : Representation ℂ M X) (S T : Subrepresentation ρ),
      Nonempty ((subQuot S T).Equiv σ) → ∀ (g : M) (c : ℂ), (∀ x, σ g x = c • x) →
        ∀ s ∈ S.toSubmodule, ρ g s - c • s ∈ T.toSubmodule := by
  intro M W X _ _ _ _ _ ρ σ S T he g c hσ s hs
  obtain ⟨e⟩ := he
  have hinj : Function.Injective e.toIntertwiningMap.toLinearMap := e.left_inv.injective
  have key : e.toIntertwiningMap.toLinearMap
        (GlobalTheory.SmGL.subQuot S T g (Submodule.Quotient.mk ⟨s, hs⟩)) =
      e.toIntertwiningMap.toLinearMap (c • Submodule.Quotient.mk ⟨s, hs⟩) := by
    rw [map_smul, ← hσ]
    exact LinearMap.congr_fun (e.toIntertwiningMap.isIntertwining' g) _
  have h2 := hinj key
  have h3 : (Submodule.Quotient.mk ⟨ρ g s, S.2 g hs⟩ :
        ↥S.toSubmodule ⧸ T.toSubmodule.comap S.toSubmodule.subtype) =
      Submodule.Quotient.mk (c • (⟨s, hs⟩ : ↥S.toSubmodule)) := h2
  rw [Submodule.Quotient.eq] at h3
  exact h3

end GlobalTheory.CompanionTheory.SubQuotScalar
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TensorProductDropZeroFactors
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.FineProd.TensorLine

theorem exists_line {G V : Type} [Group G] [Subsingleton G] [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ G V} (hi : ρ.IsIrreducible) : Nonempty (V ≃ₗ[ℂ] ℂ) := by
  have := nontrivial_of_irreducible hi
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  let S : Subrepresentation ρ := ⟨Submodule.span ℂ {v}, fun g w hw => by
    rw [Subsingleton.elim g 1, map_one]; exact hw⟩
  have hvS : v ∈ S.toSubmodule := Submodule.mem_span_singleton_self v
  have hS : S = ⊤ := by
    rcases hi.eq_bot_or_eq_top S with h | h
    · exfalso
      rw [h] at hvS
      exact hv ((Submodule.mem_bot ℂ).1 hvS)
    · exact h
  have htop : ∀ w : V, w ∈ Submodule.span ℂ {v} := fun w => by
    have : w ∈ S.toSubmodule := by
      rw [hS]
      exact (Submodule.mem_top : w ∈ (⊤ : Submodule ℂ V))
    exact this
  refine ⟨(LinearEquiv.ofBijective (LinearMap.toSpanSingleton ℂ V v) ⟨?_, ?_⟩).symm⟩
  · exact LinearMap.ker_eq_bot.1 (LinearMap.ker_toSpanSingleton ℂ hv)
  · intro w
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 (htop w)
    exact ⟨c, by simpa using hc⟩

theorem subsingleton_GL {k : Type} [Field k] {n : ℕ} (h : n = 0) : Subsingleton (GL (Fin n) k) := by
  subst h
  exact ⟨fun a b => Units.ext (Subsingleton.elim _ _)⟩

variable {r r' : ℕ}

abbrev Off (o : Fin r' → Fin r) : Type := {j : Fin r // j ∉ Set.range o}

def blockEquiv (o : Fin r' → Fin r) (ho : Function.Injective o) : Fin r' ⊕ Off o ≃ Fin r :=
  Equiv.ofBijective (Sum.elim o Subtype.val) (by
    constructor
    · rintro (a | a) (b | b) h
      · exact congrArg Sum.inl (ho h)
      · exact absurd ⟨a, h⟩ b.2
      · exact absurd ⟨b, h.symm⟩ a.2
      · exact congrArg Sum.inr (Subtype.ext h)
    · intro j
      by_cases hj : j ∈ Set.range o
      · obtain ⟨a, rfl⟩ := hj
        exact ⟨Sum.inl a, rfl⟩
      · exact ⟨Sum.inr ⟨j, hj⟩, rfl⟩)

variable {X : Fin r → Type} [∀ j, AddCommGroup (X j)] [∀ j, Module ℂ (X j)]


open scoped Classical in
def dropEquiv (o : Fin r' → Fin r) (ho : Function.Injective o) (φ : ∀ c : Off o, X c ≃ₗ[ℂ] ℂ) :
    (⨂[ℂ] j, X j) ≃ₗ[ℂ] ⨂[ℂ] a, X (o a) :=
  (PiTensorProduct.reindex ℂ X (blockEquiv o ho).symm).trans <|
    ((PiTensorProduct.tmulEquivDep ℂ fun i => X (blockEquiv o ho i)).symm).trans <|
      (TensorProduct.congr (LinearEquiv.refl ℂ (⨂[ℂ] a, X (o a)))
        ((PiTensorProduct.congr fun c : Off o => φ c).trans
          (PiTensorProduct.constantBaseRingEquiv (Off o) ℂ).toLinearEquiv)).trans
        (TensorProduct.rid ℂ _)


open scoped Classical in
theorem dropEquiv_tprod (o : Fin r' → Fin r) (ho : Function.Injective o)
    (φ : ∀ c : Off o, X c ≃ₗ[ℂ] ℂ) (x : ∀ j, X j) :
    dropEquiv o ho φ (PiTensorProduct.tprod ℂ x) =
      (∏ c : Off o, φ c (x c)) • PiTensorProduct.tprod ℂ fun a => x (o a) := by
  have h1 : PiTensorProduct.reindex ℂ X (blockEquiv o ho).symm (PiTensorProduct.tprod ℂ x) =
      PiTensorProduct.tprod ℂ fun i => x (blockEquiv o ho i) :=
    PiTensorProduct.reindex_tprod _ _
  have h2 := PiTensorProduct.tmulEquivDep_symm_apply ℂ (fun i => X (blockEquiv o ho i))
    (fun i => x (blockEquiv o ho i))
  have h3 : (PiTensorProduct.congr fun c : Off o => φ c)
      (PiTensorProduct.tprod ℂ fun c : Off o => x c) = PiTensorProduct.tprod ℂ fun c : Off o => φ c (x c) :=
    PiTensorProduct.congr_tprod _ _
  have ht : ((PiTensorProduct.tmulEquivDep ℂ fun i => X (blockEquiv o ho i)).symm
      (PiTensorProduct.reindex ℂ X (blockEquiv o ho).symm (PiTensorProduct.tprod ℂ x)) :
        TensorProduct ℂ (⨂[ℂ] a, X (o a)) (⨂[ℂ] c : Off o, X c)) =
      (PiTensorProduct.tprod ℂ fun a => x (o a)) ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ fun c : Off o => x c) :=
    (congrArg _ h1).trans h2
  show (TensorProduct.rid ℂ _) ((TensorProduct.congr (LinearEquiv.refl ℂ (⨂[ℂ] a, X (o a)))
        ((PiTensorProduct.congr fun c : Off o => φ c).trans
          (PiTensorProduct.constantBaseRingEquiv (Off o) ℂ).toLinearEquiv))
      ((PiTensorProduct.tmulEquivDep ℂ fun i => X (blockEquiv o ho i)).symm
        (PiTensorProduct.reindex ℂ X (blockEquiv o ho).symm (PiTensorProduct.tprod ℂ x)) :
        TensorProduct ℂ (⨂[ℂ] a, X (o a)) (⨂[ℂ] c : Off o, X c))) = _
  rw [ht, TensorProduct.congr_tmul, LinearEquiv.trans_apply, h3, TensorProduct.rid_tmul]
  congr 1
  exact PiTensorProduct.constantBaseRingEquiv_tprod _

theorem piTensor_drop_equiv : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {r r' : ℕ} (y : Fin r → IrrGL (k := k)) (o : Fin r' → Fin r), StrictMono o → (∀ j, (y j).1 ≠ 0 → j ∈ Set.range o) → Nonempty ((piTensor fun j => (y j).rep).Equiv ((piTensor fun a => (y (o a)).rep).comp (GlobalTheory.CompanionTheory.FineProd.dropHom (k := k) (fun j => (y j).1) o) : Representation ℂ (Levi k fun j => Fin (y j).1) _)) := by
  intro k _ _ _ _ r r' y o ho hy
  have hz : ∀ c : Off o, (y c).1 = 0 := fun c => by
    by_contra h
    exact c.2 (hy c h)
  have hφ : ∀ c : Off o, Nonempty ((y c).2.rep.V ≃ₗ[ℂ] ℂ) := fun c => by
    haveI := subsingleton_GL (k := k) (hz c)
    exact exists_line (y c).2.rep.irr
  let φ : ∀ c : Off o, (y c).2.rep.V ≃ₗ[ℂ] ℂ := fun c => (hφ c).some
  refine ⟨Representation.Equiv.mk (dropEquiv o ho.injective φ) fun g => ?_⟩
  refine PiTensorProduct.ext (MultilinearMap.ext fun x => ?_)
  have hc : ∀ c : Off o, (y c).rep (g c) (x c) = x c := fun c => by
    haveI := subsingleton_GL (k := k) (hz c)
    rw [Subsingleton.elim (g c) 1, map_one]
    rfl
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    piTensor_tprod, dropEquiv_tprod, hc, map_smul]
  congr 1
  exact (piTensor_tprod (fun a => (y (o a)).rep) (fun a => g (o a)) (fun a => x (o a))).symm

end GlobalTheory.CompanionTheory.FineProd.TensorLine

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TransposeInverseInvolutionApply
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos
open scoped Matrix

namespace GlobalTheory.CompanionTheory.ThetaInv

theorem thetaW_val_apply {A : Type} [CommRing A] (N : ℕ) (g : GL (Fin N) A) (i j : Fin N) :
    (thetaW A N g).1 i j = (g⁻¹).1 (Fin.rev j) (Fin.rev i) := by
  simp [thetaW, invT, Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply, Matrix.submatrix,
    Matrix.transpose_apply, Fin.revPerm]

theorem thetaW_thetaW_ring {A : Type} [CommRing A] (N : ℕ) (g : GL (Fin N) A) :
    thetaW A N (thetaW A N g) = g := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [thetaW_val_apply, ← map_inv, thetaW_val_apply, inv_inv, Fin.rev_rev, Fin.rev_rev]

theorem thetaW_thetaW {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (N : ℕ) (g : GL (Fin N) k) :
    thetaW k N (thetaW k N g) = g :=
  thetaW_thetaW_ring N g

end GlobalTheory.CompanionTheory.ThetaInv

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedActionSmooth
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir

noncomputable section

namespace GlobalTheory.CompanionTheory.BZMir

def stabSub {M W : Type} [Group M] [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ M W) (w : W) :
    Subgroup M where
  carrier := {m | σ m w = w}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [map_mul, Module.End.mul_apply, hb, ha]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    conv_lhs => rw [← ha]
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

theorem twAct_isSmooth {G M V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group M]
    [TopologicalSpace M] [IsTopologicalGroup M] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (hρ : IsSmooth ρ) (N : Subgroup G) (θ : N →* ℂˣ) (s : M →* G)
    (hsc : Continuous s)
    (hs : ∀ (m : M) (n : N), ∃ h : s m * (n : G) * (s m)⁻¹ ∈ N, θ ⟨_, h⟩ = θ n) :
    IsSmooth (twAct ρ N θ s hs) := by
  intro x
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have hle : ((stabSub ρ v).comap s) ≤ stabSub (twAct ρ N θ s hs) (Submodule.Quotient.mk v) := by
    intro m hm
    change ρ (s m) v = v at hm
    change (twAct ρ N θ s hs) m (Submodule.Quotient.mk v) = Submodule.Quotient.mk v
    exact congrArg (Submodule.Quotient.mk (p := twKer ρ N θ)) hm
  have hop : IsOpen (((stabSub ρ v).comap s : Subgroup M) : Set M) :=
    (hρ v).preimage hsc
  exact Subgroup.isOpen_mono hle hop

end GlobalTheory.CompanionTheory.BZMir
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformizerPowTendstoZero
section
open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel

namespace GlobalTheory.CompanionTheory.UnifPow

theorem valuation_unifU_lt_one (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] : valuation k ((Zls.unifU k : kˣ) : k) < 1 := by
  have hle : valuation k ((Zls.unif k : 𝒪[k]) : k) ≤ 1 := (Zls.unif k).2
  refine lt_of_le_of_ne hle fun h1 => (Zls.irreducible_unif (k := k)).not_isUnit ?_
  exact ((Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one).2 h1

theorem tendsto_unifU_pow : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k],
    Filter.Tendsto (fun n : ℕ => ((Zls.unifU k : kˣ) : k) ^ n) Filter.atTop (nhds 0) := by
  intro k _ _ _ _
  rw [(IsValuativeTopology.hasBasis_nhds_zero' k).tendsto_right_iff]
  intro γ hγ
  have h := valuation_unifU_lt_one k
  have : MulArchimedean (ValueGroupWithZero k) :=
    ValuativeRel.isRankLeOne_iff_mulArchimedean.mp inferInstance
  obtain ⟨n, hn⟩ := exists_pow_lt₀ h (Units.mk0 γ hγ)
  filter_upwards [eventually_ge_atTop n] with m hm
  rw [map_pow]
  exact lt_of_le_of_lt (pow_le_pow_right_of_le_one' h.le hm) hn

end GlobalTheory.CompanionTheory.UnifPow
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentRadicalStdBlocksEq
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult

namespace GlobalTheory.CompanionTheory.ParabolicCompare

theorem unipRad_stdBlocks_eq_unipotentRadical (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) :
    unipRad k (stdBlocks d hd) = GroundTheory.Automorphic.Parabolic.unipotentRadical k N (Zl.JC.blockIdx d hd) := by
  ext g
  rw [GlobalTheory.SmGL.mem_unipRad, GroundTheory.Automorphic.Parabolic.mem_unipotentRadical,
    GroundTheory.Automorphic.Iwasawa.mem_blockUpper, GlobalTheory.SmGL.mem_parab]
  refine and_congr Iff.rfl ⟨fun H i j hij => ?_, fun H a i j => ?_⟩
  · obtain ⟨⟨a, i⟩, rfl⟩ := (stdBlocks d hd).surjective i
    obtain ⟨⟨b, j⟩, rfl⟩ := (stdBlocks d hd).surjective j
    obtain rfl : a = b := by simpa [Zl.JC.blockIdx] using hij
    have := H a i j
    rw [this]
    by_cases e : i = j
    · subst e; simp
    · rw [Matrix.one_apply_ne e, Matrix.one_apply_ne]
      intro h'
      exact e (by simpa using (stdBlocks d hd).injective h')
  · rw [H _ _ (by simp [Zl.JC.blockIdx])]
    by_cases e : i = j
    · subst e; simp
    · rw [Matrix.one_apply_ne e, Matrix.one_apply_ne]
      intro h'
      exact e (by simpa using (stdBlocks d hd).injective h')

end GlobalTheory.CompanionTheory.ParabolicCompare
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ValuationLtOneOfPowTendstoZero
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult

namespace GlobalTheory.CompanionTheory.Val

theorem valuation_lt_one_of_tendsto_pow_zero :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
      ∀ t : kˣ, Filter.Tendsto (fun n : ℕ => (t : k) ^ n) Filter.atTop (nhds 0) →
        ValuativeRel.valuation k (t : k) < 1 := by
  intro k _ _ _ _ t ht
  by_contra hge
  have hge' : 1 ≤ ValuativeRel.valuation k (t : k) := not_lt.mp hge
  have hU : {x : k | ValuativeRel.valuation k x < 1} ∈ nhds (0 : k) :=
    (IsValuativeTopology.hasBasis_nhds_zero' k).mem_of_mem one_ne_zero
  obtain ⟨n, hn⟩ := (ht.eventually hU).exists
  have hn' : ValuativeRel.valuation k ((t : k) ^ n) < 1 := hn
  rw [map_pow] at hn'
  exact absurd hn' (not_lt.mpr (one_le_pow₀ hge'))

end GlobalTheory.CompanionTheory.Val
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WordOccursOfSubquotient
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M

namespace GlobalTheory.CompanionTheory.Words

theorem wd_of_isSubquotient {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {N : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] (π : Representation ℂ (GL (Fin N) k) V) (σ : Representation ℂ (GL (Fin N) k) W)
    (hπ : IsSmooth π) (h : IsSubquotient σ π) (w : List (IrrGL (k := k))) (hw : Wd σ w) : Wd π w := by
  obtain ⟨hd, hne⟩ := hw
  refine ⟨hd, ?_⟩
  exact jhMult_ne_zero_iff.2
    ((jhMult_ne_zero_iff.1 hne).trans (GlobalTheory.JacquetExact.isSubquotient_jac _ hπ h))

end GlobalTheory.CompanionTheory.Words
end

