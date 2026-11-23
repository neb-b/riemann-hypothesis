module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Bundle0025
public import ReciprocityTheory.Automorphisms.Bundle0001
public import ReciprocityTheory.ResidueCardinality.ArtinOntoB
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Bundle0002

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocDensHIL
section
noncomputable section

namespace PI.VolStabS

namespace IdxLW

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsLocalRing

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

theorem index_maxIdeal :
    (maximalIdeal (v.adicCompletionIntegers F)).toAddSubgroup.index = Nat.card (𝓞 F ⧸ v.asIdeal) := by
  rw [← ReciprocityTheory.Bridge.ResidueFieldCardinality.card_residue v]
  rfl

variable {E : Type} [Field E] [Algebra F E] {d : ℕ} (b : Module.Basis (Fin d) F E) (a M : ℕ)

def crdL : latSub b v a M →+ (Fin a × Fin M × Fin d → v.adicCompletionIntegers F) where
  toFun x q := ⟨(Algebra.TensorProduct.basis (Fv F v) b).repr ((x : Fin a → Fin M → Fv F v ⊗[F] E)
    q.1 q.2.1) q.2.2, x.2 q.1 q.2.1 q.2.2⟩
  map_zero' := by
    funext q
    apply Subtype.ext
    simp
  map_add' x y := by
    funext q
    apply Subtype.ext
    simp

theorem crdL_surj : Function.Surjective (crdL v b a M) := by
  intro c
  let x : Fin a → Fin M → Fv F v ⊗[F] E := fun i j =>
    (Algebra.TensorProduct.basis (Fv F v) b).repr.symm
      (Finsupp.equivFunOnFinite.symm fun k => (c (i, j, k) : Fv F v))
  have hx : ∀ i j k, (Algebra.TensorProduct.basis (Fv F v) b).repr (x i j) k = c (i, j, k) := by
    intro i j k
    simp [x]
  refine ⟨⟨x, fun i j k => by rw [hx]; exact (c (i, j, k)).2⟩, ?_⟩
  funext q
  apply Subtype.ext
  exact hx q.1 q.2.1 q.2.2

theorem crd_smul' (s : Fv F v) (y : Fv F v ⊗[F] E) (k : Fin d) :
    (Algebra.TensorProduct.basis (Fv F v) b).repr (s • y) k =
      s * (Algebra.TensorProduct.basis (Fv F v) b).repr y k := by
  simp [map_smul, Finsupp.smul_apply, smul_eq_mul]

theorem addSubgroupOf_eq :
    (lamF b v a M 0).addSubgroupOf (latSub b v a M) =
      (AddSubgroup.pi Set.univ fun _ : Fin a × Fin M × Fin d =>
        (maximalIdeal (v.adicCompletionIntegers F)).toAddSubgroup).comap (crdL v b a M) := by
  have hv := unifV_val v
  have h0 := (unifV_spec v).1
  ext x
  rw [AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_comap, AddSubgroup.mem_pi]
  simp only [Set.mem_univ, true_implies, Submodule.mem_toAddSubgroup, ReciprocityTheory.Aut.mem_maxIdeal_iff]
  constructor
  · intro hx q
    simp only [lamF, mem_smulSub, zero_add, pow_one] at hx
    obtain ⟨p, hp, hpx⟩ := hx
    show Valued.v ((Algebra.TensorProduct.basis (Fv F v) b).repr
      ((x : Fin a → Fin M → Fv F v ⊗[F] E) q.1 q.2.1) q.2.2) < 1
    rw [← hpx]
    simp only [Pi.smul_apply]
    rw [crd_smul', map_mul, hv]
    have hp' : Valued.v ((Algebra.TensorProduct.basis (Fv F v) b).repr (p q.1 q.2.1) q.2.2) ≤ 1 := by
      have h := hp q.1 q.2.1 q.2.2
      rwa [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers] at h
    calc WithZero.exp (-1 : ℤ) * Valued.v ((Algebra.TensorProduct.basis (Fv F v) b).repr
          (p q.1 q.2.1) q.2.2) ≤ WithZero.exp (-1 : ℤ) * 1 := by gcongr
      _ < 1 := by rw [mul_one]; decide
  · intro hx
    simp only [lamF, mem_smulSub, zero_add, pow_one]
    refine ⟨(unifV v)⁻¹ • (x : Fin a → Fin M → Fv F v ⊗[F] E), ?_, ?_⟩
    · intro i j k
      rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
      simp only [Pi.smul_apply]
      rw [crd_smul', map_mul, map_inv₀, hv]
      have := ReciprocityTheory.Aut.val_le_exp_neg_one_of_lt_one v (hx (i, j, k))
      calc (WithZero.exp (-1 : ℤ))⁻¹ * Valued.v ((Algebra.TensorProduct.basis (Fv F v) b).repr
            ((x : Fin a → Fin M → Fv F v ⊗[F] E) i j) k)
          ≤ (WithZero.exp (-1 : ℤ))⁻¹ * WithZero.exp (-1 : ℤ) := by gcongr; exact this
        _ = 1 := inv_mul_cancel₀ (WithZero.exp_ne_zero)
    · rw [smul_smul, mul_inv_cancel₀ h0, one_smul]

end IdxLW

open IdxLW

theorem idxL_holds : IdxL := by
  intro F E _ _ _ _ _ σ hCM M J hJ _ _ a _ _ X0 hT _ d b v
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  have hd : d = 2 := by
    have := Module.finrank_eq_card_basis b
    rw [hCM.2.2.1, Fintype.card_fin] at this
    exact this.symm
  unfold AddSubgroup.relIndex
  rw [addSubgroupOf_eq, AddSubgroup.index_comap_of_surjective _ (crdL_surj v b a M),
    AddSubgroup.index_pi]
  simp only [index_maxIdeal, Finset.prod_const, Finset.card_univ, Fintype.card_prod,
    Fintype.card_fin]
  subst hd
  ring_nf

end PI.VolStabS
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocDensIdxH
section
noncomputable section

namespace PI.VolStabS

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.VolFromSW
  IsLocalRing

namespace IdxHW

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {d : ℕ}
  (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (σ : E →ₐ[F] E) (a : ℕ)

def crdS (S : HermR (Fv F v) σ a) (i j : Fin a) (k : Fin d) : Fv F v :=
  (Algebra.TensorProduct.basis (Fv F v) b).repr ((S : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j) k

theorem mem_hermO_iff (S : HermR (Fv F v) σ a) :
    S ∈ hermO b v σ a ↔ ∀ i j k, crdS b v σ a S i j k ∈ v.adicCompletionIntegers F := Iff.rfl

theorem crdS_add (S T : HermR (Fv F v) σ a) (i j : Fin a) (k : Fin d) :
    crdS b v σ a (S + T) i j k = crdS b v σ a S i j k + crdS b v σ a T i j k := by
  simp [crdS, Matrix.add_apply, map_add (f := _)]

theorem crdS_smul (t : Fv F v) (S : HermR (Fv F v) σ a) (i j : Fin a) (k : Fin d) :
    crdS b v σ a (t • S) i j k = t * crdS b v σ a S i j k := by
  simp only [crdS, coe_hermSMul, Matrix.smul_apply, map_smul, Finsupp.smul_apply, smul_eq_mul]

def redH : (hermO b v σ a) →+
    (Fin a → Fin a → Fin d → ResidueField (v.adicCompletionIntegers F)) where
  toFun S i j k := residue _ ⟨crdS b v σ a S i j k, (mem_hermO_iff b v σ a S).1 S.2 i j k⟩
  map_zero' := by
    funext i j k
    have : crdS b v σ a (0 : HermR (Fv F v) σ a) i j k = 0 := by simp [crdS]
    simp only [ZeroMemClass.coe_zero, this, Pi.zero_apply]
    rw [show (⟨0, _⟩ : v.adicCompletionIntegers F) = 0 from rfl, map_zero]
  map_add' S T := by
    funext i j k
    simp only [Pi.add_apply, ← map_add (f := _)]
    congr 1
    ext
    simp [crdS_add]

theorem unifV_ne_zero : unifV v ≠ 0 := by
  intro h
  have := unifV_val v
  rw [h, map_zero] at this
  exact WithZero.zero_ne_coe this

theorem val_of_res (x : v.adicCompletionIntegers F) (h : residue _ x = 0) :
    Valued.v (x : Fv F v) ≤ WithZero.exp (-1 : ℤ) :=
  ReciprocityTheory.Aut.val_le_exp_neg_one_of_lt_one v
    ((ReciprocityTheory.Aut.mem_maxIdeal_iff v x).1 ((residue_eq_zero_iff x).1 h))

theorem res_of_val (x : v.adicCompletionIntegers F) (h : Valued.v (x : Fv F v) < 1) :
    residue _ x = 0 :=
  (residue_eq_zero_iff x).2 ((ReciprocityTheory.Aut.mem_maxIdeal_iff v x).2 h)

theorem ker_redH :
    (redH b v σ a).ker = (hF b v σ a 0).addSubgroupOf (hermO b v σ a) := by
  ext S
  rw [AddMonoidHom.mem_ker, AddSubgroup.mem_addSubgroupOf]
  have hπ := unifV_val v
  have hπ0 := unifV_ne_zero v
  constructor
  · intro h
    have hc : ∀ i j k, Valued.v (crdS b v σ a S i j k) ≤ WithZero.exp (-1 : ℤ) := by
      intro i j k
      have h1 : residue _ (⟨crdS b v σ a S i j k, (mem_hermO_iff b v σ a S).1 S.2 i j k⟩ :
          v.adicCompletionIntegers F) = 0 := congrFun (congrFun (congrFun h i) j) k
      have h2 := val_of_res v _ h1
      exact h2
    refine (mem_smulSub _ _ _).2 ⟨(unifV v)⁻¹ • (S : HermR (Fv F v) σ a), ?_, ?_⟩
    · refine (mem_hermO_iff b v σ a _).2 fun i j k => ?_
      rw [crdS_smul, HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, map_inv₀, hπ]
      calc (WithZero.exp (-1 : ℤ))⁻¹ * Valued.v (crdS b v σ a S i j k)
          ≤ (WithZero.exp (-1 : ℤ))⁻¹ * WithZero.exp (-1 : ℤ) := mul_le_mul_right (hc i j k) _
        _ = 1 := inv_mul_cancel₀ (WithZero.exp_ne_zero)
    · rw [zero_add, pow_one, smul_smul, mul_inv_cancel₀ hπ0, one_smul]
  · intro h
    obtain ⟨p, hp, hpS⟩ := (mem_smulSub _ _ _).1 h
    funext i j k
    have hlt : Valued.v (crdS b v σ a S i j k) < 1 := by
      rw [← hpS, zero_add, pow_one, crdS_smul, map_mul, hπ]
      have hp1 : Valued.v (crdS b v σ a p i j k) ≤ 1 :=
        (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 ((mem_hermO_iff b v σ a p).1 hp i j k)
      calc WithZero.exp (-1 : ℤ) * Valued.v (crdS b v σ a p i j k) ≤ WithZero.exp (-1 : ℤ) * 1 :=
            mul_le_mul_right hp1 _
        _ < 1 := by
          rw [mul_one, ← WithZero.exp_zero, WithZero.exp_lt_exp]
          norm_num
    have h3 := res_of_val v ⟨crdS b v σ a S i j k, (mem_hermO_iff b v σ a S).1 S.2 i j k⟩ hlt
    exact h3

end IdxHW

end PI.VolStabS
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocDensVolDone
section
namespace PI.VolStabS

theorem volAA_holds : VolAA := volAA_of_lift chLift_holds

end PI.VolStabS
end

