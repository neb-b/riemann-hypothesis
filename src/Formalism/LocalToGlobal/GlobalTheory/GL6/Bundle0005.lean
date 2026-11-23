module

public import Formalism.LocalToGlobal.GlobalTheory.GL6.BwAValIntegralNonneg
public import Formalism.LocalToGlobal.GlobalTheory.GL6.Bundle0004

@[expose] public section

-- bundled from Formalism.LocalToGlobal.GlobalTheory.GL6.LatticeInclusionOfDecompGlob
section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Classical

variable (D : D7) (u : D.what₂.Word)

theorem bwA_natW_anti {N : ℕ} (lam : DomWeight N) : Antitone lam.natW := by
  first
    | exact lam.natW_anti
    | exact lam.anti
    | exact lam.antitone
    | (intro a b hab
       simp only [DomWeight.natW]
       first
         | (have := lam.anti hab; omega)
         | (have := lam.dom hab; omega)
         | (have := lam.antitone hab; omega)
         | (have := lam.mono hab; omega)
         | (have := lam.2 hab; omega)
         | (have := lam.dom a b hab; omega)
         | (have := lam.2 a b hab; omega)
         | (have := lam.w_anti hab; omega)
         | (have := lam.anti a b hab; omega))

theorem bwA_val_locInt (w : D.what₂.places.Pl) (σ : D.host.E →+* D.host.E) (y : D.host.E) (s : ℕ)
    (hs : ¬ D.what₂.places.resChar w ∣ s) (hy : (s : D.host.E) * y ∈ (algebraMap (NumberField.RingOfIntegers D.host.E) D.host.E).range) :
    (0 : WithTop ℤ) ≤ D.what₂.places.val w (D.embE (σ y)) := by
  obtain ⟨a, ha⟩ := hy
  have hint : IsIntegral ℤ (D.embE (σ (algebraMap (NumberField.RingOfIntegers D.host.E) D.host.E a))) :=
    (NumberField.RingOfIntegers.isIntegral_coe a).map ((D.embE.comp σ).toIntAlgHom)
  have h0 := bwA_val_integral_nonneg D.what₂.places w _ hint
  rw [ha, map_mul, map_mul, map_natCast, map_natCast, AddValuation.map_mul,
    bwA_val_nat_eq_zero D.what₂.places w s hs, zero_add] at h0
  exact h0

def bwA_EO (O : Subring ℂ) (N : ℕ) : Submonoid (Matrix (Fin N) (Fin N) ℂ) :=
  Submonoid.closure {g | ∃ (a b : Fin N) (c : ℂ), c ∈ O ∧ g = 1 + Matrix.single b a c}

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases
end
end

-- bundled from Formalism.LocalToGlobal.GlobalTheory.GL6.RndLinkAdmTOf
section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

open Formalism.BasicNotions Formalism.L2.Forms NumberField IsDedekindDomain Matrix Formalism.UG

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}

theorem rnd_cls (S : StepLevel F E σ J T f bad) (γ0 : GL (Fin n) E) (hγ0 : γ0 ∈ UJ (σ : E →+* E) J)
    (y1 y2 : UPts σ J (FiniteAdeleRing (𝓞 F) F)) (k : S.U)
    (h : bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ0 * y1.1 = y2.1 * k.1) :
    (Quotient.mk'' y1 : Cls S) = Quotient.mk'' y2 := by
  have hkU : k.1 ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F) := ((S.U_eq k.1).1 k.2).1
  have e : bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ0 = y2.1 * k.1 * y1.1⁻¹ := by
    rw [← h]; group
  have hb : bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ0 ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F) := by
    rw [e]; exact Subgroup.mul_mem _ (Subgroup.mul_mem _ y2.2 hkU) (Subgroup.inv_mem _ y1.2)
  refine (@DoubleCoset.eq _ _ _ _ y1 y2).2 ⟨⟨bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ0, hb⟩,
    ?_, ⟨k.1⁻¹, Subgroup.inv_mem _ hkU⟩, ?_, ?_⟩
  · exact Subgroup.mem_subgroupOf.2 ⟨γ0, hγ0, rfl⟩
  · exact Subgroup.mem_subgroupOf.2 (S.U.inv_mem k.2)
  · apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [h]; group

theorem rnd_chi (S : StepLevel F E σ J T f bad) (v : HeightOneSpectrum (𝓞 F)) (hb : v ∉ bad)
    (η η' : UPts σ J (FiniteAdeleRing (𝓞 F) F))
    (hη : ∀ v', v' ≠ v → bc (prV (E := E) v') η.1 = 1) (hη' : ∀ v', v' ≠ v → bc (prV (E := E) v') η'.1 = 1)
    (κ κ' k : S.U) (hk : k.1 = η.1 * κ.1 * η'.1 * κ'.1) : S.chi k = S.chi κ * S.chi κ' := by
  have key : S.chi ((κ * κ')⁻¹ * k) = 1 := by
    apply S.chi_triv
    intro v'' hv''
    have hne : v'' ≠ v := fun e => hb (e ▸ hv'')
    simp only [Subgroup.coe_mul, InvMemClass.coe_inv, hk, map_mul, map_inv, hη v'' hne, hη' v'' hne, mul_one, one_mul]
    group
  rw [map_mul, map_inv, inv_mul_eq_one] at key
  rw [← key, map_mul]

end Gen

variable {D : D7} {u : D.what₂.Word}



end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases
end
end

