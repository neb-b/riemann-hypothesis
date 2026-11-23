module

public import Formalism.LocalRingCardinality.SpanPowerMembership.NDLocF

@[expose] public section

noncomputable section

namespace Formalism.BasicNotions.Examples₂.LB

open NumberField IsDedekindDomain Polynomial IsLocalRing Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc

variable {l : ℕ} [hl : Fact l.Prime]

section Emb

variable {F : Type} [Field F] [NumberField F]

def Kphi (φ : F →+* PadicAlgCl l) : IntermediateField ℚ_[l] (PadicAlgCl l) :=
  IntermediateField.adjoin ℚ_[l] (Set.range fun i => φ (Module.finBasis ℚ F i))

instance Kphi_fin (φ : F →+* PadicAlgCl l) : FiniteDimensional ℚ_[l] (Kphi φ) :=
  IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x

theorem phi_mem (φ : F →+* PadicAlgCl l) (x : F) : φ x ∈ Kphi φ := by
  have hx := (Module.finBasis ℚ F).sum_repr x
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← hx, map_sum]
  refine sum_mem (fun i _ => ?_)
  rw [map_rat_smul, Rat.smul_def]
  refine mul_mem ?_ (IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩)
  first
  | exact SubfieldClass.ratCast_mem _ _
  | exact ratCast_mem _ _
  | exact (Kphi φ).toSubfield.ratCast_mem _
  | simp


theorem exists_embAt (w : HeightOneSpectrum (𝓞 F)) (hw : ((l : ℕ) : 𝓞 F) ∈ w.asIdeal) :
    ∃ φ : F →+* PadicAlgCl l, ∀ x : 𝓞 F, x ∈ w.asIdeal ↔ ‖φ (x : F)‖ < 1 := by
  have hA := isPlaceOver_placeOf (AlgebraicClosure F) w
  have hAl : (placeOf (AlgebraicClosure F) w).valuation ((l : ℕ) : AlgebraicClosure F) < 1 := by
    have := (hA ((l : ℕ) : 𝓞 F)).mpr hw
    simpa using this
  haveI : IsAlgClosure ℚ (AlgebraicClosure F) := isAlgClosureQ F (AlgebraicClosure F)
  obtain ⟨j, hj⟩ := exists_emb (l := l) _ hAl
  exact ⟨j.comp (algebraMap F (AlgebraicClosure F)), fun x => by
    rw [← hA x, val_lt_one_iff hj]; rfl⟩

end Emb


section Mu

variable (LL : FinExt l) {N : ℕ} [NeZero N] {ζ : PadicAlgCl l} (hζ : IsPrimitiveRoot ζ N) (hm : ζ ∈ LL.1)


end Mu

end Formalism.BasicNotions.Examples₂.LB
