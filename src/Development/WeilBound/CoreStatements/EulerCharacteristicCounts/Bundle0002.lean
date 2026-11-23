module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.WachCoordinates
public import Formalism.SharpRestriction.LevelLetterCocycles.PairedCharacterCondition
public import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypes
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0013
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0005
public import Development.AutomorphicSpectrum.Definitions.NonGaloisLines.TopLine
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.H2EquivOfTorsionCharacter
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0246
public import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.ExistsPerfectCharacterQuotient
public import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.Bundle0002
public import Development.WeilBound.CoreStatements.EulerCharacteristicCounts.CardH0TwistedDual
public import Development.WeilBound.CoreStatements.EulerCharacteristicCounts.Bundle0001
public import Formalism.GaloisCohomology.LocalTateDualityK
public import GroundTheory.ProfiniteCohomology.LocalTateDuality.TensorHomDualRepRootsOfUnityIsoCartierPairing

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.EulerCharacteristicCounts.EquivariantB
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module GlobalTheory.CompanionTheory.LocDual

namespace PositivityTheory.LocalTateOrthogonality.Bk.Eul

section Act

variable {G : Type} [Group G] {Qp LL O V : Type} [Field Qp] [Field LL] [Algebra Qp LL] [CommRing O]
  [Algebra O LL] [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] [Module O V]
  [IsScalarTower O LL V] {ρ : Representation LL G V}

theorem actQ_one' (L : Lattice (O := O) ρ) (I : Submodule O ↥L.T) (hI : StableSub L I)
    (m : ↥L.T ⧸ I) : actQ L I hI 1 m = m := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ m
  change Submodule.Quotient.mk (actT L 1 x) = _
  congr 1
  apply Subtype.ext
  change ρ 1 (x : V) = x
  simp

theorem actQ_mul' (L : Lattice (O := O) ρ) (I : Submodule O ↥L.T) (hI : StableSub L I)
    (g h : G) (m : ↥L.T ⧸ I) : actQ L I hI (g * h) m = actQ L I hI g (actQ L I hI h m) := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ m
  change Submodule.Quotient.mk (actT L (g * h) x) = Submodule.Quotient.mk (actT L g (actT L h x))
  congr 1
  apply Subtype.ext
  change ρ (g * h) (x : V) = ρ g (ρ h x)
  simp [Module.End.mul_apply]

end Act

theorem psi_unit {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] (ι : ℤ_[l] →+* O) (J : Ideal O)
    (n : ℕ) (hN : ((l ^ n : ℕ) : O) ∈ J) (ψ : (O ⧸ J) →+ ZMod (l ^ n)) (u : ℤ_[l]) (p : O) :
    ψ (Ideal.Quotient.mk J (ι u * p)) = PadicInt.toZModPow n u * ψ (Ideal.Quotient.mk J p) := by
  have hl : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  set m : ℕ := (PadicInt.toZModPow n u : ZMod (l ^ n)).val with hm
  have hmc : ((m : ℕ) : ZMod (l ^ n)) = PadicInt.toZModPow n u := ZMod.natCast_zmod_val _
  have hk : u - (m : ℤ_[l]) ∈ Ideal.span {(l : ℤ_[l]) ^ n} := by
    rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_natCast, hmc, sub_self]
  obtain ⟨v, hv⟩ := Ideal.mem_span_singleton'.1 hk
  have hu : u = (m : ℤ_[l]) + v * (l : ℤ_[l]) ^ n := by rw [hv]; ring
  have h2 : Ideal.Quotient.mk J (ι u * p) = m • Ideal.Quotient.mk J p := by
    rw [← map_nsmul, Ideal.Quotient.eq]
    have : ι u * p - m • p = (ι v * p) * ((l ^ n : ℕ) : O) := by
      rw [hu]
      simp only [map_add (f := _), map_mul, map_pow, map_natCast, nsmul_eq_mul, Nat.cast_pow]
      ring
    rw [this]
    exact J.mul_mem_left _ hN
  rw [h2, map_nsmul, nsmul_eq_mul, hmc]

theorem exists_pair {O W W' : Type} [CommRing O] [AddCommGroup W] [Module O W] [AddCommGroup W']
    [Module O W'] (J : Ideal O) (N : ℕ) (B : W →ₗ[O] W' →ₗ[O] (O ⧸ J)) (ψ₀ : (O ⧸ J) →+ ZMod N)
    (hψ : ∀ x, (∀ o, ψ₀ (o * x) = 0) → x = 0) (hBl : ∀ x, (∀ y, B x y = 0) → x = 0)
    (hBr : ∀ y, (∀ x, B x y = 0) → y = 0) :
    ∃ Pb : W →+ W' →+ ZMod N, (∀ x y, Pb x y = ψ₀ (B x y)) ∧ (∀ x, (∀ y, Pb x y = 0) → x = 0) ∧
      ∀ y, (∀ x, Pb x y = 0) → y = 0 := by
  have hsm : ∀ (o : O) (b : O ⧸ J), Ideal.Quotient.mk J o * b = o • b := fun o b => by
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    rw [← map_mul]
    rfl
  refine ⟨AddMonoidHom.mk' (fun x => ψ₀.comp (B x).toAddMonoidHom) (fun x y => by
    ext z
    simp), fun _ _ => rfl, fun x hx => hBl x fun y => hψ _ fun o => ?_,
    fun y hy => hBr y fun x => hψ _ fun o => ?_⟩
  · obtain ⟨o, rfl⟩ := Ideal.Quotient.mk_surjective o
    rw [hsm, ← map_smul]
    exact hx _
  · obtain ⟨o, rfl⟩ := Ideal.Quotient.mk_surjective o
    rw [hsm, ← LinearMap.smul_apply, ← map_smul]
    exact hy _

theorem quot_killed {O M : Type} [CommRing O] [AddCommGroup M] [Module O M] (J : Ideal O) (N : ℕ)
    (hN : (N : O) ∈ J) (m : M ⧸ (J • ⊤ : Submodule O M)) : N • m = 0 := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ m
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, ← Nat.cast_smul_eq_nsmul O]
  exact Submodule.smul_mem_smul hN trivial

theorem final_count (h1 w z h0 h0' q a d : ℕ) (hw : 0 < w) (hq : w = q ^ a)
    (hC : h1 * w = z * h0) (hZ : z = h0' * w ^ (d + 1)) : h1 = h0 * h0' * q ^ (a * d) := by
  apply Nat.eq_of_mul_eq_mul_right hw
  rw [hC, hZ, pow_succ, pow_mul, ← hq]
  ring


end PositivityTheory.LocalTateOrthogonality.Bk.Eul
end

-- bundled from Development.WeilBound.CoreStatements.EulerCharacteristicCounts.GcohDefs
section
open CategoryTheory GroundTheory.ProfCoh ReciprocityTheory.Gal ValuativeRel

namespace PositivityTheory.LocalTateOrthogonality.Gcoh

def SgcRep : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M] (rho : Representation R G M), ContAction rho → ∃ (A : Rep.{0} (ULift.{0} ℤ) G) (_ : IsDiscreteRep A) (e : M ≃+ A.V), ∀ g m, e (rho g m) = A.ρ g (e m)

def Sgc0 : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M] (rho : Representation R G M) (A : Rep.{0} (ULift.{0} ℤ) G) [IsDiscreteRep A] (e : M ≃+ A.V), (∀ g m, e (rho g m) = A.ρ g (e m)) → ∃ e0 : ↥(H0 rho) ≃+ cohomology A 0, ∀ (m : ↥(H0 rho)) (x : cocycles A 0), (∀ s, cochainOf A (cocycleι A 0 x) s = e m.1) → e0 m = cohomologyπ A 0 x

def Sgc1 : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M] (rho : Representation R G M) (A : Rep.{0} (ULift.{0} ℤ) G) [IsDiscreteRep A] (e : M ≃+ A.V), (∀ g m, e (rho g m) = A.ρ g (e m)) → ∃ e1 : H1 rho ≃+ cohomology A 1, (∀ z : ↥(Z1 rho), ∃ x : cocycles A 1, ∀ s, cochainOf A (cocycleι A 1 x) s = e (z.1 (s 0))) ∧ ∀ (z : ↥(Z1 rho)) (x : cocycles A 1), (∀ s, cochainOf A (cocycleι A 1 x) s = e (z.1 (s 0))) → e1 (Submodule.Quotient.mk z) = cohomologyπ A 1 x

def Sgc2 : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M] (rho : Representation R G M) (A : Rep.{0} (ULift.{0} ℤ) G) [IsDiscreteRep A] (e : M ≃+ A.V), (∀ g m, e (rho g m) = A.ρ g (e m)) → ∃ e2 : H2 rho ≃+ cohomology A 2, (∀ z : ↥(Z2 rho), ∃ x : cocycles A 2, ∀ s, cochainOf A (cocycleι A 2 x) s = e (z.1 (s 0, s 1))) ∧ ∀ (z : ↥(Z2 rho)) (x : cocycles A 2), (∀ s, cochainOf A (cocycleι A 2 x) s = e (z.1 (s 0, s 1))) → e2 (Submodule.Quotient.mk z) = cohomologyπ A 2 x

def Sgcn : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M] (rho : Representation R G M) (A : Rep.{0} (ULift.{0} ℤ) G) [IsDiscreteRep A] (e : M ≃+ A.V), (∀ g m, e (rho g m) = A.ρ g (e m)) → ∀ n : ℕ, Nonempty (Hn rho n ≃+ cohomology A n)

def SgcField : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)), FiniteDimensional ℚ_[l] K → IsSepClosure ↥K (PadicAlgCl l) ∧ ∃ (_ : ValuativeRel ↥K) (t : TopologicalSpace ↥K), @IsNonarchimedeanLocalField ↥K _ _ t ∧ ∀ m : ℕ, Nat.card (𝒪[↥K] ⧸ Ideal.span {((l ^ m : ℕ) : 𝒪[↥K])}) = (l ^ m) ^ Module.finrank ℚ_[l] ↥K

def SgcMu : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) (r : ℕ), ∃ e : ZMod (l ^ r) ≃+ (galRootsOfUnity.{0} ↥K (PadicAlgCl l) (l ^ r)).V, ∀ (g : Formalism.GaloisCohomology.GK l K) (m : ZMod (l ^ r)), e ((Formalism.GaloisCohomology.cycK l K r g : ZMod (l ^ r)) * m) = (galRootsOfUnity.{0} ↥K (PadicAlgCl l) (l ^ r)).ρ g (e m)

end PositivityTheory.LocalTateOrthogonality.Gcoh
end

