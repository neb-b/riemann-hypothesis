module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0004
public import Formalism.LocalToGlobal.Columns.BaseLemmas
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0098
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProdAbsNormDivsDvd
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0094
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHeckeCharTrivOnRealSubfieldInfinityType
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0108
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgebraicHeckeCharValuesInNumberField
public import Formalism.LocalToGlobal.Divisibility.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0091
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0103
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.PrimePairSizeCondition
public import Development.AutomorphicArithmetic.PrimeDiscriminants.Bundle0001
public import Development.AutomorphicArithmetic.WeightCongruences.Bundle0001
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle0005
public import Formalism.FrobeniusOrbits.HostThickExists
public import Development.AutomorphicArithmetic.FrobeniusLocalisation.MuSplitsCfacts
public import Development.AutomorphicArithmetic.WeightCongruences.ProdResidueCharNormOneUnitEqOne
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.SchurOrthogonalityIndefiniteUnitaryGroup
public import Formalism.LocalToGlobal.Columns.HeckeInertComm
public import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
public import Formalism.LocalToGlobal.Columns.LocWLemmas
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0039

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EquivOfISupRange
section
open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host GlobalTheory.CuspRep Matrix

namespace GlobalTheory.CuspRep.LocUniq

theorem equiv_of_iSup_range {R M S S' : Type} [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup S] [Module R S]
    [AddCommGroup S'] [Module R S'] [IsSimpleModule R S] [IsSimpleModule R S']
    (h : ∀ x : M, x ∈ ⨆ f : S →ₗ[R] M, LinearMap.range f) (g : S' →ₗ[R] M) (hg : Function.Injective g) :
    Nonempty (S ≃ₗ[R] S') := by
  let s : Set (Submodule R M) := {m | Nonempty (m ≃ₗ[R] S)}
  have : ∀ m : s, IsSimpleModule R m := fun m => m.2.elim fun e => IsSimpleModule.congr e
  have e0 := LinearEquiv.ofInjective g hg
  have : IsSimpleModule R (LinearMap.range g) := IsSimpleModule.congr e0.symm
  have hle : LinearMap.range g ≤ sSup s := fun x _ => by
    refine (iSup_le (a := sSup s) fun f => ?_) (h x)
    rcases LinearMap.injective_or_eq_zero f with hf | rfl
    · exact le_sSup ⟨(LinearEquiv.ofInjective f hf).symm⟩
    · simp
  obtain ⟨m, ⟨e⟩, ⟨e'⟩⟩ := (LinearMap.range g).linearEquiv_of_le_sSup s hle
  exact ⟨(e0.trans (e'.trans e)).symm⟩

section Rep

variable {G V W W' : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup W'] [Module ℂ W']

def isoPart (σ : Representation ℂ G W) (ρ : Representation ℂ G V) : Submodule ℂ V :=
  ⨆ f : σ.IntertwiningMap ρ, LinearMap.range f.toLinearMap

theorem isoPart_act (σ : Representation ℂ G W) (ρ : Representation ℂ G V) (g : G) {x : V} (hx : x ∈ isoPart σ ρ) :
    ρ g x ∈ isoPart σ ρ := by
  refine (iSup_le (a := (isoPart σ ρ).comap (ρ g)) fun f => ?_) hx
  rintro _ ⟨v, rfl⟩
  exact Submodule.mem_iSup_of_mem f ⟨σ g v, LinearMap.congr_fun (f.isIntertwining' g) v⟩

theorem isoPart_comm (σ : Representation ℂ G W) (ρ : Representation ℂ G V) (T : Module.End ℂ V)
    (hT : ∀ g x, T (ρ g x) = ρ g (T x)) {x : V} (hx : x ∈ isoPart σ ρ) : T x ∈ isoPart σ ρ := by
  refine (iSup_le (a := (isoPart σ ρ).comap T) fun f => ?_) hx
  rintro _ ⟨v, rfl⟩
  refine Submodule.mem_iSup_of_mem (⟨T ∘ₗ f.toLinearMap, fun g => LinearMap.ext fun u => ?_⟩ : σ.IntertwiningMap ρ)
    ⟨v, rfl⟩
  exact (congrArg T (LinearMap.congr_fun (f.isIntertwining' g) u)).trans (hT g _)

theorem equiv_of_isoPart (σ : Representation ℂ G W) (σ' : Representation ℂ G W') (ρ : Representation ℂ G V)
    [σ.IsIrreducible] [σ'.IsIrreducible] (h : isoPart σ ρ = ⊤) (f' : σ'.IntertwiningMap ρ) (hf' : f' ≠ 0) :
    Nonempty (σ.Equiv σ') := by
  have hi := (Representation.IsIrreducible.injective_or_eq_zero f').resolve_right hf'
  obtain ⟨e⟩ := equiv_of_iSup_range (R := MonoidAlgebra ℂ G) (S := σ.asModule) (M := ρ.asModule) (fun x => by
    have hx : ρ.asModuleEquiv x ∈ isoPart σ ρ := h ▸ Submodule.mem_top
    have hle : isoPart σ ρ ≤ ((⨆ f : σ.asModule →ₗ[MonoidAlgebra ℂ G] ρ.asModule,
        LinearMap.range f).restrictScalars ℂ).comap ρ.asModuleEquiv.symm.toLinearMap := by
      refine iSup_le fun f => ?_
      rintro _ ⟨v, rfl⟩
      have : Representation.IntertwiningMap.equivLinearMapAsModule σ ρ f (σ.asModuleEquiv.symm v) ∈
          ⨆ f : σ.asModule →ₗ[MonoidAlgebra ℂ G] ρ.asModule, LinearMap.range f :=
        Submodule.mem_iSup_of_mem (Representation.IntertwiningMap.equivLinearMapAsModule σ ρ f) ⟨_, rfl⟩
      exact this
    exact hle hx) (Representation.IntertwiningMap.equivLinearMapAsModule σ' ρ f') hi
  exact ⟨((Representation.IntertwiningMap.equivLinearMapAsModule σ σ').symm e.toLinearMap).ofBijective e.bijective⟩

end Rep

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

theorem gl_ext {g h : GL (Fin a) (Af E)}
    (H : ∀ v, GeneralLinearGroup.map (pLoc E v) g = GeneralLinearGroup.map (pLoc E v) h) : g = h := by
  refine Units.ext (Matrix.ext fun i j => FiniteAdeleRing.ext E fun v => ?_)
  exact congrArg (fun x : GL (Fin a) (v.adicCompletion E) => x.val i j) (H v)

theorem comm_locGL (w : HeightOneSpectrum (𝓞 E)) {k : GL (Fin a) (Af E)}
    (hk : GeneralLinearGroup.map (pLoc E w) k = 1) (g : GL (Fin a) (w.adicCompletion E)) :
    k * locGL E a w g = locGL E a w g * k := by
  refine gl_ext fun v => ?_
  rw [map_mul, map_mul]
  by_cases h : v = w
  · subst h; rw [hk, one_mul, mul_one]
  · rw [pLoc_locGL_of_ne h, one_mul, mul_one]

theorem isoPart_fin {V : Type} [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ (GL (Fin a) (Af E)) V)
    (w : HeightOneSpectrum (𝓞 E)) {W : Type} [AddCommGroup W] [Module ℂ W]
    (σ : Representation ℂ (GL (Fin a) (w.adicCompletion E)) W) (k : GL (Fin a) (Af E)) {x : V}
    (hx : x ∈ isoPart σ (τ.comp (locGL E a w))) : τ k x ∈ isoPart σ (τ.comp (locGL E a w)) := by
  obtain ⟨g, hg⟩ : ∃ g, g = GeneralLinearGroup.map (pLoc E w) k := ⟨_, rfl⟩
  have hk : GeneralLinearGroup.map (pLoc E w) ((locGL E a w g)⁻¹ * k) = 1 := by
    rw [map_mul, map_inv, pLoc_locGL, hg, inv_mul_cancel]
  have h1 := isoPart_act σ _ g (isoPart_comm σ _ (τ ((locGL E a w g)⁻¹ * k)) (fun g' y => by
    simp only [MonoidHom.comp_apply]
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, comm_locGL w hk]) hx)
  rwa [MonoidHom.comp_apply, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left] at h1

variable [_root_.NumberField.IsTotallyComplex E]

theorem isoPart_op (π : CuspSub E a) (w : HeightOneSpectrum (𝓞 E)) {W : Type} [AddCommGroup W] [Module ℂ W]
    (σ : Representation ℂ (GL (Fin a) (w.adicCompletion E)) W) (o : Op E a) {x : π.V}
    (hx : x ∈ isoPart σ (π.locRep w)) : π.op o x ∈ isoPart σ (π.locRep w) := by
  cases o with
  | fin k =>
    exact isoPart_fin π.finPart w σ k hx
  | cpt k =>
    refine isoPart_comm σ _ _ (fun g y => Subtype.ext ?_) hx
    change (rt E a (infGL E a (Unitary.toUnits k)) * rt E a (finGL E a (locGL E a w g))) y.1 =
      (rt E a (finGL E a (locGL E a w g)) * rt E a (infGL E a (Unitary.toUnits k))) y.1
    rw [← map_mul, ← map_mul, infGL_comm]
  | lie X =>
    refine isoPart_comm σ _ _ (fun g y => Subtype.ext ?_) hx
    exact LinearMap.congr_fun (lie_rt_fin X (locGL E a w g)) y.1

theorem isLocComp_unique (π : CuspSub E a) (w : HeightOneSpectrum (𝓞 E))
    (σ σ' : SmIrr (GL (Fin a) (w.adicCompletion E))) (h : π.IsLocComp w σ) (h' : π.IsLocComp w σ') :
    Nonempty (σ.ρ.Equiv σ'.ρ) := by
  obtain ⟨f, h0, hf⟩ := h
  obtain ⟨f', h0', hf'⟩ := h'
  have := σ.irred
  have := σ'.irred
  refine equiv_of_isoPart σ.ρ σ'.ρ (π.locRep w) ?_ ⟨f', fun g => LinearMap.ext (hf' g)⟩
    fun e => h0' (congrArg Representation.IntertwiningMap.toLinearMap e)
  have hi := Submodule.map_injective_of_injective π.V.injective_subtype
  rcases π.irred ((isoPart σ.ρ (π.locRep w)).map π.V.subtype) (Submodule.map_subtype_le _ _) (by
    rintro o _ ⟨x, hx, rfl⟩
    exact ⟨_, isoPart_op π w σ.ρ o hx, rfl⟩) with h1 | h1
  · refine absurd (LinearMap.ext fun v => ?_) h0
    have h2 : isoPart σ.ρ (π.locRep w) = ⊥ := hi (h1.trans (Submodule.map_bot _).symm)
    have h3 : f v ∈ isoPart σ.ρ (π.locRep w) :=
      Submodule.mem_iSup_of_mem (⟨f, fun g => LinearMap.ext (hf g)⟩ : σ.ρ.IntertwiningMap (π.locRep w)) ⟨v, rfl⟩
    rw [h2] at h3
    exact h3
  · exact hi (h1.trans (Submodule.map_subtype_top _).symm)

end GlobalTheory.CuspRep.LocUniq

theorem GlobalTheory.CuspRep.CG.IsLoc.unique : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : CG E a) (w : HeightOneSpectrum (𝓞 E)) (σ σ' : Irr (GL (Fin a) (w.adicCompletion E))), π.IsLoc w σ → π.IsLoc w σ' → σ = σ' := by
  intro E _ _ _ a π w σ σ' h h'
  induction π using Quotient.inductionOn
  induction σ using Quotient.inductionOn
  induction σ' using Quotient.inductionOn
  exact Quotient.sound (GlobalTheory.CuspRep.LocUniq.isLocComp_unique _ w _ _ h h')
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdelicSplit
section
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct

namespace GlobalTheory.Mem.VolSplit

section Gen

variable {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {r : ℕ}

theorem map_sigR {A B : Type} [CommRing A] [Algebra F A] [CommRing B] [Algebra F B] (p : A →ₐ[F] B) (z : A ⊗[F] E) :
    (Algebra.TensorProduct.map p (AlgHom.id F E)).toRingHom (sigR A σ z) =
      sigR B σ ((Algebra.TensorProduct.map p (AlgHom.id F E)).toRingHom z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => simp [sigR]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem map_JR {A B : Type} [CommRing A] [Algebra F A] [CommRing B] [Algebra F B] (p : A →ₐ[F] B)
    (J : Matrix (Fin r) (Fin r) E) :
    (JR A J).map (Algebra.TensorProduct.map p (AlgHom.id F E)).toRingHom = JR B J := by
  ext i j; simp [JR, inclR]

theorem map_unit {A B : Type} [CommRing A] [Algebra F A] [CommRing B] [Algebra F B] (p : A →ₐ[F] B)
    (J : Matrix (Fin r) (Fin r) E) (g : Matrix (Fin r) (Fin r) (A ⊗[F] E)) :
    (Formalism.UG.cT (sigR A σ) g * JR A J * g).map (Algebra.TensorProduct.map p (AlgHom.id F E)).toRingHom =
      Formalism.UG.cT (sigR B σ) (g.map (Algebra.TensorProduct.map p (AlgHom.id F E)).toRingHom) * JR B J *
        g.map (Algebra.TensorProduct.map p (AlgHom.id F E)).toRingHom := by
  rw [Matrix.map_mul, Matrix.map_mul, map_JR]
  congr 2
  ext i j
  exact map_sigR σ p _

end Gen

theorem exists_adelic_split : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E), ∃ e : HA (AF F) σ J ≃ₜ* HA (Ainf F) σ J × HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) σ J, ∀ h, ((HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) σ J (e h).2 : GL (Fin M) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E)) : Matrix (Fin M) (Fin M) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E)) = finMat σ J h ∧ ((HA.mat (Ainf F) σ J (e h).1 : GL (Fin M) (Ainf F ⊗[F] E)) : Matrix (Fin M) (Fin M) (Ainf F ⊗[F] E)) = ((HA.mat (AF F) σ J h : GL (Fin M) (AF F ⊗[F] E)) : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)).map (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)) := by
  intro F E _ _ _ _ _ σ r J
  let pInf : AF F ⊗[F] E →+* Ainf F ⊗[F] E := (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)).toRingHom
  let pFin : AF F ⊗[F] E →+* Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E := (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom
  obtain ⟨e, he, hc, hc'⟩ := GlobalTheory.AdSplit.exists_adele_equiv F E
  have ext : ∀ {M N : Matrix (Fin r) (Fin r) (AF F ⊗[F] E)}, M.map pInf = N.map pInf → M.map pFin = N.map pFin →
      M = N := fun {M N} h1 h2 => by
    ext i j
    refine e.injective (Prod.ext ?_ ?_)
    · rw [(he _).1, (he _).1]; exact congrFun (congrFun h1 i) j
    · rw [(he _).2, (he _).2]; exact congrFun (congrFun h2 i) j
  let gl : Matrix (Fin r) (Fin r) (Ainf F ⊗[F] E) → Matrix (Fin r) (Fin r) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E) →
      Matrix (Fin r) (Fin r) (AF F ⊗[F] E) := fun M N => Matrix.of fun i j => e.symm (M i j, N i j)
  have g1 : ∀ M N, (gl M N).map pInf = M := fun M N => by
    ext i j
    exact ((he _).1.symm.trans (congrArg Prod.fst (e.apply_symm_apply _)))
  have g2 : ∀ M N, (gl M N).map pFin = N := fun M N => by
    ext i j
    exact ((he _).2.symm.trans (congrArg Prod.snd (e.apply_symm_apply _)))
  let χ : HA (AF F) σ J →* HA (Ainf F) σ J × HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) σ J :=
    { toFun := fun h => ((⟨Formalism.UG.bc pInf (HA.mat _ _ _ h), (by
          have := congrArg (fun M => M.map pInf) (show Formalism.UG.cT _ _ * _ * _ = _ from h.2)
          rw [map_unit σ (fstA F), map_JR (fstA F)] at this
          exact this)⟩ : HR (Ainf F) σ J),
        (⟨Formalism.UG.bc pFin (HA.mat _ _ _ h), (by
          have := congrArg (fun M => M.map pFin) (show Formalism.UG.cT _ _ * _ * _ = _ from h.2)
          rw [map_unit σ (sndA F), map_JR (sndA F)] at this
          exact this)⟩ : HR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) σ J))
      map_one' := Prod.ext (Subtype.ext (map_one (Formalism.UG.bc pInf))) (Subtype.ext (map_one (Formalism.UG.bc pFin)))
      map_mul' := fun a b => Prod.ext (Subtype.ext (map_mul (Formalism.UG.bc pInf) _ _))
        (Subtype.ext (map_mul (Formalism.UG.bc pFin) _ _)) }
  let ω : HA (Ainf F) σ J × HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) σ J → HA (AF F) σ J := fun g =>
    (⟨⟨gl g.1.1.val g.2.1.val, gl g.1.1.inv g.2.1.inv,
      ext (by rw [Matrix.map_mul, g1, g1, g.1.1.val_inv]; simp) (by rw [Matrix.map_mul, g2, g2, g.2.1.val_inv]; simp),
      ext (by rw [Matrix.map_mul, g1, g1, g.1.1.inv_val]; simp) (by rw [Matrix.map_mul, g2, g2, g.2.1.inv_val]; simp)⟩,
      ext ((map_unit σ (fstA F) J _).trans (Eq.trans (by
        rw [g1]
        exact g.1.2) (map_JR (fstA F) J).symm)) ((map_unit σ (sndA F) J _).trans (Eq.trans (by
        rw [g2]
        exact g.2.2) (map_JR (sndA F) J).symm))⟩ : HR (AF F) σ J)
  have l1 : Function.LeftInverse ω χ := fun h => Subtype.ext (Units.ext (ext (g1 _ _) (g2 _ _)))
  have l2 : Function.RightInverse ω χ := fun g =>
    Prod.ext (Subtype.ext (Units.ext (g1 _ _))) (Subtype.ext (Units.ext (g2 _ _)))
  let ψ : HA (AF F) σ J ≃* HA (Ainf F) σ J × HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) σ J :=
    { χ with invFun := ω, left_inv := l1, right_inv := l2 }
  have hp1 : Continuous pInf := (continuous_fst.comp hc).congr fun z => (he z).1
  have hp2 : Continuous pFin := (continuous_snd.comp hc).congr fun z => (he z).2
  have hv : Continuous fun h : HA (AF F) σ J => HA.mat _ _ _ h := continuous_subtype_val
  have c1 : Continuous ψ := by
    refine Continuous.prodMk (Continuous.subtype_mk (Units.continuous_iff.2 ⟨?_, ?_⟩) _)
      (Continuous.subtype_mk (Units.continuous_iff.2 ⟨?_, ?_⟩) _)
    · exact (Units.continuous_val.comp hv).matrix_map hp1
    · exact (Units.continuous_coe_inv.comp hv).matrix_map hp1
    · exact (Units.continuous_val.comp hv).matrix_map hp2
    · exact (Units.continuous_coe_inv.comp hv).matrix_map hp2
  have c2 : Continuous ψ.symm := by
    refine Continuous.subtype_mk (Units.continuous_iff.2 ⟨?_, ?_⟩) _
    · refine continuous_matrix fun i j => hc'.comp (Continuous.prodMk ?_ ?_)
      · exact (Units.continuous_val.comp (continuous_subtype_val.comp continuous_fst)).matrix_elem i j
      · exact (Units.continuous_val.comp (continuous_subtype_val.comp continuous_snd)).matrix_elem i j
    · refine continuous_matrix fun i j => hc'.comp (Continuous.prodMk ?_ ?_)
      · exact (Units.continuous_coe_inv.comp (continuous_subtype_val.comp continuous_fst)).matrix_elem i j
      · exact (Units.continuous_coe_inv.comp (continuous_subtype_val.comp continuous_snd)).matrix_elem i j
  exact ⟨{ ψ with continuous_toFun := c1, continuous_invFun := c2 }, fun h => ⟨rfl, rfl⟩⟩

end GlobalTheory.Mem.VolSplit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCommonField
section
open UpperTheory.HF

open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem
open Formalism.L2.Col

noncomputable section

namespace GlobalTheory.Mem.DatHecke

open Formalism.L2.Host (HChar embPsi)
open GlobalTheory.Mem.Chr (ConjPl CMData)

theorem exists_gen (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M] :
    ∃ α : ℂ, IsAlgebraic ℚ α ∧ ∀ (K : Type) [Field K] [CharZero K] (σ : K →+* ℂ), (∃ x, σ x = α) →
      ∀ z ∈ M, ∃ x, σ x = z := by
  obtain ⟨a, ha⟩ := Field.exists_primitive_element ℚ M
  refine ⟨a, (Algebra.IsAlgebraic.isAlgebraic a).algHom M.val, ?_⟩
  intro K _ _ σ ⟨x, hx⟩ z hz
  have h1 : (⊤ : IntermediateField ℚ M) ≤ (σ.toRatAlgHom.fieldRange).comap M.val := by
    rw [← ha]
    exact IntermediateField.adjoin_simple_le_iff.2 ⟨x, hx⟩
  exact h1 (IntermediateField.mem_top (x := (⟨z, hz⟩ : M)))

section Host

variable {R : Ranks} (H : Host R)

end Host


section PrimesOk

variable {X : Fields} {Pr : Primes X}

theorem mem_vG (h : Pr.Ok) (i : Fin 2) (w : HeightOneSpectrum (𝓞 X.E)) :
    w ∈ Pr.vG i ↔ X.conjO (Pr.piG i) ∈ w.asIdeal := by
  refine mem_divs (fun h0 => ?_) w
  have h1 := h.piG_norm i
  rw [h0, mul_zero] at h1
  have h2 : (Pr.g i : 𝓞 X.E) ≠ 0 := by exact_mod_cast (h.g_prime i).ne_zero
  exact h2 h1.symm

theorem mem_vGs (w : HeightOneSpectrum (𝓞 X.E)) : w ∈ Pr.vGs ↔ ∃ i, w ∈ Pr.vG i := by
  classical
  unfold Primes.vGs
  rw [Fin.exists_fin_two]
  convert Finset.mem_union

theorem g_mem_of_mem_vG (h : Pr.Ok) {i : Fin 2} {w : HeightOneSpectrum (𝓞 X.E)} (hw : w ∈ Pr.vG i) :
    ((Pr.g i : ℕ) : 𝓞 X.E) ∈ w.asIdeal := by
  rw [← h.piG_norm i]
  exact w.asIdeal.mul_mem_left _ ((mem_vG h i w).1 hw)

end PrimesOk

end GlobalTheory.Mem.DatHecke

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsFdegSmulOfIsDS
section
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct

namespace GlobalTheory.Mem.Vol

theorem exists_isFdeg_smul_of_isDS : ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsDS ε lam σ → ∀ c : NNReal, 0 < c → ∃ d : ℝ, IsFdeg ((c : ENNReal) • Formalism.REAL.muG ε) σ d := by
  intro n ε lam H _ _ σ h c hc
  obtain ⟨h1, h2, hU, hirr, hsq, -⟩ := h
  obtain ⟨d, hd, hI⟩ := GlobalTheory.schur_orthogonality_unitary n ε H σ hU hirr hsq
  have hc' : (0 : ℝ) < (c : ℝ) := hc
  refine ⟨d / c, div_pos hd hc', fun v w v' w' => ⟨(hI v w v' w').1.smul_measure ENNReal.coe_ne_top, ?_⟩⟩
  rw [integral_smul_measure, (hI v w v' w').2, ENNReal.coe_toReal, Complex.real_smul,
    Complex.ofReal_div, div_div_eq_mul_div]
  ring

end GlobalTheory.Mem.Vol
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSmulMemOfIsLattice
section
namespace GlobalTheory.SmulMemOfIsLattice

theorem exists_smul_mem_of_isLattice {E : Type} [inst : Field E] [NumberField E] {n : ℕ}
    (B : Submodule (NumberField.RingOfIntegers E) (Formalism.L2.Col.Sp E n))
    (hB : Submodule.IsFullLattice E B) (x : Formalism.L2.Col.Sp E n) :
    ∃ r ∈ nonZeroDivisors (NumberField.RingOfIntegers E), r • x ∈ B := by
  have hx : x ∈ Submodule.span E (B : Set (Formalism.L2.Col.Sp E n)) := by
    rw [hB.span_eq_top]; exact Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_mem _, by simpa using hy⟩
  | zero => exact ⟨1, one_mem _, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨r, hr, hry⟩ := hy
    obtain ⟨s, hs, hsz⟩ := hz
    refine ⟨r * s, mul_mem hr hs, ?_⟩
    rw [smul_add]
    refine B.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact B.smul_mem _ hry
    · rw [mul_smul]; exact B.smul_mem _ hsz
  | smul c y _ hy =>
    obtain ⟨r, hr, hry⟩ := hy
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := NumberField.RingOfIntegers E) c
    refine ⟨r * b, mul_mem hr hb, ?_⟩
    have hb0 : algebraMap (NumberField.RingOfIntegers E) E b ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
    have h : (r * b) • ((algebraMap (NumberField.RingOfIntegers E) E a / algebraMap (NumberField.RingOfIntegers E) E b) • y) = a • (r • y) := by
      rw [← algebraMap_smul E (r * b), ← algebraMap_smul E a, ← algebraMap_smul E r y, smul_smul, smul_smul, map_mul]
      congr 1
      field_simp
    rw [h]
    exact B.smul_mem _ hry

end GlobalTheory.SmulMemOfIsLattice
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueInfEmb
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct

namespace GlobalTheory.Mem.VolEmb

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem infEmb_exists (τ : E →+* ℂ) (w : InfinitePlace F) (hw : w.embedding = τ.comp (algebraMap F E)) :
    ∃ θ : Ainf F ⊗[F] E →+* ℂ, IsInfEmb τ θ := by
  let _ : Algebra F ℂ := (τ.comp (algebraMap F E)).toAlgebra
  let f : Ainf F →ₐ[F] ℂ :=
    { toRingHom := (InfinitePlace.Completion.extensionEmbedding w).comp (Pi.evalRingHom _ w)
      commutes' := fun x => by
        change InfinitePlace.Completion.extensionEmbedding w ((algebraMap F (Ainf F) x) w) = _
        rw [InfiniteAdeleRing.algebraMap_apply, InfinitePlace.Completion.extensionEmbedding_coe]
        exact DFunLike.congr_fun hw x }
  let g : E →ₐ[F] ℂ := { toRingHom := τ, commutes' := fun _ => rfl }
  refine ⟨(Algebra.TensorProduct.lift f g (fun _ _ => Commute.all _ _)).toRingHom, fun x => ?_, ?_⟩
  · show f 1 * g x = τ x
    rw [map_one, one_mul]
    rfl
  · have : (fun a : Ainf F => (Algebra.TensorProduct.lift f g (fun _ _ => Commute.all _ _)).toRingHom
        (a ⊗ₜ[F] (1 : E))) = fun a => InfinitePlace.Completion.extensionEmbedding w (a w) := by
      funext a
      show f a * g 1 = _
      rw [map_one, mul_one]
      rfl
    rw [this]
    exact (InfinitePlace.Completion.isometry_extensionEmbedding w).continuous.comp (continuous_apply w)

theorem infEmb_unique (τ : E →+* ℂ) (θ θ' : Ainf F ⊗[F] E →+* ℂ) (h : IsInfEmb τ θ)
    (h' : IsInfEmb τ θ') : θ = θ' :=
  by apply _root_.UpperTheory.Reformulated.B.Qh26.isInfEmb_unique <;> assumption

theorem existsUnique_infEmb : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ τ : E →+* ℂ, ∃! θ : Ainf F ⊗[F] E →+* ℂ, IsInfEmb τ θ := by
  intro F E _ _ _ _ _ σ h τ
  have := h.1
  have hr : (InfinitePlace.mk (τ.comp (algebraMap F E))).IsReal := IsTotallyReal.isReal _
  have hw : (InfinitePlace.mk (τ.comp (algebraMap F E))).embedding = τ.comp (algebraMap F E) :=
    InfinitePlace.embedding_mk_eq_of_isReal (InfinitePlace.isReal_mk_iff.1 hr)
  obtain ⟨θ, hθ⟩ := infEmb_exists τ _ hw
  exact ⟨θ, hθ, fun θ' h' => infEmb_unique τ θ' θ h' hθ⟩

end GlobalTheory.Mem.VolEmb
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryMuZeroCharactersOfSplitTypePrimesAlStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mu0Exists_of_splits_of_integral_of_MUQ : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (P : Formalism.L2.Host.PiBar H) (W : Formalism.L2.Host.Omg H) (e : R.Psi → ℚ) (j : ℕ), (∀ k, SplitsC H.E (H.g k)) → (∀ τ, ∃ z : ℤ, e τ = z) → UpperTheory.MUQ (Formalism.L2.Host.embPsi H) e → Formalism.L2.Host.Mu0Exists P W e j := by
  first | exact @GlobalTheory.Mem.MuZero.exists_unitary_mu_zero_characters_of_split_type_primes | exact GlobalTheory.Mem.MuZero.exists_unitary_mu_zero_characters_of_split_type_primes | (intros; apply GlobalTheory.Mem.MuZero.exists_unitary_mu_zero_characters_of_split_type_primes <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HostDeltaCharacterInertialOrderFifteenExistsStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.host_delta_character_inertial_order_fifteen_exists : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (p : ℕ), p.Prime → p % 15 = 1 → SplitsC H.E p → Formalism.L2.Host.DeltaExists (H := H) p := by
  first | exact @GlobalTheory.Mem.DeltaZero.delta_exists | exact GlobalTheory.Mem.DeltaZero.delta_exists | (intros; apply GlobalTheory.Mem.DeltaZero.delta_exists <;> assumption)
end

