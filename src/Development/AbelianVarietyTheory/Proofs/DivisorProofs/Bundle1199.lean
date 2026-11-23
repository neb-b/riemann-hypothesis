module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1176
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0298
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0300
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenNsmulAdelicCompletionOfVectorSet
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.GelfandKazhdanDual
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1192
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1173
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1186
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.Counterexamples.TwistSurvey.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0948
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0958
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicDiscreteSeriesModelsUnitarilyEquivale
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1179
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0038
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1184
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1162
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1163
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1183
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1143
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1069
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1065
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1122
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1131

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonDenominatorCompactFiniteAdeles
section
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CuspQuot GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace MeasureTheory

open IsDedekindDomain

namespace GlobalTheory.AdeleDenom

variable (E : Type) [Field E] [NumberField E]

def intAfter (c : Af E) : Set (Af E) := {y | ∀ v, (c * y) v ∈ v.adicCompletionIntegers E}

theorem isOpen_intAfter (c : Af E) : IsOpen (intAfter E c) :=
  (GlobalTheory.AdLat.OpenLat.isOpen_integral E).preimage (continuous_const.mul continuous_id)

theorem nat_mul_integral (k : ℕ) {x : Af E} (hx : ∀ v, x v ∈ v.adicCompletionIntegers E) (v) :
    ((k : Af E) * x) v ∈ v.adicCompletionIntegers E := by
  have hk : ((k : Af E)) v ∈ v.adicCompletionIntegers E := by
    rw [show ((k : Af E)) v = (k : v.adicCompletion E) from rfl]
    exact natCast_mem _ k
  exact mul_mem hk (hx v)

theorem exists_nat_mul_integral (a : Af E) :
    ∃ N : ℕ, 0 < N ∧ ∀ v, ((N : Af E) * a) v ∈ v.adicCompletionIntegers E := by
  obtain ⟨N, hN, h⟩ := GlobalTheory.AdLat.OpenLat.exists_nsmul_adele E (intAfter E a)
    ((isOpen_intAfter E a).mem_nhds (by intro v; simp only [mul_zero]; exact zero_mem _))
  refine ⟨N, hN, fun v => ?_⟩
  have h1 := h 1 (fun v => one_mem _) v
  rw [nsmul_eq_mul, mul_one, mul_comm] at h1
  exact h1

theorem mem_intAfter_of_dvd {d m : ℕ} (h : d ∣ m) {y : Af E} (hy : y ∈ intAfter E (d : Af E)) :
    y ∈ intAfter E (m : Af E) := by
  obtain ⟨k, rfl⟩ := h
  intro v
  have e : (((d * k : ℕ)) : Af E) * y = (k : Af E) * ((d : Af E) * y) := by
    rw [Nat.cast_mul]; ring
  rw [e]
  exact nat_mul_integral E k hy v

theorem intAfter_mono {n m : ℕ} (h : n ≤ m) :
    intAfter E ((n.factorial : ℕ) : Af E) ⊆ intAfter E ((m.factorial : ℕ) : Af E) :=
  fun _ hy => mem_intAfter_of_dvd E (Nat.factorial_dvd_factorial h) hy

theorem exists_common_denom : ∀ (E : Type) [Field E] [NumberField E] (Kf : Set (Af E)), IsCompact Kf →
    ∃ n : ℕ, 0 < n ∧ ∀ ξ : E, algebraMap E (Af E) ξ ∈ Kf → IsIntegral ℤ ((n : E) * ξ) := by
  intro E _ _ Kf hK
  have hcov : Kf ⊆ ⋃ n : ℕ, intAfter E ((n.factorial : ℕ) : Af E) := by
    intro y _
    obtain ⟨N, hN, h⟩ := exists_nat_mul_integral E y
    exact Set.mem_iUnion.mpr ⟨N, mem_intAfter_of_dvd E (Nat.dvd_factorial hN le_rfl) h⟩
  obtain ⟨n, hn⟩ := hK.elim_directed_cover _ (fun n => isOpen_intAfter E _) hcov
    (Monotone.directed_le fun a b h => intAfter_mono E h)
  refine ⟨n.factorial, Nat.factorial_pos n, fun ξ hξ => ?_⟩
  have h := hn hξ
  have hr : ((n.factorial : ℕ) : E) * ξ ∈ (algebraMap (𝓞 E) E).range := by
    refine HeightOneSpectrum.mem_integers_of_valuation_le_one E _ fun v => ?_
    have := h v
    rw [← map_natCast (algebraMap E (Af E)), ← map_mul] at this
    rwa [FiniteAdeleRing.algebraMap_apply, HeightOneSpectrum.mem_adicCompletionIntegers,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at this
  obtain ⟨a, ha⟩ := hr
  rw [← ha]
  exact ((RingOfIntegers.isIntegral a).map (IsScalarTower.toAlgHom ℤ (𝓞 E) E))

end GlobalTheory.AdeleDenom
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactClopenNhdsOneGLFiniteAdeles
section
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CuspQuot GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace MeasureTheory

open scoped RestrictedProduct

noncomputable section

namespace GlobalTheory.GLFinAdeleNhds

theorem totallyDisconnectedSpace_of_injective {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [TotallyDisconnectedSpace Y] (f : X → Y) (hf : Continuous f) (hi : Function.Injective f) :
    TotallyDisconnectedSpace X := by
  refine ⟨fun s _ hs => ?_⟩
  have h := (hs.image f hf.continuousOn).subsingleton
  exact fun x hx y hy => hi (h (Set.mem_image_of_mem f hx) (Set.mem_image_of_mem f hy))

theorem totallyDisconnectedSpace_adicCompletion {F : Type} [Field F] [NumberField F]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) : TotallyDisconnectedSpace (v.adicCompletion F) := by
  rw [totallyDisconnectedSpace_iff_connectedComponent_zero]
  refine Set.eq_singleton_iff_unique_mem.mpr ⟨mem_connectedComponent, fun x hx => ?_⟩
  by_contra hne
  have hr : (Valued.v : Valuation (v.adicCompletion F) _).restrict x ≠ 0 :=
    (Valuation.zero_iff _).not.mpr hne
  have hc := Valued.isClopen_ball (R := v.adicCompletion F)
    ((Valued.v : Valuation (v.adicCompletion F) _).restrict x)
  have h0 : (0 : v.adicCompletion F) ∈
      {y | (Valued.v : Valuation (v.adicCompletion F) _).restrict y <
        (Valued.v : Valuation (v.adicCompletion F) _).restrict x} := by
    simp only [Set.mem_ofPred_eq, map_zero]
    exact pos_iff_ne_zero.mpr hr
  have h1 := hc.connectedComponent_subset h0 hx
  exact (lt_irrefl ((Valued.v : Valuation (v.adicCompletion F) _).restrict x)) h1

theorem totallyDisconnectedSpace_Af (E : Type) [Field E] [NumberField E] : TotallyDisconnectedSpace (Af E) := by
  haveI : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 E), TotallyDisconnectedSpace (v.adicCompletion E) :=
    fun v => totallyDisconnectedSpace_adicCompletion v
  haveI : TotallyDisconnectedSpace
      (Πʳ v : IsDedekindDomain.HeightOneSpectrum (𝓞 E), [v.adicCompletion E, v.adicCompletionIntegers E]) :=
    totallyDisconnectedSpace_of_injective (fun x v => x v) (continuous_pi fun v => RestrictedProduct.continuous_eval v)
      fun x y h => Subtype.ext (funext fun v => congrFun h v)
  exact inferInstanceAs (TotallyDisconnectedSpace
    (Πʳ v : IsDedekindDomain.HeightOneSpectrum (𝓞 E), [v.adicCompletion E, v.adicCompletionIntegers E]))

theorem exists_isCompact_isClopen (E : Type) [Field E] [NumberField E] (a : ℕ) (B : Set (GL (Fin a) (Af E)))
    (hB : B ∈ nhds (1 : GL (Fin a) (Af E))) :
    ∃ U : Set (GL (Fin a) (Af E)), IsOpen U ∧ IsCompact U ∧ IsClosed U ∧ 1 ∈ U ∧ U ⊆ B := by
  haveI := totallyDisconnectedSpace_Af E
  haveI : TotallyDisconnectedSpace (Matrix (Fin a) (Fin a) (Af E)) :=
    inferInstanceAs (TotallyDisconnectedSpace (Fin a → Fin a → Af E))
  haveI : TotallyDisconnectedSpace (GL (Fin a) (Af E)) :=
    totallyDisconnectedSpace_of_injective _ Units.continuous_val Units.val_injective
  haveI : LocallyCompactSpace (GL (Fin a) (Af E)) := Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  obtain ⟨K, hK, hKB, hc⟩ := local_compact_nhds hB
  obtain ⟨U, hU, h1, hUK⟩ := loc_compact_Haus_tot_disc_of_zero_dim.mem_nhds_iff.1 hK
  exact ⟨U, hU.2, hc.of_isClosed_subset hU.1 hUK, hU.1, h1, hUK.trans hKB⟩

end GlobalTheory.GLFinAdeleNhds
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplexConjugateCuspidalRepresentation
section
open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair

noncomputable section

namespace GlobalTheory

def CuspRep.CuspSub.mapConj {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}
    (π : CuspSub E a) (C : Sm E a ≃ₗ⋆[ℂ] Sm E a) (hact : ∀ o φ, act o (C φ) = C (act o φ))
    (hcusp : ∀ φ : Sm E a, IsCuspForm φ → IsCuspForm (C φ)) : CuspSub E a where
  V := π.V.map C.toLinearMap
  cusp := by rintro _ ⟨φ, hφ, rfl⟩; exact hcusp φ (π.cusp φ hφ)
  stable := by
    rintro o _ ⟨φ, hφ, rfl⟩
    exact ⟨_, π.stable o φ hφ, (hact o φ).symm⟩
  ne_bot h := π.ne_bot ((Submodule.map_eq_bot_iff (e := C)).1 h)
  irred W hW hs := by
    have h := π.irred (W.comap C.toLinearMap) (fun φ hφ => by
      obtain ⟨ψ, h1, h2⟩ := hW hφ
      rwa [← C.injective h2]) fun o φ hφ => by
      change C (act o φ) ∈ W
      rw [← hact]
      exact hs o _ hφ
    have e := Submodule.map_comap_eq_of_surjective (f := C.toLinearMap) C.surjective W
    exact h.imp (fun h => by rw [← e, h, Submodule.map_bot]) fun h => by rw [← e, h]

theorem exists_conj_cuspSub : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : CuspSub E a),
    ∃ (π' : CuspSub E a) (J : π.V ≃ₗ⋆[ℂ] π'.V), ∀ o φ, J (π.op o φ) = π'.op o (J φ) := by
  intro E _ _ _ a π
  obtain ⟨C, hC, hact⟩ := _root_.GlobalTheory.smooth_conj_commutes_act E a
  have hZ := _root_.GlobalTheory.CuspRep.ConjZalg.conj_Zalg E a C hact
  have hcusp := isCuspForm_of_conj_pointwise E a C hC hact hZ
  refine ⟨π.mapConj C hact hcusp, C.submoduleMap π.V, fun o φ => Subtype.ext ?_⟩
  exact (hact o φ.1).symm

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousRepresentativeSobolevBound
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjEq

theorem exists_conjModel_cast {D : D7} {V : HSp D} {S S' : D.what₂.Tau → SPar} (e : S' = fun τ => dualPar (S τ))
    (M : DSModel V S) (v : M.Vec) (hv : IsExtVec M v) :
    ∃ (M' : DSModel V S') (c : ∀ τ, M'.H τ ≃ₗᵢ⋆[ℂ] M.H τ) (v' : M'.Vec),
      (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ y, c τ (M'.rep τ g y) = M.rep τ g (c τ y)) ∧ IsExtVec M' v' := by
  subst e
  exact GlobalTheory.ConjExt.exists_conjModel_ext D V S M v hv

theorem exists_conj_equiv : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.IsModels → TieIn T R κ v₀ → ∀ i σ, ¬ GoodEmb T.Q.c (res T σ) → ∃ c : ∀ τ, (R.MW i σ).H τ ≃ₗᵢ⋆[ℂ] (R.MW i ((starRingEnd ℂ).comp σ)).H τ, ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (Wc D i) τ), ∀ y, c τ ((R.MW i σ).rep τ g y) = (R.MW i ((starRingEnd ℂ).comp σ)).rep τ g (c τ y) := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ hM hT i σ hσ
  have hg : GoodEmb T.Q.c (res T ((starRingEnd ℂ).comp σ)) := good_resC T hσ
  obtain ⟨hs, -, w, hw⟩ := GlobalTheory.HolDict.holShape_of_good D G Pl0 T0 A T R κ v₀ hT i ((starRingEnd ℂ).comp σ) hg
  obtain ⟨M', c, v', hc, hv'⟩ := exists_conjModel_cast (GlobalTheory.ConjReading.parAt_conj (Wc D i) σ) (R.MW i σ) (v₀ i σ)
    (hT.hv₀ i σ).1
  obtain ⟨U, hU⟩ := _root_.GlobalTheory.HolDict.holModel_unique D R.θ _ _ (R.MW i ((starRingEnd ℂ).comp σ)) M' w (v₀ i _) v' hM.inf hs hw
    (hT.hv₀ i _).1 hv'
  refine ⟨fun τ => (c τ).symm.trans (U τ), fun τ g hg y => ?_⟩
  show U τ ((c τ).symm _) = (R.MW i ((starRingEnd ℂ).comp σ)).rep τ g (U τ ((c τ).symm y))
  rw [← hU τ g hg]
  congr 1
  apply (c τ).injective
  rw [hc τ g hg, LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.apply_symm_apply]

end GlobalTheory.ConjEq
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousSplitTorusSection
section
noncomputable section

open NumberField Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.StdPar GlobalTheory.IdTorus
open GlobalTheory.Doubling (absE conjUnit)
open Formalism.UG (cT)
open scoped TensorProduct

namespace GlobalTheory.IdTorus

def frameTorMat {A : Type} [CommRing A] (s : A →+* A) {n r : ℕ} (J : Matrix (Fin n) (Fin n) A)
    (X Y : Matrix (Fin n) (Fin r) A) (d : Fin r → Aˣ) : Matrix (Fin n) (Fin n) A :=
  1 + X * diagonal (fun i => (d i : A) - 1) * (cT s Y * J) +
    Y * diagonal (fun i => s ((d i)⁻¹ : Aˣ) - 1) * (cT s X * J)

section Alg

variable {A : Type} [CommRing A] {s : A →+* A} {n r : ℕ} {J : Matrix (Fin n) (Fin n) A}
  {X Y : Matrix (Fin n) (Fin r) A}

theorem diagonal_sub_one' (a : Fin r → A) : diagonal (fun i => a i - 1) = diagonal a - 1 := by
  rw [← diagonal_one, diagonal_sub]

theorem frameTorMat_mul_X (xx : cT s X * J * X = 0) (yx : cT s Y * J * X = 1) (d : Fin r → Aˣ) :
    frameTorMat s J X Y d * X = X * diagonal fun i => (d i : A) := by
  simp only [frameTorMat, Matrix.add_mul, Matrix.mul_assoc _ (cT s Y * J), Matrix.mul_assoc _ (cT s X * J), xx, yx,
    diagonal_sub_one', Matrix.mul_sub]
  simp

theorem frameTorMat_mul_Y (yy : cT s Y * J * Y = 0) (xy : cT s X * J * Y = 1) (d : Fin r → Aˣ) :
    frameTorMat s J X Y d * Y = Y * diagonal fun i => s ((d i)⁻¹ : Aˣ) := by
  simp only [frameTorMat, Matrix.add_mul, Matrix.mul_assoc _ (cT s Y * J), Matrix.mul_assoc _ (cT s X * J), yy, xy,
    diagonal_sub_one', Matrix.mul_sub]
  simp

theorem frameTorMat_mulVec {z : Fin n → A} (hx : (cT s X * J) *ᵥ z = 0) (hy : (cT s Y * J) *ᵥ z = 0)
    (d : Fin r → Aˣ) : frameTorMat s J X Y d *ᵥ z = z := by
  rw [frameTorMat, add_mulVec, add_mulVec, ← mulVec_mulVec, hy, mulVec_zero, ← mulVec_mulVec, hx, mulVec_zero]
  simp

theorem frameTorMat_mul_inv (xx : cT s X * J * X = 0) (yy : cT s Y * J * Y = 0) (xy : cT s X * J * Y = 1)
    (yx : cT s Y * J * X = 1) (d : Fin r → Aˣ) : frameTorMat s J X Y d * frameTorMat s J X Y d⁻¹ = 1 := by
  conv_lhs => rw [show frameTorMat s J X Y d⁻¹ = 1 + _ + _ from rfl, Matrix.mul_add, Matrix.mul_add, Matrix.mul_one]
  simp only [← Matrix.mul_assoc (frameTorMat s J X Y d), frameTorMat_mul_X xx yx, frameTorMat_mul_Y yy xy,
    Matrix.mul_assoc _ (diagonal _) (diagonal _), diagonal_mul_diagonal]
  have h1 : ∀ i, (d i : A) * (((d⁻¹) i : Aˣ) - 1) = 1 - d i := fun i => by
    rw [Pi.inv_apply, mul_sub, Units.mul_inv, mul_one]
  have h2 : ∀ i, s ((d i)⁻¹ : Aˣ) * (s (((d⁻¹) i)⁻¹ : Aˣ) - 1) = 1 - s ((d i)⁻¹ : Aˣ) := fun i => by
    rw [Pi.inv_apply, inv_inv, mul_sub, ← map_mul, Units.inv_mul, map_one, mul_one]
  simp only [h1, h2, frameTorMat, ← diagonal_sub, diagonal_one, Matrix.mul_sub, Matrix.sub_mul]
  abel

theorem frameTorMat_unitary (hs : ∀ a, s (s a) = a) (hJ : cT s J = J) (xx : cT s X * J * X = 0)
    (yy : cT s Y * J * Y = 0) (xy : cT s X * J * Y = 1) (yx : cT s Y * J * X = 1) (d : Fin r → Aˣ) :
    cT s (frameTorMat s J X Y d) * J * frameTorMat s J X Y d = J := by
  have cc : ∀ Z : Matrix (Fin n) (Fin r) A, cT s (cT s Z) = Z := fun Z => Matrix.ext fun i j => hs _
  have cd : ∀ a : Fin r → A, cT s (diagonal a) = diagonal fun i => s (a i) := fun a => by
    ext i j; by_cases h : i = j <;> simp [cT, diagonal, h, eq_comm]
  have ca : ∀ P Q : Matrix (Fin n) (Fin n) A, cT s (P + Q) = cT s P + cT s Q := fun P Q =>
    Matrix.ext fun i j => map_add s _ _
  have hU : cT s (frameTorMat s J X Y d) * J = J * frameTorMat s J X Y d⁻¹ := by
    simp only [frameTorMat, ca, Formalism.UG.cT_mul, Formalism.UG.cT_one, cc, hJ, cd, map_sub, map_one, hs, Pi.inv_apply, inv_inv,
      Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, Matrix.one_mul, Matrix.mul_one]
    abel
  have hM' : frameTorMat s J X Y d⁻¹ * frameTorMat s J X Y d = 1 := by
    simpa only [inv_inv] using frameTorMat_mul_inv xx yy xy yx d⁻¹
  rw [hU, Matrix.mul_assoc, hM', Matrix.mul_one]

end Alg

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

omit [NumberField F] [NumberField E] in
theorem continuous_frameTorMat {B : Type} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] {s : B →+* B}
    (hs : Continuous s) {n r : ℕ} (J : Matrix (Fin n) (Fin n) B) (X Y : Matrix (Fin n) (Fin r) B) :
    Continuous (frameTorMat s J X Y) := by
  have h1 : Continuous fun d : Fin r → Bˣ => diagonal fun i => (d i : B) - 1 :=
    Continuous.matrix_diagonal (continuous_pi fun i => (Units.continuous_val.comp (continuous_apply i)).sub continuous_const)
  have h2 : Continuous fun d : Fin r → Bˣ => diagonal fun i => s ((d i)⁻¹ : Bˣ) - 1 :=
    Continuous.matrix_diagonal (continuous_pi fun i =>
      (hs.comp (Units.continuous_coe_inv.comp (continuous_apply i))).sub continuous_const)
  exact (continuous_const.add ((continuous_const.matrix_mul h1).matrix_mul continuous_const)).add
    ((continuous_const.matrix_mul h2).matrix_mul continuous_const)

theorem exists_continuous_isIdTorusElt {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ}
    {X Y : Matrix (Fin n) (Fin r) E} (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) :
    ∃ t : (Fin r → (AF F ⊗[F] E)ˣ) → GAd σ J, Continuous t ∧ ∀ l, IsIdTorusElt σ J X Y l (t l) := by
  obtain ⟨_, _⟩ := ring_facts (F := F) (E := E)
  set s := sigR (AF F) σ
  have hs : ∀ a, s (s a) = a := fun a => by
    induction a using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | tmul a x => exact congrArg (a ⊗ₜ[F] ·) (sigma_sigma h x)
  have c1 : ∀ {a b : ℕ} (Z : Matrix (Fin a) (Fin b) E), cT s (adMat F Z) = adMat F (cT (σ : E →+* E) Z) :=
    fun Z => rfl
  have c3 : ∀ {a : ℕ} (Z : Matrix (Fin n) (Fin a) E),
      (cT s (adMat F Z) * JR (AF F) J : Matrix (Fin a) (Fin n) (AF F ⊗[F] E)) = adMat F (cT (σ : E →+* E) Z * J) :=
    fun Z => by rw [c1]; simp only [adMat, JR, Matrix.map_mul] <;> rfl
  have c2 : ∀ Z Z' : Matrix (Fin n) (Fin r) E,
      (cT s (adMat F Z) * JR (AF F) J : Matrix (Fin r) (Fin n) (AF F ⊗[F] E)) * adMat F Z' =
        adMat F (cT (σ : E →+* E) Z * J * Z') := fun Z Z' => by
    rw [c3]; simp only [adMat, Matrix.map_mul]
  have hJ' : cT s (JR (AF F) J) = JR (AF F) J :=
    (c1 J).trans (congrArg (adMat F) (Matrix.ext fun i j => hJ.1 i j))
  have xx : (cT s (adMat F X) * JR (AF F) J : Matrix (Fin r) (Fin n) (AF F ⊗[F] E)) * adMat F X = 0 := by
    rw [c2, hW.xx]; exact Matrix.map_zero _ (map_zero _)
  have yy : (cT s (adMat F Y) * JR (AF F) J : Matrix (Fin r) (Fin n) (AF F ⊗[F] E)) * adMat F Y = 0 := by
    rw [c2, hW.yy]; exact Matrix.map_zero _ (map_zero _)
  have xy : (cT s (adMat F X) * JR (AF F) J : Matrix (Fin r) (Fin n) (AF F ⊗[F] E)) * adMat F Y = 1 := by
    rw [c2, hW.xy]; exact Matrix.map_one _ (map_zero _) (map_one _)
  have yx : (cT s (adMat F Y) * JR (AF F) J : Matrix (Fin r) (Fin n) (AF F ⊗[F] E)) * adMat F X = 1 := by
    rw [c2, GlobalTheory.StdPar.yx h hJ hW]; exact Matrix.map_one _ (map_zero _) (map_one _)
  let M := frameTorMat s (JR (AF F) J) (adMat F X) (adMat F Y)
  have hinv : ∀ d, M d * M d⁻¹ = 1 := frameTorMat_mul_inv xx yy xy yx
  have hinv' : ∀ d, M d⁻¹ * M d = 1 := fun d => by simpa only [inv_inv] using hinv d⁻¹
  let t : (Fin r → (AF F ⊗[F] E)ˣ) → GAd σ J := fun l =>
    ⟨⟨M l, M l⁻¹, hinv l, hinv' l⟩, frameTorMat_unitary hs hJ' xx yy xy yx l⟩
  have hc : Continuous M := continuous_frameTorMat (GlobalTheory.AdelicUnitaryTop.continuous_sigR (AF F) σ) _ _ _
  refine ⟨t, ?_, fun l => ⟨frameTorMat_mul_X xx yx l, ?_, fun z hz => ?_⟩⟩
  · refine Continuous.subtype_mk ((Units.continuous_iff (f := fun l => (⟨M l, M l⁻¹, hinv l, hinv' l⟩ : GL (Fin n) (AF F ⊗[F] E)))).2 ⟨hc, hc.comp continuous_inv⟩) _
  · refine (frameTorMat_mul_Y yy xy l).trans (congrArg (fun D => adMat F Y * diagonal D) (funext fun k => ?_))
    rw [← map_inv]; rfl
  · have key : ∀ C : Matrix (Fin n) (Fin r) E, z ∈ colPerp σ J C Set.univ →
        (cT s (adMat F C) * JR (AF F) J) *ᵥ z = 0 := fun C hC => by
      rw [c3]
      funext i
      have := (Submodule.mem_iInf _).1 hC i
      simpa using this
    exact frameTorMat_mulVec (key X hz.1) (key Y hz.2) l

end Main

end GlobalTheory.IdTorus
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleCoordsLocalRingOfVarietyPointResidueCStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_etaleCoords_localRingOfVarietyPoint_residueComplex : ∀ {κ' : Type} [Field κ'] [Algebra ℂ κ'] (B : Subring κ') (hB : IsLocModel (algebraMap ℂ κ') B),
    RatRes (algebraMap ℂ κ') B → ((algebraMap ℂ κ').codRestrict B hB.const_mem).FormallySmooth →
    ∃ (r : ℕ) (τ : Fin r → B), (letI := hB.isLocalRing; IsLocalRing.maximalIdeal B = Ideal.span (Set.range τ)) ∧
      (MvPolynomial.eval₂Hom ((algebraMap ℂ κ').codRestrict B hB.const_mem) τ).FormallyEtale ∧
      TrBasis (algebraMap ℂ κ') (fun i => (τ i : κ')) := by
  first | exact @GlobalTheory.EtaleCoordLocal.exists_etaleCoords | exact GlobalTheory.EtaleCoordLocal.exists_etaleCoords | (intros; apply GlobalTheory.EtaleCoordLocal.exists_etaleCoords <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlobalGenerationAmplePairMultiples
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.HSNef.AmpleGen

theorem exists_genAt_mul : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → ∀ P : Pair p, IsAmpleLB P.A.B → ∃ c₀ : ℕ, 0 < c₀ ∧ ∀ j : ℕ, GenAt P (c₀ * j) := by
  intro k _ X _ p D _ P hA
  obtain ⟨c, hc, N, s, hs⟩ := hA.exists_isGenerated_pow
  have hrep : P.Rep 0 (c : ℤ) (P.A.pow c) := by
    have := Pair.rep_pow k X p P 0 1 P.A c (Pair.rep_base k X p P).2.1
    simpa using this
  obtain ⟨e, -, hrange, hnu, -⟩ := RepDict.rep_dict k X p P 0 c (P.A.pow c) hrep
  have hmem : ∀ i, e (s i) ∈ P.H 0 c := fun i => by
    have : e (s i) ∈ Set.range e := ⟨s i, rfl⟩
    rw [hrange] at this
    exact this
  have hne : ∀ (σ : k →+* ℂ) (y : CxPts p σ), ∃ i, P.nu 0 c σ y (e (s i)) ≠ 0 := by
    intro σ y
    obtain ⟨i, hi⟩ := exists_mem_ptsIn hs y
    refine ⟨i, fun h0 => ?_⟩
    have h2 := hnu (s i) σ y
    have hpick := mem_pick ((P.A.pow c).φ σ).isLB y
    have hv := (secVal_ne_zero_iff (s i) hpick).2 hi
    have hpos : ((P.A.pow c).φ σ).nsq (secVal p σ (s i)) y ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ (norm_ne_zero_iff.2 hv)) (Real.exp_pos _).ne'
    rw [h0] at h2
    exact hpos (by rw [← h2]; ring)
  refine ⟨c, hc, fun j => ⟨N, fun i => e (s i) ^ j, fun i => ?_, fun σ y => ?_⟩⟩
  · obtain ⟨h1, -⟩ := NuPow.pow_mem_H_and_nu_pow k X p P 0 c (e (s i)) (hmem i) j
    have e1 : (j : ℤ) * 0 = 0 := by ring
    have e2 : (j : ℤ) * c = ((c * j : ℕ) : ℤ) := by push_cast; ring
    rw [e1, e2] at h1
    exact h1
  · obtain ⟨i, hi⟩ := hne σ y
    obtain ⟨-, h2⟩ := NuPow.pow_mem_H_and_nu_pow k X p P 0 c (e (s i)) (hmem i) j
    have e1 : (j : ℤ) * 0 = 0 := by ring
    have e2 : (j : ℤ) * c = ((c * j : ℕ) : ℤ) := by push_cast; ring
    have h3 := h2 σ y
    rw [e1, e2] at h3
    exact ⟨i, by rw [h3]; exact pow_ne_zero _ hi⟩

end GlobalTheory.HSNef.AmpleGen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteProductOfLocalFunctionsUnitaryNeZeroStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.TraceBlocks
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_productOfLocalFunctionsUnitary_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (S : Set (Pl E)) (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ f : ∀ w : Pl E, UL n w → ℂ, IsTest (KL n) K' f → {q : finU (E := E) (n := n) ⧸ globLev S K' | globFn S f q.out ≠ 0}.Finite := by
  first | exact @GlobalTheory.BCT.finite_globFn_ne_zero | exact GlobalTheory.BCT.finite_globFn_ne_zero | (intros; apply GlobalTheory.BCT.finite_globFn_ne_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatTensorSubalgebraMvPolynomialEvalOfFlatAevalStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair GlobalTheory.GraphLocal
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_tensorSubalgebraMvPolynomialEval_of_flat_aeval : ∀ {K κ' : Type} [Field K] [Field κ'] [Algebra ℂ K] [Algebra ℂ κ'] (A : Subalgebra ℂ K)
    (m : ℕ) (v : Fin m → A),
    (MvPolynomial.aeval v : MvPolynomial (Fin m) ℂ →ₐ[ℂ] A).toRingHom.Flat →
    (polyMap (κ' := κ') A v).Flat := by
  first | exact @GlobalTheory.GraphLocal.flat_polyMap_of_flat_aeval | exact GlobalTheory.GraphLocal.flat_polyMap_of_flat_aeval | (intros; apply GlobalTheory.GraphLocal.flat_polyMap_of_flat_aeval <;> assumption)
end

