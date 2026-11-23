module

public import Mathlib
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0028
public import Formalism.LocalToGlobal.ProjectiveLattices.LatPAddRight
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0031
public import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsCompleteIsAlgClosedAddValuation
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.MarkSpec
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Formalism.LocalToGlobal.ProjectiveLattices.PetersonNormSubspace
public import Formalism.LocalToGlobal.ProjectiveLattices.PartitionExtendByZeroAntitone
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0025
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0020
public import Formalism.LocalToGlobal.ProjectiveLattices.DatProofs
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0008
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
public import Formalism.LocalToGlobal.ProjectiveLattices.IntAllProofFree
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0017
public import Formalism.LocalToGlobal.ProjectiveLattices.UnitIndepOfCharts
public import Formalism.LocalToGlobal.ProjectiveLattices.GenFrPf
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.CubicalExtendsSt
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0065

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsEmbeddingCompleteAlgClosedFixedCarrier
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain IsLocalRing ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.MainNotions.DIV.Cons
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SmallClosedField

open Cardinal

theorem mk_le_of_denseRange {A C : Type} [MetricSpace C] (f : A → C) (hf : DenseRange f) :
    #C ≤ #A ^ ℵ₀ := by
  have h : ∀ x : C, ∃ s : ℕ → A, Filter.Tendsto (fun n => f (s n)) Filter.atTop (nhds x) := by
    intro x
    obtain ⟨u, hu, hx⟩ := mem_closure_iff_seq_limit.1 (hf x)
    choose s hs using hu
    exact ⟨s, by simpa [hs] using hx⟩
  choose s hs using h
  have hinj : Function.Injective s := fun x y hxy =>
    tendsto_nhds_unique (hs x) (hxy ▸ hs y)
  simpa using mk_le_of_injective hinj

theorem mk_le_continuum_of_finite_residueField (V : Type) [CommRing V] [IsLocalRing V]
    [IsNoetherianRing V] [Finite (ResidueField V)] : #V ≤ 𝔠 := by
  have hfin : ∀ n : ℕ, Finite (V ⧸ maximalIdeal V ^ n) := fun n =>
    haveI : Finite (V ⧸ maximalIdeal V) := inferInstanceAs (Finite (ResidueField V))
    Ideal.finite_quotient_pow (maximalIdeal V).fg_of_isNoetherianRing n
  let f : V → ∀ n : ℕ, V ⧸ maximalIdeal V ^ n := fun x n => Ideal.Quotient.mk _ x
  have hinj : Function.Injective f := by
    intro x y hxy
    have : x - y ∈ ⨅ n : ℕ, maximalIdeal V ^ n :=
      Ideal.mem_iInf.2 fun n => Ideal.Quotient.eq.1 (congrFun hxy n)
    rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal V).ne_top] at this
    exact sub_eq_zero.1 this
  refine (mk_le_of_injective hinj).trans ?_
  rw [mk_pi]
  refine (prod_le_prod _ (fun _ => ℵ₀) fun n => mk_le_aleph0).trans ?_
  simp

theorem exists_small_closed_subfield {K C : Type} [Field K] [NontriviallyNormedField C]
    [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [Algebra K C] (hK : #K ≤ 𝔠)
    {x : K} (hx : 1 < ‖algebraMap K C x‖) :
    ∃ L : Subfield C, (∀ y : K, algebraMap K C y ∈ L) ∧ IsClosed (L : Set C) ∧ IsAlgClosed L ∧
      #L ≤ 𝔠 := by
  let A := algebraicClosure K C
  let L : Subfield C := A.toSubfield.topologicalClosure
  have hAL : A.toSubfield ≤ L := A.toSubfield.le_topologicalClosure
  have hKL : ∀ y : K, algebraMap K C y ∈ L := fun y => hAL (A.algebraMap_mem y)
  have hcl : IsClosed (L : Set C) := A.toSubfield.isClosed_topologicalClosure
  letI : NontriviallyNormedField L :=
    { (inferInstance : NormedField L) with non_trivial := ⟨⟨_, hKL x⟩, hx⟩ }
  haveI : CompleteSpace L := hcl.completeSpace_coe
  letI : Algebra A L := (Subfield.inclusion hAL : A.toSubfield →+* L).toAlgebra
  have hd : DenseRange (algebraMap A L) :=
    (denseRange_inclusion_iff (s := (A.toSubfield : Set C)) (t := (L : Set C)) hAL).2 subset_rfl
  haveI : IsAlgClosed A := IsAlgClosure.isAlgClosed K
  refine ⟨L, hKL, hcl, isAlgClosed_of_denseRange hd, (mk_le_of_denseRange _ hd).trans ?_⟩
  have hA : #A ≤ 𝔠 :=
    (Algebra.IsAlgebraic.cardinalMk_le_max K A).trans (max_le hK aleph0_le_continuum)
  exact (power_le_power_right hA).trans continuum_power_aleph0.le

theorem exists_scf_isometry {p : ℕ} {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C]
    [CompleteSpace C] [IsAlgClosed C] [CharZero C] (hp : ‖(p : C)‖ = (p : ℝ)⁻¹) (hC : #C ≤ 𝔠) :
    ∃ (D : SCF p) (e : C →+* ↥D.S), ∀ x, ‖e x‖ = ‖x‖ := by
  have hle : #C ≤ #BigT := by
    refine hC.trans ?_
    rw [mk_set, mk_set, mk_real]
    exact (cantor _).le.trans (cantor _).le
  obtain ⟨j⟩ := (Cardinal.le_def _ _).1 hle
  let S : Set BigT := Set.range j
  let e : S ≃ C := (Equiv.ofInjective j j.injective).symm
  letI : Field S := e.field
  let r : S ≃+* C := e.ringEquiv
  letI : NormedField S := NormedField.induced S C r r.injective
  have hn : ∀ x : S, ‖x‖ = ‖r x‖ := fun _ => rfl
  have hn' : ∀ x : C, ‖r.symm x‖ = ‖x‖ := fun x => by rw [hn, r.apply_symm_apply]
  letI : NontriviallyNormedField S :=
    { (inferInstance : NormedField S) with
      non_trivial := by
        obtain ⟨x, hx⟩ := NontriviallyNormedField.non_trivial (α := C)
        exact ⟨r.symm x, (hn' x).symm ▸ hx⟩ }
  haveI : IsUltrametricDist S :=
    IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm fun x y => by
      rw [hn, hn, hn, map_add (f := _)]; exact IsUltrametricDist.norm_add_le_max _ _
  haveI : IsAlgClosed S := IsAlgClosed.of_ringEquiv C S r.symm
  have hiso : Isometry r := AddMonoidHomClass.isometry_of_norm r fun x => (hn x).symm
  haveI : CompleteSpace S :=
    (hiso.isUniformInducing.completeSpace_congr r.surjective).2 inferInstance
  haveI : CharZero S := charZero_of_injective_ringHom (f := r.symm.toRingHom) r.symm.injective
  exact ⟨{ S := S, norm_p := by rw [hn, map_natCast, hp] }, r.symm.toRingHom, hn'⟩

theorem exists_extension_intO {V W C : Type} [CommRing V] [IsDomain V] [CommRing W] [IsDomain W]
    [NormedField C] [IsUltrametricDist C] [IsAlgClosed C] (g : V →+* intO C) (φ : V →+* W)
    (hg : Function.Injective g) (hφ : Function.Injective φ) (hf : φ.Finite) :
    ∃ g' : W →+* intO C, g'.comp φ = g ∧ Function.Injective g' := by
  letI : Algebra V W := φ.toAlgebra
  letI : Algebra V C := ((intO C).subtype.comp g).toAlgebra
  haveI : Module.Finite V W := hf
  have hgC : Function.Injective (algebraMap V C) := Subtype.val_injective.comp hg
  haveI : FaithfulSMul V W := (faithfulSMul_iff_algebraMap_injective V W).2 hφ
  haveI : FaithfulSMul V C := (faithfulSMul_iff_algebraMap_injective V C).2 hgC
  let l : W →ₐ[V] C := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  have hl : Function.Injective l := by
    rw [RingHom.injective_iff_ker_eq_bot]
    refine Ideal.eq_bot_of_comap_eq_bot (R := V) ?_
    rw [eq_bot_iff]
    intro a ha
    rw [Ideal.mem_comap, RingHom.mem_ker, l.commutes] at ha
    exact (map_eq_zero_iff _ hgC).1 ha
  have hmem : ∀ a : W, l a ∈ intO C := by
    intro a
    have hO := normIntegers_integers C
    obtain ⟨q, hq, hqa⟩ := (Algebra.IsIntegral.isIntegral (R := V) a).map l
    let g₀ : V →+* normIntegers C := (algebraMap V C).codRestrict (normIntegers C) fun v =>
      mem_normIntegers_iff.2 (g v).2
    have hint : IsIntegral (normIntegers C) (l a) :=
      ⟨q.map g₀, hq.map g₀, by rw [Polynomial.eval₂_map]; exact hqa⟩
    exact mem_normIntegers_iff.1 (hO.mem_of_integral hint)
  refine ⟨l.toRingHom.codRestrict (intO C) hmem, ?_, fun a b h => hl (congrArg Subtype.val h)⟩
  ext a
  exact l.commutes a

theorem norm_lt_one_of_mem_maximalIdeal {W C : Type} [CommRing W] [IsDomain W]
    [IsDiscreteValuationRing W] [NormedField C] (g : W →+* C) (hg : ∀ a, ‖g a‖ ≤ 1) {b : W}
    (hb0 : b ≠ 0) (hb : ‖g b‖ < 1) {a : W} (ha : a ∈ maximalIdeal W) : ‖g a‖ < 1 := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible W
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hπ
  rw [hπ.maximalIdeal_eq, Ideal.mem_span_singleton] at ha
  obtain ⟨c, hc⟩ : (u : W) * π ^ n ∣ a ^ n := Units.mul_left_dvd.2 (pow_dvd_pow_of_dvd ha n)
  have h : ‖g a‖ ^ n < 1 := by
    rw [← norm_pow, ← map_pow, hc, map_mul, norm_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) hb (hg c)
  exact lt_of_not_ge fun h1 => absurd (one_le_pow₀ h1) (not_le.2 h)

theorem exists_embedding_and_extension :
    ∀ (T : CDVR) (p : ℕ), p.Prime → T.FinRes → (p : T.V) ∈ maximalIdeal T.V → (∃ (C : SCF p) (eF : T.Fr →+* ↥C.S), (∀ a : T.V, ‖eF (algebraMap T.V T.Fr a)‖ ≤ 1) ∧ ∀ a ∈ maximalIdeal T.V, ‖eF (algebraMap T.V T.Fr a)‖ < 1) ∧ ∀ (C : SCF p) (g : T.V →+* intO ↥C.S) (T' : CDVR) (φ : T.V →+* T'.V), Function.Injective g → (∀ a ∈ maximalIdeal T.V, ‖((g a : intO ↥C.S) : ↥C.S)‖ < 1) → Function.Injective φ → φ.Finite → ∃ g' : T'.V →+* intO ↥C.S, g'.comp φ = g ∧ Function.Injective g' ∧ ∀ a ∈ maximalIdeal T'.V, ‖((g' a : intO ↥C.S) : ↥C.S)‖ < 1 := by
  intro T p hp hfin hpm
  have hp0 : (p : T.V) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have h1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  refine ⟨?_, fun C g T' φ hg hgm hφ hf => ?_⟩
  · obtain ⟨C, _, _, _, _, _, hC, hCp⟩ :=
      exists_complete_isAlgClosed_of_isDiscreteValuationRing T.V T.Fr hp0 hpm
        (inv_pos.2 (zero_lt_one.trans h1)) (inv_lt_one_of_one_lt₀ h1)
    haveI : Finite (ResidueField T.V) := hfin
    have hK : #T.Fr ≤ 𝔠 :=
      (IsLocalization.cardinalMk_le (nonZeroDivisors T.V)).trans
        (mk_le_continuum_of_finite_residueField T.V)
    have hx : 1 < ‖algebraMap T.Fr C (algebraMap T.V T.Fr p)⁻¹‖ := by
      rw [map_inv₀, norm_inv, hCp, inv_inv]; exact h1
    obtain ⟨L, hKL, hcl, hac, hL⟩ := exists_small_closed_subfield hK hx
    letI : NontriviallyNormedField L :=
      { (inferInstance : NormedField L) with non_trivial := ⟨⟨_, hKL _⟩, hx⟩ }
    haveI : CompleteSpace L := hcl.completeSpace_coe
    haveI : CharZero T.Fr := charZero_of_injective_ringHom (IsFractionRing.injective T.V T.Fr)
    let i : T.Fr →+* L := (algebraMap T.Fr C).codRestrict L hKL
    have hi : ∀ y, ‖i y‖ = ‖algebraMap T.Fr C y‖ := fun _ => rfl
    haveI : CharZero L := charZero_of_injective_ringHom i.injective
    have hLp : ‖(p : L)‖ = (p : ℝ)⁻¹ := by
      rw [← map_natCast i, hi, ← map_natCast (algebraMap T.V T.Fr), hCp]
    obtain ⟨D, e, he⟩ := exists_scf_isometry hLp hL
    have hle : ∀ a : T.V, ‖(e.comp i) (algebraMap T.V T.Fr a)‖ ≤ 1 := fun a => by
      rw [RingHom.comp_apply, he, hi]; exact (hC _).2 ⟨a, rfl⟩
    refine ⟨D, e.comp i, hle, fun a ha => ?_⟩
    refine norm_lt_one_of_mem_maximalIdeal ((e.comp i).comp (algebraMap T.V T.Fr)) hle hp0 ?_ ha
    rw [map_natCast, D.norm_p]
    exact inv_lt_one_of_one_lt₀ h1
  · obtain ⟨g', hc, hinj⟩ := exists_extension_intO g φ hg hφ hf
    refine ⟨g', hc, hinj, fun a ha => ?_⟩
    refine norm_lt_one_of_mem_maximalIdeal ((intO ↥C.S).subtype.comp g') (fun b => (g' b).2)
      ((map_ne_zero_iff φ hφ).2 hp0) ?_ ha
    have := hgm p hpm
    rw [← hc] at this
    exact this

end GlobalTheory.SmallClosedField
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsDetRoot
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct Topology
open GlobalTheory.RecDict

namespace GlobalTheory.RecDict

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem cmData_sig_ne_id {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E]
    [Algebra F E] (hc : CMData F E) : ∃ a, hc.sig a ≠ a := by
  by_contra h
  push Not at h
  have hs : Function.Surjective (algebraMap F E) := fun a => (hc.fixed a).1 (h a)
  have h1 : Module.finrank F E = 1 :=
    (LinearEquiv.ofBijective (Algebra.linearMap F E)
      ⟨(algebraMap F E).injective, hs⟩).finrank_eq.symm.trans (Module.finrank_self F)
  have := hc.deg2
  omega

theorem exists_isDetRoot : ∀ (D : D7) (V : HSp D) (g : GA D V), ∃ x, IsDetRoot V g x := by
  intro D V g
  let c : D.host.E ≃ₐ[D.host.F] D.host.E :=
    AlgEquiv.ofAlgHom D.sp.cm.sig D.sp.cm.sig
      (AlgHom.ext fun a => star_star a) (AlgHom.ext fun a => star_star a)
  have hc1 : c ≠ 1 := by
    obtain ⟨a, ha⟩ := cmData_sig_ne_id D.sp.cm
    intro h
    exact ha (congrArg (fun f : D.host.E ≃ₐ[D.host.F] D.host.E => f a) h)
  have hu := det_conj_mul V g
  rw [mul_comm] at hu
  exact GlobalTheory.AdLat.hilbert90_adeleRing_tensor_quadratic D.host.F D.host.E c D.sp.cm.deg2 hc1 (Formalism.L2.Theta.mt V g).det hu

end GlobalTheory.RecDict
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLevelSubgroup
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct Topology
open GlobalTheory.RecDict

namespace GlobalTheory.RecDict

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem det_gram_ne_zero {E : Type} [Field E] [NumberField E] [StarRing E] (S : Formalism.BasicNotions.HSpace E) :
    S.gram.det ≠ 0 := by
  intro h
  obtain ⟨v, hv, h0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
  apply hv
  have hy : S.frame.equivFun.symm v = 0 := by
    apply S.nondeg.2
    intro x
    have hi : ∀ i, S.hT (S.frame i) (S.frame.equivFun.symm v) = 0 := by
      intro i
      have := congrFun h0 i
      set_option synthInstance.maxHeartbeats 100000 in
        rw [Module.Basis.equivFun_symm_apply, map_sum]
      simpa [Matrix.mulVec, dotProduct, Formalism.BasicNotions.HSpace.gram, mul_comm] using this
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← S.frame.sum_repr x, map_sum, LinearMap.sum_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, hi, smul_zero]
  exact S.frame.equivFun.symm.map_eq_zero_iff.1 hy

theorem det_mul_sigR_det {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (hJ : J.det ≠ 0) (g : GL (Fin M) (R ⊗[F] E))
    (hg : g ∈ HR R σ J) : g.1.det * sigR R σ g.1.det = 1 := by
  have h : Formalism.UG.cT (sigR R σ) g.1 * JR R J * g.1 = JR R J := hg
  have h2 := congrArg Matrix.det h
  have hu : IsUnit (JR (F := F) R J).det := by
    have : (JR (F := F) R J).det = inclR (F := F) R J.det := ((inclR (F := F) R).map_det J).symm
    rw [this]
    exact (IsUnit.mk0 _ hJ).map _
  have h3 : (Formalism.UG.cT (sigR R σ) g.1).det = sigR R σ g.1.det := by
    rw [Formalism.UG.cT, Matrix.det_transpose]
    exact ((sigR R σ).map_det g.1).symm
  rw [Matrix.det_mul, Matrix.det_mul, h3] at h2
  apply hu.mul_left_cancel
  linear_combination h2

theorem det_finHom_norm {D : D7} (V : HSp D) (k : GA D V) :
    (finHom V k).1.det * sigR (Af D.host.F) D.sp.cm.sig (finHom V k).1.det = 1 := by
  have h := det_mul_sigR_det (AF D.host.F) D.sp.cm.sig V.gram (det_gram_ne_zero V) (matHom V k) k.2
  let φ := (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom
  have e : (finHom V k).1.det = φ (matHom V k).1.det := (φ.map_det _).symm
  have c : ∀ x, sigR (Af D.host.F) D.sp.cm.sig (φ x) = φ (sigR (AF D.host.F) D.sp.cm.sig x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [φ, sigR]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  rw [e, c, ← map_mul, h, map_one]

theorem finHom_inv_mulVec_mem {D : D7} (V : HSp D) (k : GA D V)
    (hk : ∀ z ∈ latHat V, (finHom V k).1.mulVec z ∈ latHat V) :
    ∀ z ∈ latHat V, (finHom V k⁻¹).1.mulVec z ∈ latHat V := by
  let L : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E) :=
    V.L0.map (V.frame.equivFun.toLinearMap.restrictScalars (𝓞 D.host.E))
  have hL : latHat V = GlobalTheory.AdLat.hat D.host.F (L : Set (Fin V.rank → D.host.E)) := by
    unfold Formalism.L2.Pj.latHat GlobalTheory.AdLat.hat
    congr 1
    ext z
    constructor
    · rintro ⟨a, ha, x, hx, rfl⟩
      exact ⟨a, ha, _, ⟨x, hx, rfl⟩, rfl⟩
    · rintro ⟨a, ha, _, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨a, ha, x, hx, rfl⟩
  have hfg : L.FG := V.standardTuple_isLattice.fg.map _
  have hsp : Submodule.span D.host.E (L : Set (Fin V.rank → D.host.E)) = ⊤ := by
    have hspan : Submodule.span D.host.E (V.L0 : Set V.V) = ⊤ := by
      let W := Submodule.span D.host.E (V.L0 : Set V.V)
      change W = ⊤
      by_contra h
      let e : V.V ≃ₗ⋆[D.host.E] V.V :=
        V.frame.equivFun.trans ((starLinearEquiv D.host.E).trans V.frame.equivFun.symm)
      let g : V.V →ₗ[D.host.E] Module.Dual D.host.E W :=
        (LinearMap.domRestrict' W).comp (V.hT.comp e.toLinearMap)
      have hdim : Module.finrank D.host.E (Module.Dual D.host.E W) < Module.finrank D.host.E V.V := by
        rw [Subspace.dual_finrank_eq]
        exact Submodule.finrank_lt h
      obtain ⟨x, hx, hx₀⟩ :=
        Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := g) hdim)
      have hsmul (a : D.host.E) : a • e x ∈ V.L0 := by
        rw [← V.baseLattice_isUnimodular]
        change a • e x ∈ Formalism.E.hdual V.hT V.L0
        simp only [Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
          LinearMap.restrictScalars_apply, Submodule.mem_one]
        intro y hy
        have hxy : V.hT (e x) y = 0 :=
          congrArg (fun f : Module.Dual D.host.E W => f ⟨y, Submodule.subset_span hy⟩)
            (LinearMap.mem_ker.mp hx)
        have hyx : V.hT y (e x) = 0 := by
          have hh := V.herm.eq (e x) y
          simpa [hxy] using hh.symm
        simp [map_smul, hyx]
      let i : D.host.E →ₗ[𝓞 D.host.E] V.L0 :=
        ((LinearMap.toSpanSingleton D.host.E _ (e x)).restrictScalars (𝓞 D.host.E)).codRestrict V.L0 hsmul
      let : Module.Finite (𝓞 D.host.E) V.L0 := Module.Finite.iff_fg.mpr V.standardTuple_isLattice.fg
      let : Module.Finite (𝓞 D.host.E) D.host.E := Module.Finite.of_injective i fun a b hab =>
        smul_left_injective D.host.E (fun hzero => hx₀ (e.map_eq_zero_iff.mp hzero)) (congrArg Subtype.val hab)
      exact RingOfIntegers.not_isField D.host.E
        (isField_of_isIntegral_of_isField (IsFractionRing.injective (𝓞 D.host.E) D.host.E) (Field.toIsField D.host.E))
    have : (L : Set (Fin V.rank → D.host.E)) = V.frame.equivFun.toLinearMap '' (V.L0 : Set V.V) := rfl
    rw [this, Submodule.span_image, hspan, Submodule.map_top, LinearEquiv.range]
  let c : D.host.E ≃ₐ[D.host.F] D.host.E :=
    AlgEquiv.ofBijective D.sp.cm.sig (D.sp.cm.sig.bijective)
  rw [hL] at hk ⊢
  rw [map_inv]
  exact GlobalTheory.AdLat.inv_mulVec_mem_hat _ _ _ L (finHom V k) c hfg hsp hk (det_finHom_norm V k)

theorem exists_level_subgroup {G A : Type} [Group G] [CommRing A] {n : ℕ} (f : G →* GL (Fin n) A) (H : Subgroup G)
    (Λ : AddSubgroup (Fin n → A)) (N : ℕ)
    (hinv : ∀ k : G, (∀ z ∈ Λ, (f k).1.mulVec z ∈ Λ) → ∀ z ∈ Λ, (f k⁻¹).1.mulVec z ∈ Λ) :
    ∃ K : Subgroup G, (∀ k, k ∈ K ↔ k ∈ H ∧ ∀ z ∈ Λ, ∃ y ∈ Λ, (f k).1.mulVec z - z = N • y) ∧
      ∀ k ∈ K, (f k).1.mulVec '' (Λ : Set (Fin n → A)) = Λ := by
  have hin : ∀ k : G, (∀ z ∈ Λ, ∃ y ∈ Λ, (f k).1.mulVec z - z = N • y) →
      ∀ z ∈ Λ, (f k).1.mulVec z ∈ Λ := by
    intro k hk z hz
    obtain ⟨y, hy, e⟩ := hk z hz
    rw [sub_eq_iff_eq_add.1 e]
    exact add_mem (nsmul_mem hy N) hz
  have hmul : ∀ (a b : G) z, (f (a * b)).1.mulVec z = (f a).1.mulVec ((f b).1.mulVec z) := by
    intro a b z
    rw [map_mul, Units.val_mul, Matrix.mulVec_mulVec]
  have hone : ∀ z, (f 1).1.mulVec z = z := by
    intro z
    rw [map_one, Units.val_one, Matrix.one_mulVec]
  refine ⟨{ carrier := {k | k ∈ H ∧ ∀ z ∈ Λ, ∃ y ∈ Λ, (f k).1.mulVec z - z = N • y}
            mul_mem' := ?_
            one_mem' := ?_
            inv_mem' := ?_ }, fun k => Iff.rfl, ?_⟩
  · rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨mul_mem ha hb, fun z hz => ?_⟩
    obtain ⟨y, hy, e⟩ := hb' z hz
    obtain ⟨y', hy', e'⟩ := ha' _ (hin b hb' z hz)
    refine ⟨y' + y, add_mem hy' hy, ?_⟩
    rw [hmul, nsmul_add, ← e, ← e']
    abel
  · exact ⟨one_mem _, fun z _ => ⟨0, zero_mem _, by rw [hone, sub_self, nsmul_zero]⟩⟩
  · rintro a ⟨ha, ha'⟩
    refine ⟨inv_mem ha, fun z hz => ?_⟩
    obtain ⟨y, hy, e⟩ := ha' _ (hinv a (hin a ha') z hz)
    refine ⟨-y, neg_mem hy, ?_⟩
    rw [← hmul, mul_inv_cancel, hone] at e
    rw [neg_nsmul, ← e, neg_sub]
  · rintro k ⟨-, hk⟩
    apply Set.Subset.antisymm
    · rintro _ ⟨z, hz, rfl⟩
      exact hin k hk z hz
    · intro z hz
      exact ⟨_, hinv k (hin k hk) z hz, (hmul k k⁻¹ z).symm.trans (by rw [mul_inv_cancel, hone])⟩

theorem exists_isLevelK : ∀ (D : D7) (V : HSp D) (N : ℕ), ∃ Kf : Subgroup (GA D V), IsLevelK V N Kf ∧ ∀ k ∈ Kf, (finHom V k).1.mulVec '' (latHat V : Set _) = latHat V :=
  fun _ V N => exists_level_subgroup (finHom V) (GfC V) (latHat V) N (finHom_inv_mulVec_mem V)

end GlobalTheory.RecDict
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsModelPushInvertibleOverCompleteDVR
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory

theorem exists_model_pushInvertible_under_cdvr : PartI → N1ab → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ Dw.p + Dw.q → ∀ (T : CDVR) (io : c.F →+* T.Fr) (p : ℕ), p.Prime → (p : T.V) ∈ IsLocalRing.maximalIdeal T.V → l.GoodAt p → ∃ (O : Type) (_ : CommRing O) (β : O →+* c.F) (Y : Model Xo c β), PushInvertible Y.t.G Y.t.PP.L ∧ ∃ b : O →+* T.V, (algebraMap T.V T.Fr).comp b = io.comp β := by
  intro hI hN E _ _ _ H Dw l Xo c hpos T io p hp hpT hg
  classical
  obtain ⟨Xf, hXf⟩ : ∃ Xf : ∀ l' : Level H, Moduli Dw l', Xf l = Xo :=
    ⟨Function.update (fun l' => (hN E H Dw l' hpos).some) l Xo, Function.update_self ..⟩
  subst hXf
  let U₀ : ValuationSubring T.Fr := (ValuationRing.valuation T.V T.Fr).valuationSubring
  have hU₀ : ∀ x : T.Fr, x ∈ U₀ ↔ ∃ a : T.V, algebraMap T.V T.Fr a = x := fun x =>
    ValuationRing.mem_integer_iff T.V T.Fr x
  have hinj : Function.Injective (algebraMap T.V T.Fr) := IsFractionRing.injective _ _
  have hpU : (p : c.F) ∈ (U₀.comap io).nonunits := by
    rw [ValuationSubring.mem_nonunits_iff_or]
    right
    intro h
    rw [ValuationSubring.mem_comap, hU₀] at h
    obtain ⟨a, ha⟩ := h
    have hp0 : (p : c.F) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
    have h1 : a * (p : T.V) = 1 := by
      apply hinj
      rw [map_mul, ha, map_natCast, map_one, ← map_natCast io p, ← map_mul, inv_mul_cancel₀ hp0, map_one]
    exact (IsLocalRing.mem_maximalIdeal _).1 hpT (IsUnit.of_mul_eq_one_right a h1)
  obtain ⟨W, hW, hWU⟩ := GlobalTheory.T.exists_valuationSubring_complex_comap_eq c.F (U₀.comap io) p hpU
  obtain ⟨Y, hY, -⟩ := hI.2 E H Dw hpos Xf
  have hmem : ∀ x : c.V W, ∃ a : T.V, algebraMap T.V T.Fr a = io x := by
    intro x
    have hx : (x : c.F) ∈ U₀.comap io := hWU ▸ x.2
    exact (hU₀ _).1 (ValuationSubring.mem_comap.1 hx)
  choose f hf using hmem
  refine ⟨c.V W, inferInstance, (c.V W).subtype, Y p W hp hW ⟨l, c, hg⟩,
    ((hY p W hp hW).1.1 ⟨l, c, hg⟩).2.2.1, ?_⟩
  refine ⟨{ toFun := f
            map_one' := hinj (by simp [hf])
            map_mul' := fun x y => hinj (by simp [hf])
            map_zero' := hinj (by simp [hf])
            map_add' := fun x y => hinj (by simp [hf]) }, ?_⟩
  ext x
  exact hf x

end GlobalTheory
end

