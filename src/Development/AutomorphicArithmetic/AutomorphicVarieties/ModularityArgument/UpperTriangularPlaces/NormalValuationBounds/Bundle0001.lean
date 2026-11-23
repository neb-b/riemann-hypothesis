module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.UpperTriangularPlaces.Bundle0001
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FrobeniusFields.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LMemMax
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.WeightKernels.TwistRatios.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.UpperTriangularPlaces.NormalValuationBounds.CharpolyScalar
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Polynomial Module UpperTheory.V.Z.Win

namespace UpperTheory.V.Keep

section linear

variable {k : Type} [Field k] [IsAlgClosed k]

private theorem common_eig {V : Type} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (S : Set (End k V)) (hS : ∀ f ∈ S, ∀ f' ∈ S, f * f' = f' * f) :
    ∀ (d : ℕ) (W : Submodule k V), finrank k W = d → W ≠ ⊥ → (∀ f ∈ S, ∀ x ∈ W, f x ∈ W) →
      ∃ v ∈ W, v ≠ 0 ∧ ∀ f ∈ S, ∃ c : k, f v = c • v :=
  _root_.UpperTheory.Reformulated.B.CommonEigenvectorOfCommutingSet.common_eig S hS

private theorem charpoly_scalar {W : Type} [AddCommGroup W] [Module k W] [FiniteDimensional k W] (hW : finrank k W = 1)
    (f : End k W) (c : k) (hf : ∀ x, f x = c • x) : f.charpoly = X - C c := by
  have hs : f = c • (1 : End k W) := LinearMap.ext fun x => by simp [hf]
  rw [hs, ← LinearMap.charpoly_toMatrix _ (Module.finBasisOfFinrankEq k W hW), map_smul]
  have : LinearMap.toMatrix (Module.finBasisOfFinrankEq k W hW) (Module.finBasisOfFinrankEq k W hW) (1 : End k W) = 1 :=
    LinearMap.toMatrix_one _
  rw [this, Matrix.smul_one_eq_diagonal, Matrix.charpoly_diagonal]
  simp

private theorem chars_of_comm {Γ : Type} [Group Γ] :
    ∀ (d : ℕ) (V : Type) [AddCommGroup V] [Module k V] [FiniteDimensional k V] (ρ : Γ →* End k V),
      (∀ a b, ρ a * ρ b = ρ b * ρ a) → finrank k V = d →
      ∃ χ : Fin d → Γ →* kˣ, ∀ g, (ρ g).charpoly = ∏ i, (X - C (χ i g : k)) := by
  intro d
  induction d with
  | zero =>
    intro V _ _ _ ρ _ hd
    refine ⟨fun i => i.elim0, fun g => ?_⟩
    simpa using eq_one_of_monic_natDegree_zero (LinearMap.charpoly_monic (ρ g))
      (by rw [LinearMap.charpoly_natDegree, hd])
  | succ d ih =>
    intro V _ _ _ ρ hc hd
    haveI : Nontrivial V := Module.nontrivial_of_finrank_pos (R := k) (by omega)
    obtain ⟨v, -, hv0, hv⟩ := common_eig (Set.range ρ)
      (by rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩; exact hc a b) _ ⊤ rfl top_ne_bot (fun _ _ _ _ => trivial)
    choose c hcv using fun g => hv (ρ g) ⟨g, rfl⟩
    have inj : ∀ a b : k, a • v = b • v → a = b := fun a b h => smul_left_injective k hv0 h
    let c0 : Γ →* k :=
      { toFun := c
        map_one' := inj _ _ (by rw [← hcv, map_one]; simp)
        map_mul' := fun a b => inj _ _ (by
          rw [← hcv, map_mul, Module.End.mul_apply, hcv b, map_smul, hcv a, smul_smul, mul_comm]) }
    let W : Submodule k V := Submodule.span k {v}
    have hvW : v ∈ W := Submodule.mem_span_singleton_self v
    have hW : ∀ g, ∀ x ∈ W, ρ g x ∈ W := by
      intro g x hx
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hx
      rw [map_smul, hcv]
      exact W.smul_mem _ (W.smul_mem _ hvW)
    let ρ' : Γ →* End k (V ⧸ W) :=
      { toFun := fun g => W.mapQ W (ρ g) (fun x hx => hW g x hx)
        map_one' := by
          refine LinearMap.ext fun x => ?_
          obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective W x
          simp
        map_mul' := fun a b => by
          refine LinearMap.ext fun x => ?_
          obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective W x
          simp [Module.End.mul_apply] }
    have hW1 : finrank k W = 1 := finrank_span_singleton hv0
    have hq : finrank k (V ⧸ W) = d := by
      have := Submodule.finrank_quotient_add_finrank W
      omega
    obtain ⟨χ, hχ⟩ := ih (V ⧸ W) ρ' (fun a b => by
      refine LinearMap.ext fun x => ?_
      obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective W x
      have h1 : ρ a (ρ b y) = ρ b (ρ a y) := LinearMap.congr_fun (hc a b) y
      simp [ρ', Module.End.mul_apply, h1]) hq
    refine ⟨Fin.cons c0.toHomUnits χ, fun g => ?_⟩
    rw [Fin.prod_univ_succ, GlobalTheory.CuspGL.charpoly_eq_restrict_mul_mapQ W (ρ g) (hW g)]
    simp only [Fin.cons_zero, Fin.cons_succ]
    congr 1
    · refine charpoly_scalar hW1 _ _ fun x => Subtype.ext ?_
      obtain ⟨x, hx⟩ := x
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hx
      show ρ g (a • v) = c g • a • v
      rw [map_smul, hcv, smul_comm]
    · exact hχ g

private theorem chars_of_gl {Γ : Type} [Group Γ] {n : ℕ} (ρ : Γ →* Matrix.GeneralLinearGroup (Fin n) k)
    (hc : ∀ a b, ρ a * ρ b = ρ b * ρ a) :
    ∃ χ : Fin n → Γ →* kˣ, ∀ g, (ρ g : Matrix (Fin n) (Fin n) k).charpoly = ∏ i, (X - C (χ i g : k)) := by
  let φ : Γ →* End k (Fin n → k) :=
    { toFun := fun g => Matrix.toLin' (ρ g : Matrix (Fin n) (Fin n) k)
      map_one' := by simp; rfl
      map_mul' := fun a b => by simp [Matrix.toLin'_mul]; rfl }
  obtain ⟨χ, h⟩ := chars_of_comm n (Fin n → k) φ (fun a b => by
    show Matrix.toLin' _ * Matrix.toLin' _ = Matrix.toLin' _ * Matrix.toLin' _
    have h1 := congrArg (fun x : Matrix.GeneralLinearGroup (Fin n) k => (x : Matrix (Fin n) (Fin n) k)) (hc a b)
    simp only [Units.val_mul] at h1
    refine LinearMap.ext fun x => ?_
    simp only [Module.End.mul_apply, Matrix.toLin'_apply, Matrix.mulVec_mulVec, h1]) (by simp)
  refine ⟨χ, fun g => ?_⟩
  rw [← h g]
  have := LinearMap.charpoly_toMatrix (φ g) (Pi.basisFun k (Fin n))
  rw [← this, LinearMap.toMatrix_eq_toMatrix']
  show _ = (LinearMap.toMatrix' (Matrix.toLin' _)).charpoly
  rw [LinearMap.toMatrix'_toLin']

end linear

section extend

variable {k : Type} [Field k] [IsAlgClosed k] [CharZero k]

private theorem extend_char {Γ Q : Type} [Group Γ] [CommGroup Q] [Finite Q] (f : Γ →* Q) (χ : Γ →* kˣ)
    (h : f.ker ≤ χ.ker) : ∃ ψ : Q →* kˣ, ψ.comp f = χ := by
  haveI : NeZero (Monoid.exponent Q) := ⟨Monoid.exponent_ne_zero_of_finite⟩
  have hk : f.rangeRestrict.ker ≤ χ.ker := by rwa [MonoidHom.ker_rangeRestrict]
  let χ' : f.range →* kˣ := f.rangeRestrict.liftOfSurjective f.rangeRestrict_surjective ⟨χ, hk⟩
  obtain ⟨ψ, hψ⟩ := MonoidHom.restrict_surjective k f.range χ'
  refine ⟨ψ, MonoidHom.ext fun g => ?_⟩
  have h1 : χ' (f.rangeRestrict g) = χ g :=
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ ⟨χ, hk⟩ g
  rw [← h1, ← hψ]
  rfl

private theorem descend [TopologicalSpace k] {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] {n : ℕ} (r : Γ →* Matrix.GeneralLinearGroup (Fin n) k) (H : Subgroup Γ) (hH : IsOpen (H : Set Γ))
    (hc : commutator Γ ≤ H) (I D : Subgroup Γ) (ht : ∀ g ∈ I, g ∈ H → r g = 1) :
    ∃ κ : Fin n → ↥D →* kˣ, (∀ i, Continuous (κ i)) ∧ ∀ g : ↥D, (g : Γ) ∈ I →
      (r g : Matrix (Fin n) (Fin n) k).charpoly = ∏ i, (X - C (κ i g : k)) := by
  have hcm : ∀ a b : Γ, a * b * a⁻¹ * b⁻¹ ∈ H := fun a b =>
    hc (Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b))
  haveI hN : H.Normal := ⟨fun h hh g => by
    have h1 := H.mul_mem (hcm g h) hh
    simpa [mul_assoc] using h1⟩
  haveI : Finite (Γ ⧸ H) := Subgroup.quotient_finite_of_isOpen H hH
  letI : CommGroup (Γ ⧸ H) :=
    { (QuotientGroup.Quotient.group H) with
      mul_comm := fun x y => by
        induction x using QuotientGroup.induction_on with | _ a =>
        induction y using QuotientGroup.induction_on with | _ b =>
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
        have h1 := hcm b⁻¹ a⁻¹
        simpa [mul_assoc] using h1 }
  let π : Γ →* Γ ⧸ H := QuotientGroup.mk' H
  have hπ : ∀ g, π g = 1 ↔ g ∈ H := fun g => QuotientGroup.eq_one_iff g
  have hcomm : ∀ a b : ↥I, (r.comp I.subtype) a * (r.comp I.subtype) b = (r.comp I.subtype) b * (r.comp I.subtype) a := by
    intro a b
    have h1 : r ((a : Γ) * b * (a : Γ)⁻¹ * (b : Γ)⁻¹) = 1 :=
      ht _ (I.mul_mem (I.mul_mem (I.mul_mem a.2 b.2) (I.inv_mem a.2)) (I.inv_mem b.2)) (hcm a b)
    simp only [map_mul, map_inv] at h1
    simp only [MonoidHom.comp_apply, Subgroup.subtype_apply]
    have h2 := mul_inv_eq_one.1 h1
    exact mul_inv_eq_iff_eq_mul.1 h2
  obtain ⟨χ, hχ⟩ := chars_of_gl (r.comp I.subtype) hcomm
  have hker : ∀ i, (π.comp I.subtype).ker ≤ (χ i).ker := by
    intro i g hg
    have hgH : (g : Γ) ∈ H := (hπ _).1 hg
    have h1 := hχ g
    have h2 : (r.comp I.subtype) g = 1 := ht _ g.2 hgH
    rw [h2, Units.val_one, Matrix.charpoly_one] at h1
    have h3 := congrArg (Polynomial.eval ((χ i g : kˣ) : k)) h1
    rw [Polynomial.eval_prod, Finset.prod_eq_zero (Finset.mem_univ i) (by simp)] at h3
    simp only [eval_pow, eval_sub, eval_X, eval_one] at h3
    have h4 : ((χ i g : kˣ) : k) - 1 = 0 := (pow_eq_zero_iff (by have := i.pos; simp; omega)).1 h3
    exact Units.ext (sub_eq_zero.1 h4)
  choose ψ hψ using fun i => extend_char (π.comp I.subtype) (χ i) (hker i)
  refine ⟨fun i => ((ψ i).comp π).comp D.subtype, fun i => ?_, fun g hg => ?_⟩
  · have hcont : Continuous ((ψ i).comp π) := by
      refine IsLocallyConstant.continuous ((IsLocallyConstant.iff_exists_open _).2 fun x =>
        ⟨(fun y => x⁻¹ * y) ⁻¹' (H : Set Γ), hH.preimage (continuous_const.mul continuous_id), ?_, fun y hy => ?_⟩)
      · simp [H.one_mem]
      · have h1 : π (x⁻¹ * y) = 1 := (hπ _).2 hy
        have h2 : π y = π x := by
          rw [map_mul, map_inv] at h1
          exact (inv_mul_eq_one.1 h1).symm
        simp [h2]
    exact hcont.comp continuous_subtype_val
  · have h1 := hχ ⟨g, hg⟩
    simp only [MonoidHom.comp_apply, Subgroup.subtype_apply] at h1 ⊢
    rw [h1]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← hψ i]
    rfl

end extend

theorem ineOf : IneOf := by
  intro Ω _ _ _ l _ n r H hH hc ht v hv A hA
  have hl : ¬ A.valuation (l : Ω) < 1 := by
    intro h
    refine hv ((hA ((l : ℕ) : 𝓞 ℚ)).1 ?_)
    simpa using h
  exact descend r H hH hc (Ine (F := ℚ) A) (Dec (F := ℚ) A) (ht A hl)

end UpperTheory.V.Keep
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.UpperTriangularPlaces.NormalValuationBounds.CommLeRbar
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Z.Win

private theorem comm_le_fix {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] (F : IntermediateField k Ω)
    (hF : IsAbelianGalois k F) : commutator (Ω ≃ₐ[k] Ω) ≤ F.fixingSubgroup := by
  haveI : Normal k F := IsGalois.to_normal
  rw [← IntermediateField.restrictNormalHom_ker]
  rw [commutator_def, Subgroup.commutator_le]
  intro a _ b _
  rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
  exact hF.toIsMulCommutative.is_comm.comm _ _

private theorem comm_le_rbar {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
    (D : Raw Ω c) (hD : D.Good) : commutator (G ℚ Ω) ≤ D.rbar.ker := by
  have hb := (UpperTheory.V.Ws.barFacts D hD).2.2.2.2.2.1
  intro g hg
  have h1 : g ∈ D.ξ.ker := Abelianization.commutator_subset_ker D.ξ hg
  have h2 : g ∈ D.Psi.ker := Abelianization.commutator_subset_ker D.Psi hg
  rw [MonoidHom.mem_ker] at h1 h2 ⊢
  rw [hb]
  simp [Raw.bar, h1, h2]

theorem UpperTheory.V.Keep.ineQ : UpperTheory.V.Keep.IneQ := by
  unfold UpperTheory.V.Keep.IneQ
  intro hI Ω _ _ _ l _ c D T hD c' h X y _ r hr
  haveI := T.nF
  haveI := T.abF
  apply hI Ω l 4 r.toHomUnits (T.F.fixingSubgroup ⊓ D.rbar.ker)
  · rw [Subgroup.coe_inf]
    exact (IntermediateField.fixingSubgroup_isOpen T.F).inter
      (UpperTheory.V.GradeZeroInterpolatingElement.facts D hD).2.2.2.2.2.2.2.2.2.2.2.1
  · exact le_inf (comm_le_fix T.F T.abF) (comm_le_rbar D hD)
  · intro A hA g hgA hgH
    obtain ⟨hF, hK⟩ := Subgroup.mem_inf.mp hgH
    obtain ⟨s, rfl⟩ := UpperTheory.V.Ws.exists_resQ hF
    have hs : s ∈ (T.fr ∅).N := ⟨A, by simpa [Raw.Away] using hA, (resQ_Ine T.F A s).mpr hgA, hK⟩
    have h1 : X.P.r s = 1 := X.pair.kill s hs
    have h2 : r (resQ T.F s) = (X.P.map ↑y).r s := by rw [← hr]; rfl
    apply Units.ext
    rw [MonoidHom.coe_toHomUnits, h2]
    simp [PD.map, mapRep, h1]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.UpperTriangularPlaces.NormalValuationBounds.ExistsNormal
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Z.Win

namespace UpperTheory.V.Keep

section tri

variable {k : Type} [Field k]

private theorem tri_mul (X Y : Matrix (Fin 4) (Fin 4) k) (hX : ∀ i j, j < i → X i j = 0) (hY : ∀ i j, j < i → Y i j = 0) :
    (∀ i j, j < i → (X * Y) i j = 0) ∧ ∀ i, (X * Y) i i = X i i * Y i i := by
  constructor
  · intro i j hij
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun b _ => ?_
    rcases lt_or_ge b i with h | h
    · rw [hX i b h, zero_mul]
    · rw [hY b j (hij.trans_le h), mul_zero]
  · intro i
    rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · intro b _ hb
      rcases lt_or_gt_of_ne hb with h | h
      · rw [hX i b h, zero_mul]
      · rw [hY b i h, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ i) h

private theorem flag_of {Γ : Type} [Group Γ] (H : Subgroup Γ) (r : Γ →* GL (Fin 4) k) (a : GL (Fin 4) k)
    (h : ∀ g ∈ H, ∀ i j, j < i → (a * r g * a⁻¹ : GL (Fin 4) k) i j = 0) :
    ∃ κ : Fin 4 → ↥H →* kˣ, Af.IsFlagOn r H κ := by
  let q : Fin 4 → ↥H →* k := fun i =>
    { toFun := fun g => (a * r g * a⁻¹ : GL (Fin 4) k) i i
      map_one' := by simp
      map_mul' := fun x y => by
        have e : (a * r ((x * y : ↥H) : Γ) * a⁻¹ : GL (Fin 4) k) =
            (a * r x * a⁻¹) * (a * r y * a⁻¹) := by
          simp only [Subgroup.coe_mul, map_mul]
          group
        rw [e, Units.val_mul]
        exact (tri_mul _ _ (h x x.2) (h y y.2)).2 i }
  exact ⟨fun i => (q i).toHomUnits, a, fun s => ⟨h s s.2, fun i => rfl⟩⟩

private theorem tri_step {Γ : Type} [Group Γ] (hU : UpTri) (r : Γ →* GL (Fin 4) k) (a : GL (Fin 4) k) (s g : Γ)
    (d : Fin 4 → k) (hd : Function.Injective d)
    (h1 : ∀ i j, j < i → (a * r s * a⁻¹ : GL (Fin 4) k) i j = 0)
    (h1' : ∀ i j, j < i → (a * r (g * s * g⁻¹) * a⁻¹ : GL (Fin 4) k) i j = 0)
    (h2 : ∀ i, (a * r s * a⁻¹ : GL (Fin 4) k) i i ^ 2 = d i)
    (h2' : ∀ i, (a * r (g * s * g⁻¹) * a⁻¹ : GL (Fin 4) k) i i ^ 2 = d i) :
    ∀ i j, j < i → (a * r g * a⁻¹ : GL (Fin 4) k) i j = 0 := by
  set X : GL (Fin 4) k := a * r s * a⁻¹ with hX
  set Y : GL (Fin 4) k := a * r (g * s * g⁻¹) * a⁻¹ with hY
  set B : GL (Fin 4) k := a * r g * a⁻¹ with hB
  have hBX : B * (X * X) = (Y * Y) * B := by
    simp only [hX, hY, hB, map_mul, map_inv]
    group
  have t1 := tri_mul (X : Matrix (Fin 4) (Fin 4) k) X h1 h1
  have t2 := tri_mul (Y : Matrix (Fin 4) (Fin 4) k) Y h1' h1'
  refine hU k 4 ((X : Matrix (Fin 4) (Fin 4) k) * X) ((Y : Matrix (Fin 4) (Fin 4) k) * Y) B d hd t1.1 t2.1
    (fun i => by rw [t1.2, ← sq, h2]) (fun i => by rw [t2.2, ← sq, h2']) ?_
  have := congrArg (Units.val) hBX
  simpa only [Units.val_mul] using this

end tri

section gal

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω]

private theorem exists_normal (F : IntermediateField ℚ Ω) [NumberField F] (U : Subgroup (G F Ω))
    (hU : IsOpen (U : Set (G F Ω))) :
    ∃ N : Subgroup (G ℚ Ω), N.Normal ∧ IsOpen (N : Set (G ℚ Ω)) ∧ ∀ s ∈ N, ∃ u ∈ U, resQ F u = s := by
  obtain ⟨E, hE, hEU⟩ := (krullTopology_mem_nhds_one_iff F Ω U).1 (hU.mem_nhds U.one_mem)
  haveI : FiniteDimensional F E := hE
  haveI : FiniteDimensional ℚ E := Module.Finite.trans F E
  let E' : IntermediateField ℚ Ω := E.restrictScalars ℚ
  haveI : FiniteDimensional ℚ E' := ‹FiniteDimensional ℚ E›
  haveI : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  obtain ⟨N, hN⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
    (IntermediateField.fixingSubgroup_isOpen E') E'.fixingSubgroup.one_mem
  refine ⟨N.toSubgroup, inferInstance, N.isOpen', fun s hs => ?_⟩
  have hsE : ∀ x ∈ E, s x = x := fun x hx =>
    (IntermediateField.mem_fixingSubgroup_iff E' s).1 (hN hs) x hx
  let u : G F Ω := { s.toRingEquiv with commutes' := fun x => hsE _ (E.algebraMap_mem x) }
  refine ⟨u, hEU ?_, by ext x; rfl⟩
  exact (IntermediateField.mem_fixingSubgroup_iff E u).2 hsE

private theorem ine_res (F : IntermediateField ℚ Ω) [NumberField F] (A : ValuationSubring Ω) (u : G F Ω)
    (h : resQ F u ∈ Ine (F := ℚ) A) : u ∈ Ine (F := F) A := by
  obtain ⟨h1, h2⟩ := h
  exact ⟨h1, h2⟩

end gal

end UpperTheory.V.Keep

theorem UpperTheory.V.Keep.flagQ :
    UpperTheory.V.Keep.FlagQ := by
  intro hInf hUp Ω _ _ _ l _ c D T hD r hfl v hv A hA
  have hl : A.valuation (l : Ω) < 1 := by
    have := (hA ((l : ℕ) : 𝓞 ℚ)).2 hv
    simpa using this
  obtain ⟨κ, hκ⟩ := hfl A hl
  obtain ⟨a, ha⟩ := hκ.flag
  obtain ⟨U, hUo, hw⟩ := hκ.wts
  obtain ⟨N, hNn, hNo, hNU⟩ := UpperTheory.V.Keep.exists_normal T.F U hUo
  obtain ⟨s, ⟨hsN, hsI⟩, hso⟩ := hInf ℚ Ω l A hl N hNo
  refine UpperTheory.V.Keep.flag_of _ _ a fun g hg => ?_
  have key : ∀ t ∈ N, t ∈ Ine (F := ℚ) A → cycBar ℚ Ω l t = cycBar ℚ Ω l s →
      (∀ i j, j < i → (a * r.toHomUnits t * a⁻¹ : GL (Fin 4) (Qbar l)) i j = 0) ∧
      ∀ i, (a * r.toHomUnits t * a⁻¹ : GL (Fin 4) (Qbar l)) i i ^ 2 =
        ((cycBar ℚ Ω l s ^ (2 * (D.wts4 i : ℤ)) : (Qbar l)ˣ) : Qbar l) := by
    intro t htN htI hc
    obtain ⟨u, huU, rfl⟩ := hNU t htN
    have huI := UpperTheory.V.Keep.ine_res T.F A u htI
    have huD : u ∈ Dec (F := T.F) A := Ine_le_Dec A huI
    obtain ⟨e1, e2⟩ := ha ⟨u, huD⟩
    refine ⟨e1, fun i => ?_⟩
    have e3 := hw i ⟨u, huD⟩ ⟨huU, huI⟩
    rw [← hc]
    have e4 : (a * r.toHomUnits (resQ T.F u) * a⁻¹ : GL (Fin 4) (Qbar l)) i i = (κ i ⟨u, huD⟩ : Qbar l) := e2 i
    rw [e4, ← Units.val_pow_eq_pow_val, e3]
    rfl
  have hinj : Function.Injective fun i : Fin 4 =>
      ((cycBar ℚ Ω l s ^ (2 * (D.wts4 i : ℤ)) : (Qbar l)ˣ) : Qbar l) := by
    intro i j e
    have e2 := injective_zpow_iff_not_isOfFinOrder.2 hso (Units.val_injective e)
    have := hD.two_le
    fin_cases i <;> fin_cases j <;> simp [Raw.wts4] at e2 ⊢ <;> omega
  have ht := key s hsN hsI rfl
  have hc : cycBar ℚ Ω l (g * s * g⁻¹) = cycBar ℚ Ω l s := by
    rw [map_mul, map_mul, map_inv, mul_comm (cycBar ℚ Ω l g), mul_inv_cancel_right]
  have ht' := key (g * s * g⁻¹) (hNn.conj_mem s hsN g) (conj_mem_Ine hg hsI) hc
  exact UpperTheory.V.Keep.tri_step hUp r.toHomUnits a s g _ hinj ht.1 ht'.1 ht.2 ht'.2
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.UpperTriangularPlaces.NormalValuationBounds.InfCyc
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Z.Win

theorem UpperTheory.V.Keep.infCyc :
    UpperTheory.V.Keep.InfCyc := by
  intro F Ω _ _ _ _ _ l _ A hA U hU
  obtain ⟨s, hsU, hsI, hs⟩ := UpperTheory.V.Z.Sym.Ga.ineInf F Ω l A hA U hU
  exact ⟨s, ⟨hsU, hsI⟩, hs⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.UpperTriangularPlaces.NormalValuationBounds.MemDec
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Z.Win

namespace UpperTheory.V.Keep

private theorem mem_dec {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {A : ValuationSubring Ω} {s : G F Ω}
    (h : ∀ x, s x ∈ A ↔ x ∈ A) : s ∈ Dec (F := F) A := by
  open Pointwise in
  rw [ReciprocityTheory.Gal.mem_Dec]
  ext x
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  have key := h (s⁻¹ • x)
  have e : s (s⁻¹ • x) = x := ReciprocityTheory.Gal.mul_inv_apply x
  rw [e] at key
  exact key.symm

end UpperTheory.V.Keep

theorem UpperTheory.V.Keep.unlL :
    UpperTheory.V.Keep.UnlL := by
  intro Ω _ _ _ l _ c D T hD ho r h w hw A hA
  have hl : A.valuation (l : Ω) < 1 := by
    have h' := (hA ((l : ℕ) : 𝓞 T.L)).2 hw
    simpa using h'
  obtain ⟨κ, hκ, hne⟩ := h A hl
  let ρ : ↥(Dec (F := T.L) A) →* ↥(Dec (F := T.F) A) :=
    ((resLe T.F_le).comp (Dec (F := T.L) A).subtype).codRestrict _ fun s =>
      UpperTheory.V.Keep.mem_dec fun x => apply_mem_iff_of_mem_Dec s.2 x
  have hρ : Function.Surjective ρ := by
    intro s
    have hd : resQ T.F s.1 ∈ Dec (F := ℚ) A := UpperTheory.V.Keep.mem_dec fun x => apply_mem_iff_of_mem_Dec s.2 x
    have hK : resQ T.F s.1 ∈ T.K.fixingSubgroup := ho.split l hD.l_mem A hl hd
    have hF : resQ T.F s.1 ∈ T.F.fixingSubgroup := fun x => s.1.commutes x
    have hLf : resQ T.F s.1 ∈ T.L.fixingSubgroup := by
      rw [T.hL, IntermediateField.fixingSubgroup_sup]
      exact ⟨hF, hK⟩
    let t : G T.L Ω := AlgEquiv.ofRingEquiv (f := s.1.toRingEquiv) fun x => hLf x
    refine ⟨⟨t, UpperTheory.V.Keep.mem_dec fun x => apply_mem_iff_of_mem_Dec s.2 x⟩, Subtype.ext (AlgEquiv.ext fun x => rfl)⟩
  refine ⟨fun i => (κ i).comp ρ, ?_, fun i j e => hne i j (MonoidHom.ext fun s => ?_)⟩
  · obtain ⟨g, hg⟩ := hκ.flag
    exact ⟨g, fun s => hg (ρ s)⟩
  · obtain ⟨t, rfl⟩ := hρ s
    exact DFunLike.congr_fun e t
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.UpperTriangularPlaces.NormalValuationBounds.UpTri
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Z.Win

theorem UpperTheory.V.Keep.upTri :
    UpperTheory.V.Keep.UpTri := by
  intro k _ n M M' B d hd hM hM' hMd hM'd hB
  have key : ∀ m : ℕ, ∀ i j : Fin n, j.val + (n - i.val) = m → j < i → B i j = 0 := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro i j hm hji
      have h1 : (B * M) i j = B i j * d j := by
        rw [Matrix.mul_apply, Finset.sum_eq_single j, hMd]
        · intro b _ hb
          rcases lt_or_gt_of_ne hb with h | h
          · have hv : b.val < j.val := h
            rw [ih (b.val + (n - i.val)) (by omega) i b rfl (h.trans hji), zero_mul]
          · rw [hM b j h, mul_zero]
        · intro h
          exact absurd (Finset.mem_univ j) h
      have h2 : (M' * B) i j = d i * B i j := by
        rw [Matrix.mul_apply, Finset.sum_eq_single i, hM'd]
        · intro b _ hb
          rcases lt_or_gt_of_ne hb with h | h
          · rw [hM' i b h, zero_mul]
          · have hv : i.val < b.val := h
            have hb' : b.val < n := b.isLt
            rw [ih (j.val + (n - b.val)) (by omega) b j rfl (hji.trans h), mul_zero]
        · intro h
          exact absurd (Finset.mem_univ i) h
      have h3 : B i j * (d j - d i) = 0 := by
        rw [hB, h2] at h1
        rw [mul_sub, ← h1, mul_comm, sub_self]
      rcases mul_eq_zero.mp h3 with h | h
      · exact h
      · exact absurd (hd (sub_eq_zero.mp h)) hji.ne
  intro i j hji
  exact key _ i j rfl hji
end

