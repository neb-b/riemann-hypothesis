module

public import Mathlib
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.ExistsIntEKMulVbar
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.GalBasic
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.ExistsDvdQKPowSubOne
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.Bundle0012
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.Bundle0013
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.Bundle0007

@[expose] public section

-- bundled from ReciprocityTheory.ClassFieldTheory.LocalClassField.InvRes
section
namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh Function

variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))

variable {p K L}

noncomputable def trivPull {G G' : Type} [Group G] [TopologicalSpace G] [Group G'] [TopologicalSpace G'] (φ : G' →* G)
    (hφ : Continuous φ) (A : Type) [AddCommGroup A] : Pair (trivRep G A) (trivRep G' A) where
  φ := φ
  u := LinearMap.id
  φ_cont := hφ
  u_cont := continuous_of_discreteTopology
  equiv _ _ := rfl

theorem conn_trivPull {G G' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group G']
    [TopologicalSpace G'] [IsTopologicalGroup G'] (φ : G' →* G) (hφ : Continuous φ) (δ δ')
    (hδ : Cx.IsConn (trivMap G (Int.castAddHom ℚ)).hom
      (trivMap G (QuotientAddGroup.mk' (Int.castAddHom ℚ).range)).hom δ)
    (hδ' : Cx.IsConn (trivMap G' (Int.castAddHom ℚ)).hom
      (trivMap G' (QuotientAddGroup.mk' (Int.castAddHom ℚ).range)).hom δ') (n : ℕ) (x) :
    δ' n ((trivPull φ hφ QZ).hom.H n x) = (trivPull φ hφ ℤ).hom.H (n + 1) (δ n x) :=
  connNat_holds ℤ _ _ _ _ _ _ _ _ _ _ (trivPull φ hφ ℤ).hom (trivPull φ hφ ℚ).hom (trivPull φ hφ QZ).hom δ δ'
    (admissibility_holds ℤ G _ _ _ _ _ (admissible_int_rat_sequence G)) (admissibility_holds ℤ G' _ _ _ _ _ (admissible_int_rat_sequence G'))
    (fun _ _ => rfl) (fun _ _ => rfl) hδ hδ' n x

theorem cocycle_pow {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (x : (trivRep G QZ).coch.X 1) (hx : (trivRep G QZ).coch.d 1 x = 0)
    (g : G) (k : ℕ) : x.1 ![g ^ k] = k • x.1 ![g] := by
  obtain ⟨e, he⟩ := exists_h1_equiv_characters G
  rw [← he x hx, ← he x hx, ofMul_pow, map_nsmul]
  rfl

theorem resGK_mem_subG_Kur (hK : FiniteDimensional ℚ_[p] K) (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L)
    (σ : GK p L) (hσ : σ ∈ subG p L (MaximalUnramifiedExtension p L)) : resGK h σ ∈ subG p K (MaximalUnramifiedExtension p K) :=
  fun x hx => hσ x (Kur_le_Kur L hK hL h hx)

noncomputable def invMap {R : Type} [CommRing R] {G G' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group G']
    [TopologicalSpace G'] [IsTopologicalGroup G'] {M : TRep R G} {M' : TRep R G'} (Q : Pair M M') (N : Subgroup G)
    [N.Normal] (N' : Subgroup G') [N'.Normal] (hN : ∀ g ∈ N', Q.φ g ∈ N) :
    Pair (InflationRestrictionInvariants.invQ M N) (InflationRestrictionInvariants.invQ M' N') where
  φ := QuotientGroup.map N' N Q.φ hN
  u :=
    { toFun := fun x => ⟨Q.u x.1, fun g => by
        have h1 : M.rho (Q.φ g.1) x.1 = x.1 := x.2 ⟨Q.φ g.1, hN g.1 g.2⟩
        show M'.rho g.1 (Q.u x.1) = Q.u x.1
        rw [← Q.equiv, h1]⟩
      map_add' := fun x y => Subtype.ext (map_add Q.u x.1 y.1)
      map_smul' := fun r x => Subtype.ext (map_smul Q.u r x.1) }
  φ_cont := (QuotientGroup.isOpenQuotientMap_mk.isQuotientMap.continuous_iff).2
    (continuous_quot_mk.comp Q.φ_cont)
  u_cont := Continuous.subtype_mk (Q.u_cont.comp continuous_subtype_val) _
  equiv g m := by
    induction g using QuotientGroup.induction_on with
    | H σ => exact Subtype.ext (Q.equiv σ m.1)

theorem invMap_φ {R : Type} [CommRing R] {G G' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group G']
    [TopologicalSpace G'] [IsTopologicalGroup G'] {M : TRep R G} {M' : TRep R G'} (Q : Pair M M') (N : Subgroup G)
    [N.Normal] (N' : Subgroup G') [N'.Normal] (hN : ∀ g ∈ N', Q.φ g ∈ N) (σ : G') :
    (invMap Q N N' hN).φ (QuotientGroup.mk σ) = QuotientGroup.mk (Q.φ σ) := rfl

theorem invMap_u {R : Type} [CommRing R] {G G' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group G']
    [TopologicalSpace G'] [IsTopologicalGroup G'] {M : TRep R G} {M' : TRep R G'} (Q : Pair M M') (N : Subgroup G)
    [N.Normal] (N' : Subgroup G') [N'.Normal] (hN : ∀ g ∈ N', Q.φ g ∈ N) (x : (InflationRestrictionInvariants.invQ M N).V) :
    ((invMap Q N N' hN).u x).1 = Q.u x.1 := rfl

theorem invMap_H {R : Type} [CommRing R] {G G' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group G']
    [TopologicalSpace G'] [IsTopologicalGroup G'] {M : TRep R G} {M' : TRep R G'} (Q : Pair M M') (N : Subgroup G)
    [N.Normal] (N' : Subgroup G') [N'.Normal] (hN : ∀ g ∈ N', Q.φ g ∈ N) (n : ℕ) (x : (InflationRestrictionInvariants.invQ M N).H n) :
    Q.hom.H n ((InflationRestrictionInvariants.invP M N).hom.H n x) =
      (InflationRestrictionInvariants.invP M' N').hom.H n ((invMap Q N N' hN).hom.H n x) := by
  induction x using Cx.H_ind with
  | h x hx => exact Cx.cls_congr _ _ (Subtype.ext (funext fun _ => rfl))

noncomputable def urRes (hK : FiniteDimensional ℚ_[p] K) (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L) :
    Pair (urT p K) (urT p L) :=
  invMap (resPair h) (subG p K (MaximalUnramifiedExtension p K)) (subG p L (MaximalUnramifiedExtension p L)) (resGK_mem_subG_Kur hK hL h)

theorem exists_urRes (hK : FiniteDimensional ℚ_[p] K) (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L) :
    ∃ P : Pair (urT p K) (urT p L), (∀ σ : GK p L, P.φ (QuotientGroup.mk σ) = QuotientGroup.mk (resGK h σ)) ∧
      (∀ x, (P.u x).1 = x.1) ∧
      ∀ n x, (resPair h).hom.H n ((layerInf p K (MaximalUnramifiedExtension p K)).hom.H n x) =
        (layerInf p L (MaximalUnramifiedExtension p L)).hom.H n (P.hom.H n x) := by
  exact ⟨urRes hK hL h, invMap_φ (resPair h) _ _ _, invMap_u (resPair h) _ _ _, invMap_H (resPair h) _ _ _⟩

theorem vLayerMap_urRes (hK : FiniteDimensional ℚ_[p] K) (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L)
    (x : (urT p K).V) (y : (urT p L).V) (hxy : y.1 = x.1) :
    vLayerMap p L (MaximalUnramifiedExtension p L) y = (eLK p K L : ℤ) • vLayerMap p K (MaximalUnramifiedExtension p K) x := by
  apply Int.cast_injective (α := ℝ)
  rw [vLayerMap_spec p (le_Kur (K := L)), smul_eq_mul, Int.cast_mul, vLayerMap_spec p (le_Kur (K := K)), eK_Kur p hK,
    eK_Kur p hL, eK_eq_mul p hL h, hxy]
  push_cast
  ring

theorem invUr_urRes (hK : FiniteDimensional ℚ_[p] K) (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L)
    (P : Pair (urT p K) (urT p L)) (hφ : ∀ σ : GK p L, P.φ (QuotientGroup.mk σ) = QuotientGroup.mk (resGK h σ))
    (hu : ∀ x, (P.u x).1 = x.1) (x : (urT p K).H 2) :
    invUr p L (P.hom.H 2 x) = degLK p K L • invUr p K x := by
  obtain ⟨⟨δ, hδ, -⟩, -⟩ := lES_holds ℤ _ _ _ _ _
    (admissibility_holds ℤ (GalLK p K (MaximalUnramifiedExtension p K)) _ _ _ _ _ (admissible_int_rat_sequence (GalLK p K (MaximalUnramifiedExtension p K))))
  obtain ⟨⟨δ', hδ', -⟩, -⟩ := lES_holds ℤ _ _ _ _ _
    (admissibility_holds ℤ (GalLK p L (MaximalUnramifiedExtension p L)) _ _ _ _ _ (admissible_int_rat_sequence (GalLK p L (MaximalUnramifiedExtension p L))))
  obtain ⟨c, hc⟩ := (conn_int_rat_bijective _ δ hδ 1 one_pos).2 ((vLayer p K (MaximalUnramifiedExtension p K)).hom.H 2 x)
  obtain ⟨χ, hχ, rfl⟩ := Cx.exists_cls c
  have h1 := invUr_eq hK δ hδ x χ hχ hc.symm
  have hv : (vLayer p L (MaximalUnramifiedExtension p L)).hom.H 2 (P.hom.H 2 x) =
      (eLK p K L : ℤ) • (trivPull P.φ P.φ_cont ℤ).hom.H 2 ((vLayer p K (MaximalUnramifiedExtension p K)).hom.H 2 x) := by
    induction x using Cx.H_ind with
    | h z hz =>
      refine Cx.cls_congr _ _ (Subtype.ext (funext fun g => ?_))
      exact vLayerMap_urRes hK hL h _ _ (hu _)
  have hn := conn_trivPull P.φ P.φ_cont δ δ' hδ hδ' 1 (Cx.cls _ 1 χ hχ)
  rw [← hc] at hv
  have hd : (trivRep (GalLK p L (MaximalUnramifiedExtension p L)) QZ).coch.d 1
      ((eLK p K L : ℤ) • (trivPull P.φ P.φ_cont QZ).hom.f 1 χ) = 0 := by
    rw [map_smul, ← Cx.Hom.comm, hχ, map_zero, smul_zero]
  have h2 := invUr_eq hL δ' hδ' (P.hom.H 2 x) ((eLK p K L : ℤ) • (trivPull P.φ P.φ_cont QZ).hom.f 1 χ) hd
    (hv.trans ((congrArg ((eLK p K L : ℤ) • ·) hn.symm).trans (map_smul (δ' 1) _ _).symm))
  have h3 : ((eLK p K L : ℤ) • (trivPull P.φ P.φ_cont QZ).hom.f 1 χ).1 ![frobLK p L (MaximalUnramifiedExtension p L)] =
      eLK p K L • χ.1 ![P.φ (frobLK p L (MaximalUnramifiedExtension p L))] := by
    refine Eq.trans ?_ (natCast_zsmul _ _)
    refine congrArg ((eLK p K L : ℤ) • ·) (congrArg χ.1 (funext fun i => ?_))
    fin_cases i
    rfl
  have h4 : P.φ (frobLK p L (MaximalUnramifiedExtension p L)) = frobLK p K (MaximalUnramifiedExtension p K) ^ fLK p K L :=
    (hφ _).trans (resGK_frobK L hK hL h (qK_eq_pow_fLK p hL h))
  rw [h2, h3, h4, cocycle_pow χ hχ, h1, ← eLK_mul_fLK_eq_degLK p hL h]
  exact (mul_smul (eLK p K L) (fLK p K L) (χ.1 ![frobLK p K (MaximalUnramifiedExtension p K)] : QZ)).symm

theorem exists_res_ur (hK : FiniteDimensional ℚ_[p] K) (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L)
    (x : (urT p K).H 2) : ∃ y : (urT p L).H 2,
      (resPair h).hom.H 2 ((layerInf p K (MaximalUnramifiedExtension p K)).hom.H 2 x) = (layerInf p L (MaximalUnramifiedExtension p L)).hom.H 2 y ∧
      invUr p L y = degLK p K L • invUr p K x := by
  obtain ⟨P, hφ, hu, hP⟩ := exists_urRes hK hL h
  exact ⟨P.hom.H 2 x, hP 2 x, invUr_urRes hK hL h P hφ hu x⟩

end ReciprocityTheory.DiscreteGroups.LocalClassField
end

-- bundled from ReciprocityTheory.ClassFieldTheory.LocalClassField.TransportBC
section
namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ValuativeRel Function

open scoped commutatorElement

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] {p : ℕ} [Fact p.Prime] (m : Model K p)

noncomputable def Model.mapField (L : IntermediateField K (AlgebraicClosure K)) :
    IntermediateField ℚ_[p] (PadicAlgCl p) :=
  (L.toSubfield.map (m.E : AlgebraicClosure K →+* PadicAlgCl p)).toIntermediateField fun x =>
    ⟨algebraMap K _ (m.e.symm (algebraMap ℚ_[p] m.K' x)), L.algebraMap_mem _, by
      show m.E _ = _
      rw [m.comm, RingEquiv.apply_symm_apply]
      rfl⟩

theorem Model.corr_mapField (L : IntermediateField K (AlgebraicClosure K)) : m.Corr L (m.mapField L) := fun x =>
  ⟨by rintro ⟨y, hy, hyx⟩; rwa [← m.E.injective hyx], fun hx => ⟨x, hx, rfl⟩⟩

noncomputable def Model.comapField (L' : IntermediateField ℚ_[p] (PadicAlgCl p)) (h : m.K' ≤ L') :
    IntermediateField K (AlgebraicClosure K) :=
  (L'.toSubfield.comap (m.E : AlgebraicClosure K →+* PadicAlgCl p)).toIntermediateField fun x => by
    show m.E (algebraMap K _ x) ∈ L'
    rw [m.comm]
    exact h (m.e x).2

theorem Model.corr_comapField (L' : IntermediateField ℚ_[p] (PadicAlgCl p)) (h : m.K' ≤ L') :
    m.Corr (m.comapField L' h) L' := fun _ => Iff.rfl

variable {m} {L : IntermediateField K (AlgebraicClosure K)} {L' : IntermediateField ℚ_[p] (PadicAlgCl p)}

theorem Model.Corr.le (h : m.Corr L L') : m.K' ≤ L' := fun x hx => by
  have := (h (algebraMap K _ (m.e.symm ⟨x, hx⟩))).2 (L.algebraMap_mem _)
  rwa [m.comm, RingEquiv.apply_symm_apply] at this

noncomputable def Model.Corr.equiv (h : m.Corr L L') : L ≃+* IntermediateField.extendScalars h.le where
  toFun x := ⟨m.E x, (h x).2 x.2⟩
  invFun y := ⟨m.E.symm y, (h _).1 (by rw [RingEquiv.apply_symm_apply]; exact y.2)⟩
  left_inv x := Subtype.ext (m.E.symm_apply_apply _)
  right_inv y := Subtype.ext (m.E.apply_symm_apply _)
  map_mul' x y := Subtype.ext (map_mul m.E _ _)
  map_add' x y := Subtype.ext (map_add m.E _ _)

theorem Model.Corr.equiv_comp (h : m.Corr L L') :
    (algebraMap m.K' (IntermediateField.extendScalars h.le)).comp (m.e : K →+* m.K') =
      (h.equiv : L →+* IntermediateField.extendScalars h.le).comp (algebraMap K L) :=
  RingHom.ext fun x => Subtype.ext (m.comm x).symm

theorem Model.Corr.equiv_symm_comp (h : m.Corr L L') :
    (algebraMap K L).comp (m.e.symm : m.K' →+* K) =
      (h.equiv.symm : IntermediateField.extendScalars h.le →+* L).comp
        (algebraMap m.K' (IntermediateField.extendScalars h.le)) :=
  RingHom.ext fun x => Subtype.ext (m.E_symm_coe x).symm

theorem Model.Corr.finite_iff (h : m.Corr L L') : FiniteDimensional K L ↔ FiniteDimensional ℚ_[p] L' := by
  constructor
  · intro hL
    have h1 : Module.Finite m.K' (IntermediateField.extendScalars h.le) :=
      Module.Finite.of_equiv_equiv m.e h.equiv h.equiv_comp
    have := m.fin
    have h2 : FiniteDimensional ℚ_[p] (IntermediateField.extendScalars h.le) :=
      FiniteDimensional.trans ℚ_[p] m.K' _
    exact h2
  · intro hL'
    have := finDim_extendScalars_of_le p hL' h.le
    exact Module.Finite.of_equiv_equiv m.e.symm h.equiv.symm h.equiv_symm_comp

theorem Model.Corr.norm_eq (h : m.Corr L L') (z : L) :
    m.e (Algebra.norm K z) = Algebra.norm m.K' (h.equiv z) := by
  rw [Algebra.norm_eq_of_equiv_equiv m.e h.equiv h.equiv_comp, RingEquiv.apply_symm_apply]

theorem Model.mem_fixingSubgroup_iff_model {φ} (hφ : m.IsGalIso φ) (h : m.Corr L L')
    (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) : g ∈ L.fixingSubgroup ↔ φ g ∈ subG p m.K' L' := by
  rw [IntermediateField.mem_fixingSubgroup_iff, mem_subG_iff]
  constructor
  · intro hg y hy
    have hx : m.E.symm y ∈ L := (h _).1 (by rwa [RingEquiv.apply_symm_apply])
    have := hφ g (m.E.symm y)
    rwa [hg _ hx, RingEquiv.apply_symm_apply] at this
  · intro hg x hx
    apply m.E.injective
    rw [← hφ]
    exact hg _ ((h x).2 hx)

theorem Model.abelian_restriction_eq_one_iff {φ} (hφ : m.IsGalIso φ) (h : m.Corr L L') (hL : IsFiniteAbelian K L)
    (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :
    abRestrict K L hL (toAb K g) = 1 ↔ φ g ∈ subG p m.K' L' := by
  have := hL.isGalois
  rw [abRestrict_mk, ← Model.mem_fixingSubgroup_iff_model hφ h g, ← IntermediateField.restrictNormalHom_ker,
    MonoidHom.mem_ker]

theorem map_commutator_mulEquiv {G H : Type*} [Group G] [Group H] (φ : G ≃* H) :
    (commutator G).map (φ : G →* H) = commutator H := by
  rw [commutator_def, commutator_def, Subgroup.map_commutator, Subgroup.map_top_of_surjective _ φ.surjective]

theorem Model.isFiniteAbelian_iff_model (h : m.Corr L L') : IsFiniteAbelian K L ↔ IsAbLK p m.K' L' := by
  have hφ := m.isGalIso_galIso
  constructor
  · intro hL
    refine ⟨h.le, h.finite_iff.1 hL.finiteDimensional, ?_⟩
    intro τ hτ
    rw [← map_commutator_mulEquiv m.galIso] at hτ
    obtain ⟨g, hg, rfl⟩ := hτ
    show m.galIso g ∈ _
    rw [← Model.abelian_restriction_eq_one_iff hφ h hL]
    have h1 : toAb K g = 1 :=
      (QuotientGroup.eq_one_iff (N := Subgroup.topologicalClosure (commutator (Field.absoluteGaloisGroup K))) g).2
        (Subgroup.le_topologicalClosure (G := Field.absoluteGaloisGroup K) _ hg)
    rw [h1, map_one]
  · intro hL'
    have := m.charZero
    have hfd := h.finite_iff.2 hL'.fin
    have hn : L.fixingSubgroup.Normal := by
      have h1 : L.fixingSubgroup = (subG p m.K' L').comap m.galIso.toMonoidHom := by
        ext g
        exact Model.mem_fixingSubgroup_iff_model hφ h g
      rw [h1]
      have := hL'.normal
      infer_instance
    have hG : IsGalois K L := (InfiniteGalois.normal_iff_isGalois L).1 hn
    refine ⟨hfd, hG, fun a b => ?_⟩
    obtain ⟨g, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (AlgebraicClosure K) a
    obtain ⟨g', rfl⟩ := AlgEquiv.restrictNormalHom_surjective (AlgebraicClosure K) b
    rw [← map_mul, ← map_mul, ← inv_mul_eq_one, ← map_inv, ← map_mul, ← MonoidHom.mem_ker,
      IntermediateField.restrictNormalHom_ker, Model.mem_fixingSubgroup_iff_model hφ h]
    apply hL'.comm
    have h2 : (g * g')⁻¹ * (g' * g) = ⁅g'⁻¹, g⁻¹⁆ := by
      rw [commutatorElement_def]; group
    rw [h2, map_commutatorElement]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

theorem Model.mem_normGroup_iff_model (h : m.Corr L L') (hL : FiniteDimensional K L) (x : Kˣ) :
    x ∈ normGroup K L ↔ m.eU x ∈ normGrp p m.K' L' := by
  have hL' := h.finite_iff.1 hL
  rw [mem_normGrp_iff]
  constructor
  · rintro ⟨y, rfl⟩
    let y' : (PadicAlgCl p)ˣ := Units.map (m.E : AlgebraicClosure K →* PadicAlgCl p)
      (Units.map (algebraMap L (AlgebraicClosure K) : L →* AlgebraicClosure K) y)
    have hy' : (Additive.ofMul y' : KbarMult p) ∈ multOf p L' := (h _).2 y.1.2
    refine ⟨Additive.ofMul y', hy', ?_⟩
    refine Additive.toMul.injective (Units.ext ?_)
    refine (normHom_eq_algebraNorm hL' h.le _ hy').trans ?_
    exact congrArg Subtype.val (h.norm_eq (y : L)).symm
  · rintro ⟨y, hy, hyx⟩
    let w : IntermediateField.extendScalars h.le := ⟨((Additive.toMul y : (PadicAlgCl p)ˣ) : PadicAlgCl p), hy⟩
    have hw : w ≠ 0 := fun h0 => (Additive.toMul y : (PadicAlgCl p)ˣ).ne_zero (congrArg Subtype.val h0)
    have hz : h.equiv.symm w ≠ 0 := by simpa using hw
    refine ⟨Units.mk0 _ hz, Units.ext (m.e.injective (Subtype.ext ?_))⟩
    show ((m.e (Algebra.norm K (h.equiv.symm w)) : m.K') : PadicAlgCl p) = _
    rw [h.norm_eq, RingEquiv.apply_symm_apply, ← normHom_eq_algebraNorm hL' h.le y hy, hyx]
    rfl

end ReciprocityTheory.DiscreteGroups.LocalClassField
end

