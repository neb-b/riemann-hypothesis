module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedIsCrysAndJumpEqZero
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TupleActions.InstMulActionTup
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RealTransport.RealTransport
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RTwist
public import Formalism.LocalToGlobal.UnitaryNorms.CharTransport
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ConclusionAbsPow
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0022
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0034

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.GaloisRepresentationIntegralLattice
section
open Module Topology

private theorem span_padicInt_fg_of_bounded {l : ℕ} [Fact (Nat.Prime l)] {n : ℕ} (S : Set (Fin n → ℚ_[l])) (C : ℝ)
    (hS : ∀ v ∈ S, ‖v‖ ≤ C) : (Submodule.span ℤ_[l] S).FG := by
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : Nat.Prime l).one_lt
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt C hl
  let φ : (Fin n → ℤ_[l]) →ₗ[ℤ_[l]] (Fin n → ℚ_[l]) :=
    { toFun := fun c i => ((l : ℚ_[l]) ^ (-(k : ℤ))) * (c i : ℚ_[l])
      map_add' := by
        intro a b
        ext i
        simp [mul_add]
      map_smul' := by
        intro r a
        ext i
        simp [Algebra.smul_def]
        ring }
  refine Submodule.FG.of_le (Submodule.fg_range φ) ?_
  rw [Submodule.span_le]
  intro v hv
  have hbound : ∀ i, ‖(l : ℚ_[l]) ^ (k : ℤ) * v i‖ ≤ 1 := by
    intro i
    rw [norm_mul, Padic.norm_p_zpow]
    have h1 : ‖v i‖ ≤ (l : ℝ) ^ k := (norm_le_pi_norm v i).trans ((hS v hv).trans hk.le)
    calc (l : ℝ) ^ (-(k : ℤ)) * ‖v i‖ ≤ (l : ℝ) ^ (-(k : ℤ)) * (l : ℝ) ^ k := by gcongr
      _ = 1 := by
        rw [zpow_neg, ← zpow_natCast, inv_mul_cancel₀]
        exact (zpow_pos (by linarith) _).ne'
  refine ⟨fun i => ⟨(l : ℚ_[l]) ^ (k : ℤ) * v i, hbound i⟩, ?_⟩
  ext i
  show ((l : ℚ_[l]) ^ (-(k : ℤ))) * ((l : ℚ_[l]) ^ (k : ℤ) * v i) = v i
  have hne : (l : ℚ_[l]) ≠ 0 := by exact_mod_cast (Fact.out : Nat.Prime l).ne_zero
  rw [← mul_assoc, ← zpow_add₀ hne]
  simp

private theorem extendOfIsLattice_repr_eq_repr {l : ℕ} [Fact (Nat.Prime l)] {n m : ℕ}
    (L : Submodule ℤ_[l] (Fin n → ℚ_[l])) [Submodule.IsFullLattice ℚ_[l] L]
    (b : Module.Basis (Fin m) ℤ_[l] L) (y : L) (i : Fin m) :
    (b.extendOfIsFullLattice ℚ_[l]).repr (y : Fin n → ℚ_[l]) i = (b.repr y i : ℚ_[l]) := by
  conv_lhs => rw [← b.sum_repr y]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Submodule.coe_sum, map_sum, Finset.sum_apply']
  simp_rw [Submodule.coe_smul_of_tower]
  have h : ∀ j, (b.repr y j • (b j : Fin n → ℚ_[l])) = ((b.repr y j : ℚ_[l]) • b.extendOfIsFullLattice ℚ_[l] j) := by
    intro j
    rw [Module.Basis.extendOfIsFullLattice_apply, algebra_compatible_smul ℚ_[l]]
    rfl
  simp_rw [h, map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul]
  simp

theorem UpperTheory.galois_representation_integral_lattice :
    UpperTheory.V.Af.Wd.IntBasis := by
  intro l _ Γ _ _ _ V _ _ _ _ _ ρ hρ
  set n := Module.finrank ℚ_[l] V
  let e0 : Module.Basis (Fin n) ℚ_[l] V := Module.finBasis ℚ_[l] V
  let E : V ≃ₗ[ℚ_[l]] (Fin n → ℚ_[l]) := e0.equivFun
  let A : Γ → (Fin n → ℚ_[l]) →ₗ[ℚ_[l]] (Fin n → ℚ_[l]) := fun g =>
    E.toLinearMap ∘ₗ ρ g ∘ₗ E.symm.toLinearMap
  have hA1 : ∀ x, A 1 x = x := by
    intro x
    simp [A]
  have hAmul : ∀ g h x, A (g * h) x = A g (A h x) := by
    intro g h x
    simp [A, map_mul]
  have hEc : Continuous E := IsModuleTopology.continuous_of_linearMap E.toLinearMap
  let f : Γ → Fin n → (Fin n → ℚ_[l]) := fun g j => A g (Pi.single j 1)
  have hf : Continuous f := by
    refine continuous_pi fun j => ?_
    have : (fun g => f g j) = fun g => E (ρ g (E.symm (Pi.single j 1))) := rfl
    rw [this]
    exact hEc.comp (hρ _)
  obtain ⟨C, hC⟩ := (isCompact_range hf).isBounded.exists_norm_le
  let S : Set (Fin n → ℚ_[l]) := Set.range fun p : Γ × Fin n => A p.1 (Pi.single p.2 1)
  let L : Submodule ℤ_[l] (Fin n → ℚ_[l]) := Submodule.span ℤ_[l] S
  have hfg : L.FG := by
    refine span_padicInt_fg_of_bounded S C ?_
    rintro v ⟨⟨g, j⟩, rfl⟩
    exact (norm_le_pi_norm (f g) j).trans (hC _ ⟨g, rfl⟩)
  have hsingle : ∀ j : Fin n, (Pi.single j 1 : Fin n → ℚ_[l]) ∈ L := by
    intro j
    have : (Pi.single j 1 : Fin n → ℚ_[l]) = A 1 (Pi.single j 1) := (hA1 _).symm
    rw [this]
    exact Submodule.subset_span ⟨(1, j), rfl⟩
  have hspan : Submodule.span ℚ_[l] (L : Set (Fin n → ℚ_[l])) = ⊤ := by
    rw [eq_top_iff, ← (Pi.basisFun ℚ_[l] (Fin n)).span_eq]
    refine Submodule.span_mono ?_
    rintro v ⟨j, rfl⟩
    simpa using hsingle j
  have : Submodule.IsLattice ℚ_[l] L := Submodule.IsLattice.of_fg ℚ_[l] hfg
  have : Submodule.IsFullLattice ℚ_[l] L := ⟨hspan⟩
  have hstab : ∀ g, ∀ x ∈ L, (A g).restrictScalars ℤ_[l] x ∈ L := by
    intro g
    have : L ≤ L.comap ((A g).restrictScalars ℤ_[l]) := by
      rw [Submodule.span_le]
      rintro v ⟨⟨h, j⟩, rfl⟩
      show A g (A h (Pi.single j 1)) ∈ L
      rw [← hAmul]
      exact Submodule.subset_span ⟨(g * h, j), rfl⟩
    exact fun x hx => this hx
  have : Module.Free ℤ_[l] L := Submodule.IsLattice.free ℚ_[l] L
  have : Module.Finite ℤ_[l] L := Submodule.IsLattice.finite ℚ_[l] L
  let b0 := Module.Free.chooseBasis ℤ_[l] L
  let b : Module.Basis (Fin (Fintype.card (Module.Free.ChooseBasisIndex ℤ_[l] L))) ℤ_[l] L :=
    b0.reindex (Fintype.equivFin _)
  let e' := b.extendOfIsFullLattice ℚ_[l]
  let e := e'.map E.symm
  let R : Γ →* Module.End ℤ_[l] L :=
    { toFun := fun g => ((A g).restrictScalars ℤ_[l]).restrict (hstab g)
      map_one' := by
        ext x
        simp [LinearMap.restrict_apply, hA1]
      map_mul' := by
        intro g h
        ext x
        simp [LinearMap.restrict_apply, hAmul] }
  let M : Γ →* Matrix _ _ ℤ_[l] := (LinearMap.toMatrixAlgEquiv b).toMonoidHom.comp R
  have key : ∀ (g : Γ) (i j), ((M g i j : ℤ_[l]) : ℚ_[l]) = (e.repr ((ρ g) (e j))) i := by
    intro g i j
    have h1 : M g i j = b.repr (R g (b j)) i := by
      simp [M, LinearMap.toMatrixAlgEquiv_apply]
    have h2 : e.repr ((ρ g) (e j)) i = e'.repr (A g (b j)) i := by
      simp [e, e', A, Module.Basis.map_repr, Module.Basis.map_apply]
    have h3 : (A g (b j : Fin n → ℚ_[l])) = ((R g (b j) : L) : Fin n → ℚ_[l]) := rfl
    rw [h1, h2, h3, extendOfIsLattice_repr_eq_repr]
  refine ⟨_, e, M, ?_, key⟩
  refine continuous_pi fun i => continuous_pi fun j => ?_
  refine (isometry_subtype_coe.isEmbedding.continuous_iff).2 ?_
  have : (fun g => ((M g i j : ℤ_[l]) : ℚ_[l])) = fun g => e.coord i (ρ g (e j)) := by
    funext g
    rw [key]
    rfl
  show Continuous (fun g => ((M g i j : ℤ_[l]) : ℚ_[l]))
  rw [this]
  exact (IsModuleTopology.continuous_of_linearMap (e.coord i)).comp (hρ _)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.GoodRealFormOfRealPartOfRealInvolution
section
open NumberField UpperTheory.V UpperTheory.V.KT UpperTheory.V.Af.BA in
theorem UpperTheory.good_real_form_of_real_part_of_real_involution :
    UpperTheory.V.Af.BA.RePart → UpperTheory.V.Af.BA.ReInv → UpperTheory.V.Af.BA.GoodRe := by
  intro hRP hRI L _ _ _ N σ hσ
  have G := UpperTheory.V.KT.good L N
  have hqc : ∀ (y : NZ L N) (k : HS L N), qc L N y k = q k (y : Lat L N) := fun y k => by
    simp [qc, ev_apply]
  have hpoly : ∀ h : HR L N, h ∈ ConeExtensionAcyclic.poly (qr L N) → (h : HS L N) ∈ ConeExtensionAcyclic.poly (qc L N) :=
    fun h hh y => by
      have := hh y
      rw [qr_apply] at this
      rw [hqc]
      exact this
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h hh
    obtain ⟨S, hS, hev⟩ := G.locFin _ (hpoly h hh)
    refine ⟨S, hS, ?_⟩
    have := (continuous_subtype_val.tendsto h).eventually hev
    filter_upwards [this] with h' hh' y hy
    rw [qr_apply, ← hqc]
    exact hh' y hy
  · obtain ⟨k, hk⟩ := G.nonempty
    obtain ⟨k', hk', -⟩ := hRP L N σ hσ k
    have hinv := (hRI L N σ hσ).1
    refine ⟨k', fun y => ?_⟩
    have hne : sLat σ (y : Lat L N) ≠ 0 := by
      intro h0
      apply y.2
      funext a
      have := congrFun h0 a
      simp only [sLat, Pi.zero_apply] at this
      show (y : Lat L N) a = 0
      rw [← hinv ((y : Lat L N) a), this, map_zero]
    have h1 := hk y
    have h2 := hk ⟨_, hne⟩
    rw [hqc] at h1 h2
    rw [qr_apply, hk']
    have h2' : 1 ≤ q k (sLat σ (y : Lat L N)) := h2
    linarith
  · exact G.closed.preimage continuous_subtype_val
  · intro c hc k hk
    exact G.smul_mem c hc _ hk
  · intro h hh
    exact G.sub (hpoly h hh)
  · obtain ⟨x, hx⟩ := G.pos
    refine ⟨x.comp (HR L N).subtypeL, fun k hk hk0 => ?_⟩
    exact hx _ hk (fun h => hk0 (Subtype.ext h))
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.HeckeCharAlgebraicOfSign
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Published
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc

section Real

variable {E : Type} [Field E] [NumberField E] [IsTotallyReal E]

private noncomputable def diagR (E : Type) [Field E] [NumberField E] [IsTotallyReal E] : E →+* TR.Rinf E :=
  (TR.pInf E).comp (algebraMap E (Ad E))

private theorem infDiag_eqR (k : Eˣ) : infDiag k = TR.infId E (Units.map (diagR E).toMonoidHom k) := by
  classical
  have h : ((infDiag k : Ideles E) : AdeleRing (𝓞 E) E) = (algebraMap E (InfiniteAdeleRing E) k, 1) := by
    unfold infDiag
    rw [MonoidHom.finsetProd_apply, Units.coe_prod]
    let ι : (∀ w : InfinitePlace E, w.Completion) →* AdeleRing (𝓞 E) E :=
      MonoidHom.inl (InfiniteAdeleRing E) (FiniteAdeleRing (𝓞 E) E)
    change ∏ w : InfinitePlace E, ι (Pi.mulSingle w (algebraMap E w.Completion k)) =
      ι (fun w => algebraMap E w.Completion k)
    rw [← map_prod, Finset.univ_prod_mulSingle]
  apply Units.ext
  rw [h]
  refine Prod.ext ?_ ?_
  · change _ = 1 - TR.infEq E 1 + TR.infEq E ((TR.infEq E).symm (algebraMap E (InfiniteAdeleRing E) k))
    simp
  · change (1 : Af E) = 1 - 0 + 0
    simp

private theorem denseRange_diagR : DenseRange (diagR E) := by
  have hc : Continuous (TR.infEq E).symm := continuous_pi fun w =>
    (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)).continuous.comp
      (continuous_apply w)
  exact (TR.infEq E).symm.surjective.denseRange.comp (InfiniteAdeleRing.denseRange_algebraMap E) hc

private theorem denseRange_unitsR : DenseRange (Units.map (diagR E).toMonoidHom) := by
  refine dense_iff_inter_open.2 fun U hU ⟨u, hu⟩ => ?_
  obtain ⟨k, v, hv, hk⟩ := denseRange_diagR.exists_mem_open (Units.isOpenEmbedding_val.isOpenMap U hU) ⟨_, u, hu, rfl⟩
  have h0 : k ≠ 0 := by
    rintro rfl
    exact v.ne_zero (hk.trans (map_zero _))
  exact ⟨v, hv, Units.mk0 k h0, Units.ext hk.symm⟩

private theorem diagR_mk (φ : E →+* ℂ) (k : E) : ((diagR E k (InfinitePlace.mk φ) : ℝ) : ℂ) = φ k := by
  have hr := IsTotallyReal.isReal (InfinitePlace.mk φ)
  have e : diagR E k (InfinitePlace.mk φ) = InfinitePlace.embedding_of_isReal hr k := by
    change InfinitePlace.Completion.extensionEmbeddingOfIsReal hr
      (algebraMap E (InfinitePlace.mk φ).Completion k) = _
    rw [AbsoluteValue.Completion.algebraMap_def, WithAbs.algebraMap_right_apply]
    exact InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe hr (WithAbs.toAbs _ k)
  rw [e, InfinitePlace.embedding_of_isReal_apply,
    InfinitePlace.embedding_mk_eq_of_isReal (InfinitePlace.isReal_mk_iff.1 hr)]

private theorem chiInf_pos {χ : HChar E} {n : (E →+* ℂ) → ℤ} (h : IsAlgPos χ n) (u : (TR.Rinf E)ˣ)
    (hu : ∀ v, 0 < u.val v) :
    ((TR.chiInf χ u : ℂˣ) : ℂ) = ∏ φ : E →+* ℂ, ((u.val (InfinitePlace.mk φ) : ℝ) : ℂ) ^ n φ := by
  have hc : ∀ v, Continuous fun u : (TR.Rinf E)ˣ => u.val v := fun v => (continuous_apply v).comp Units.continuous_val
  have ho : IsOpen {u : (TR.Rinf E)ˣ | ∀ v, 0 < u.val v} := by
    rw [Set.setOf_forall]
    exact isOpen_iInter_of_finite fun v => isOpen_lt continuous_const (hc v)
  have hcl : IsClosed {u : (TR.Rinf E)ˣ |
      ((TR.chiInf χ u : ℂˣ) : ℂ) = ∏ φ : E →+* ℂ, ((u.val (InfinitePlace.mk φ) : ℝ) : ℂ) ^ n φ} :=
    isClosed_eq (Units.continuous_val.comp (TR.continuous_chiInf χ)) (continuous_finsetProd _ fun φ _ =>
      (Complex.continuous_ofReal.comp (hc _)).zpow₀ _ fun u => Or.inl
        (Complex.ofReal_ne_zero.2 (TR.unit_ne_zero u _)))
  refine closure_minimal ?_ hcl (denseRange_unitsR.open_subset_closure_inter ho hu)
  rintro _ ⟨hk, k, rfl⟩
  have h1 := h k fun φ => by
    have h2 := hk (InfinitePlace.mk (Complex.ofRealHom.comp φ))
    have h3 := diagR_mk (Complex.ofRealHom.comp φ) (k : E)
    exact h2.trans_eq (Complex.ofReal_injective h3)
  rw [HChar.inf, MonoidHom.comp_apply, infDiag_eqR] at h1
  refine h1.trans (Finset.prod_congr rfl fun φ _ => ?_)
  exact congrArg (· ^ n φ) (diagR_mk φ (k : E)).symm

open Classical in
private noncomputable def negAt (v : InfinitePlace E) : (TR.Rinf E)ˣ :=
  Units.map (MonoidHom.mulSingle (fun _ : InfinitePlace E => ℝ) v) (-1)

private theorem infId_negAt (v : InfinitePlace E) : TR.infId E (negAt v) = ReciprocityTheory.Neutral.Bridge.HCFR.infIdele E v (-1) := by
  classical
  apply Units.ext
  refine Prod.ext ?_ ?_
  · change 1 - TR.infEq E 1 + TR.infEq E (Pi.mulSingle v (-1)) = Pi.mulSingle v (-1)
    rw [map_one, sub_self]
    refine (zero_add _).trans (funext fun w => ?_)
    change (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)).symm
      ((Pi.mulSingle v (-1) : TR.Rinf E) w) = _
    by_cases h : w = v
    · subst h
      rw [Pi.mulSingle_eq_same, Pi.mulSingle_eq_same, map_neg, map_one]
    · rw [Pi.mulSingle_eq_of_ne h, Pi.mulSingle_eq_of_ne h, map_one]
  · change (1 : Af E) - 0 + 0 = 1
    simp

private theorem bij_mk : Function.Bijective (InfinitePlace.mk : (E →+* ℂ) → InfinitePlace E) := by
  refine ⟨fun φ ψ h => ?_, fun w => ⟨w.embedding, w.mk_embedding⟩⟩
  rw [← InfinitePlace.embedding_mk_eq_of_isReal (IsTotallyReal.complexEmbedding_isReal φ), h,
    InfinitePlace.embedding_mk_eq_of_isReal (IsTotallyReal.complexEmbedding_isReal ψ)]

private theorem chiInf_all {χ : HChar E} {b : ℤ} (h : IsAlgPos χ fun _ => b)
    (hs : ∀ v : InfinitePlace E, χ.locInf v (-1) = (-1) ^ b) (u : (TR.Rinf E)ˣ) :
    ((TR.chiInf χ u : ℂˣ) : ℂ) = ∏ φ : E →+* ℂ, ((u.val (InfinitePlace.mk φ) : ℝ) : ℂ) ^ b := by
  classical
  let s : (TR.Rinf E)ˣ := ∏ v, if u.val v < 0 then negAt v else 1
  have h1 : ∀ w, s.val w = if u.val w < 0 then -1 else 1 := fun w => by
    simp only [s, Units.coe_prod, Finset.prod_apply]
    rw [Finset.prod_eq_single w _ fun hw => absurd (Finset.mem_univ w) hw]
    · split_ifs
      · exact Pi.mulSingle_eq_same (M := fun _ : InfinitePlace E => ℝ) w _
      · rfl
    · intro v _ hv
      split_ifs
      · exact Pi.mulSingle_eq_of_ne (M := fun _ : InfinitePlace E => ℝ) hv.symm _
      · rfl
  have h2 : ((TR.chiInf χ s : ℂˣ) : ℂ) = ∏ φ : E →+* ℂ, ((s.val (InfinitePlace.mk φ) : ℝ) : ℂ) ^ b := by
    rw [bij_mk.prod_comp fun w => ((s.val w : ℝ) : ℂ) ^ b]
    simp only [h1]
    simp only [s, map_prod, Units.coe_prod]
    refine Finset.prod_congr rfl fun v _ => ?_
    split_ifs
    · have e : TR.chiInf χ (negAt v) = χ.locInf v (-1) := congrArg χ.1 (infId_negAt v)
      rw [e, hs]
      simp
    · simp
  have h3 := chiInf_pos h (s * u) fun w => by
    change 0 < s.val w * u.val w
    rw [h1]
    split_ifs with hw
    · linarith
    · rw [one_mul]
      exact lt_of_le_of_ne (not_lt.1 hw) (TR.unit_ne_zero u w).symm
  rw [map_mul, Units.val_mul] at h3
  refine mul_left_cancel₀ (TR.chiInf χ s).ne_zero (h3.trans ?_)
  rw [h2, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun φ _ => ?_
  rw [← mul_zpow, ← Complex.ofReal_mul]
  rfl

end Real

theorem UpperTheory.heckeChar_algebraic_of_sign :
    UpperTheory.V.Af.Cr.AlgOfSign := by
  intro F _ _ _ χ b h hs k
  rw [HChar.inf, MonoidHom.comp_apply, infDiag_eqR]
  refine (chiInf_all h hs _).trans (Finset.prod_congr rfl fun φ _ => ?_)
  exact congrArg (· ^ b) (diagR_mk φ (k : F))
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.HeckeCharRealTransport
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Published
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc
open ReciprocityTheory.Neutral.Bridge.HCFR

private theorem comap_surj {E L : Type} [Field E] [Field L] (j : E ≃+* L) (v' : InfinitePlace E) :
    ∃ v : InfinitePlace L, v.comap j.toRingHom = v' := by
  refine ⟨v'.comap j.symm.toRingHom, ?_⟩
  ext x
  show v' (j.symm (j x)) = v' x
  rw [RingEquiv.symm_apply_apply]

private theorem comap_inj {E L : Type} [Field E] [Field L] (j : E ≃+* L) (u v : InfinitePlace L)
    (h : u.comap j.toRingHom = v.comap j.toRingHom) : u = v := by
  ext x
  have h1 : (u.comap j.toRingHom) (j.symm x) = (v.comap j.toRingHom) (j.symm x) := by rw [h]
  change u (j (j.symm x)) = v (j (j.symm x)) at h1
  rwa [RingEquiv.apply_symm_apply] at h1

private theorem idMap_infIdele {E L : Type} [Field E] [NumberField E] [Field L] [NumberField L] (j : E ≃+* L)
    (v : InfinitePlace L) :
    CT.idMap j (infIdele E (v.comap j.toRingHom) (-1)) = infIdele L v (-1) := by
  classical
  apply Units.ext
  apply Prod.ext
  · funext u
    show CT.infEquiv j u (Pi.mulSingle (M := fun w : InfinitePlace E => w.Completion) (v.comap j.toRingHom) (-1)
      (u.comap j.toRingHom)) = Pi.mulSingle (M := fun w : InfinitePlace L => w.Completion) v (-1) u
    by_cases h : u = v
    · subst h
      rw [Pi.mulSingle_eq_same, Pi.mulSingle_eq_same, map_neg, map_one]
    · have h' : u.comap j.toRingHom ≠ v.comap j.toRingHom := fun e => h (comap_inj j u v e)
      rw [Pi.mulSingle_eq_of_ne h', Pi.mulSingle_eq_of_ne h, map_one]
  · show CT.finMap j 1 = 1
    exact map_one _

theorem UpperTheory.heckeChar_realTransport :
    UpperTheory.V.Af.Cr.RealTransport := by
  intro F K _ _ _ _ _ _ _ h2 χ
  haveI : Algebra.IsQuadraticExtension F K := { finrank_eq_two' := h2 }
  let j : maximalRealSubfield K ≃+* F := (CMExtension.equivMaximalRealSubfield F K).symm
  refine ⟨CT.transport j χ, fun v' => ?_, fun w => ?_⟩
  · obtain ⟨v, rfl⟩ := comap_surj j v'
    refine ⟨v, ?_⟩
    show χ.1 (CT.idMap j (infIdele _ (v.comap j.toRingHom) (-1))) = χ.1 (infIdele F v (-1))
    rw [idMap_infIdele]
  · have hp : CT.plMap j (w.under (𝓞 (maximalRealSubfield K))) = w.under (𝓞 F) := by
      ext x
      show algebraMap (𝓞 (maximalRealSubfield K)) (𝓞 K) ((RingOfIntegers.mapRingEquiv j).symm x) ∈ w.asIdeal ↔
        algebraMap (𝓞 F) (𝓞 K) x ∈ w.asIdeal
      have e : algebraMap (𝓞 (maximalRealSubfield K)) (𝓞 K) ((RingOfIntegers.mapRingEquiv j).symm x) =
          algebraMap (𝓞 F) (𝓞 K) x := RingOfIntegers.ext rfl
      rw [e]
    refine ⟨?_, fun hu => ?_⟩
    · have h := CT.absNorm_plMap j (w.under (𝓞 (maximalRealSubfield K)))
      rw [hp, Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply] at h
      exact h.symm
    · rw [← hp] at hu
      refine ⟨(CT.transport_unrAt_iff j χ _).mpr hu, ?_⟩
      rw [CT.transport_val j χ _ hu, hp]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IrreducibleConstituentOfLevelWeilDeligneEqCharac
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N ValuativeRel
open GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem eq_one_of_charpoly_dvd {V V' : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V'] (f : Module.End ℂ V)
    (hf : f.IsSemisimple) (hd : f.charpoly ∣ (1 : Module.End ℂ V').charpoly) : f = 1 := by
  rw [LinearMap.charpoly_one] at hd
  obtain ⟨q, hq⟩ := hd
  have h0 := congrArg (Polynomial.aeval f) hq
  rw [map_mul, LinearMap.aeval_self_charpoly, zero_mul, map_pow, map_sub, Polynomial.aeval_X,
    map_one] at h0
  have hs : (f - algebraMap ℂ (Module.End ℂ V) 1).IsSemisimple :=
    Module.End.isSemisimple_sub_algebraMap_iff.2 hf
  rw [map_one] at hs
  exact sub_eq_zero.1 (Module.End.eq_zero_of_isNilpotent_isSemisimple ⟨_, h0⟩ hs)

theorem UpperTheory.irreducible_constituent_of_level_weilDeligne_eq_character :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (w : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω) (h : IsPlaceOver A w) (M n : ℕ), 1 ≤ M →
    ∀ x z : WD h, UpperTheory.V.Af.IsLevelWD M n x → IsIrrWD z → (∀ σ, z.charPol σ ∣ x.charPol σ) →
    ∃ (ξ : Weil h →* ℂˣ) (hξ : IsSmooth ξ), z = WD.lpOfChar h ξ hξ ∧
      ∀ s : ↥(Ine (F := F) A), (∀ ζ : Ω, ζ ^ M = 1 → (s : G F Ω) ζ = ζ) → ξ (ineIncl h s) = 1 := by
  intro F Ω _ _ _ _ _ w A h M n hM x z hx hz hd
  obtain ⟨χ, a, hχ, rfl, -, ha⟩ := hx
  obtain ⟨m, b, rfl, hb⟩ := hz
  have key : ∀ s : ↥(Ine (F := F) A), (∀ ζ : Ω, ζ ^ M = 1 → (s : G F Ω) ζ = ζ) →
      b.ρ (ineIncl h s) = 1 := by
    intro s hs
    have h1 : a.ρ (ineIncl h s) = 1 := by
      rw [ha s]
      have : (fun i => ((χ i s : ℂˣ) : ℂ)) = fun _ => 1 := by
        funext i
        rw [hχ i s hs]
        rfl
      rw [this, Matrix.diagonal_one, Matrix.toLin'_one]
      rfl
    have h2 := hd (ineIncl h s)
    rw [WD.charPol_mk, WD.charPol_mk, h1] at h2
    exact eq_one_of_charpoly_dvd _ (b.semisimple _) h2
  obtain ⟨ξ, hξ, h1, h2⟩ := UpperTheory.irreducible_weilDeligne_tame_level_eq_character F Ω w A h M hM m b hb key
  exact ⟨ξ, hξ, h1, fun s hs => h2 _ (key s hs)⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.RankCohHomOfRankHomology
section
open CategoryTheory in
theorem UpperTheory.rankCohHom_of_rankHomology :
    UpperTheory.V.Af.CohB.RankHomology → UpperTheory.V.Af.BA.RankCohHom := by
  intro hR Γ _ P q X hX A
  obtain ⟨i⟩ := hX
  rw [(groupCohomologyIsoExt A q ≪≫ P.isoExt q A).toLinearEquiv.rank_eq]
  refine (hR _ q).trans ?_
  rw [ChainComplex.linearYonedaObj_X]
  exact (Linear.homCongr ℂ i (Iso.refl A)).rank_eq.le
end

