module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.HostNumber
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNormalised
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.Bundle0014
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.FrameClassOne
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.HostCount
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.HostDataOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.Bundle0011
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.HostLocVan
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.HostOk
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.HostSha
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.Bundle0015
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.ExistsIsUniv
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0022
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0030
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.IrrOpen
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.Bundle0017
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.IsCharZeroPtOfIsPtHom

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.CountVOf
section
open NumberField Matrix IsLocalRing Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.Aut UpperTheory.V.UnitaryThreeInertia

private theorem arith {a V E : ℕ} {s L X : ℝ} {C : ℕ} (ha : a ≤ V) (hV : (V : ℝ) ≤ 2 * E * s) (hL : 0 ≤ L)
    (hs : s * L ≤ X ^ C) (hX : 2 ≤ X) : (a : ℝ) / E * L ≤ X ^ (C + 1) := by
  have hp : 0 ≤ X ^ C := pow_nonneg (by linarith) C
  rcases Nat.eq_zero_or_pos E with rfl | hE
  · simp only [Nat.cast_zero, div_zero, zero_mul]
    exact pow_nonneg (by linarith) _
  · have hE' : (0 : ℝ) < E := by exact_mod_cast hE
    have ha' : (a : ℝ) ≤ V := by exact_mod_cast ha
    have h1 : (a : ℝ) / E ≤ 2 * s := by
      rw [div_le_iff₀ hE']
      linarith
    have h2 := mul_le_mul_of_nonneg_right h1 hL
    have h3 := mul_le_mul_of_nonneg_left hX hp
    rw [pow_succ]
    linarith

private theorem l_mem {l : ℕ} [hl : Fact l.Prime] (c : Coef l) : ((l : ℕ) : c.O) ∈ maximalIdeal c.O := by
  haveI : IsLocalHom (algebraMap ℤ_[l] c.O) := (UpperTheory.V.Base.dvrFacts l c.O).2.2.1
  have h : ((l : ℕ) : ℤ_[l]) ∈ maximalIdeal ℤ_[l] := by
    rw [PadicInt.maximalIdeal_eq_span_p]
    exact Ideal.mem_span_singleton_self _
  have := map_nonunit (algebraMap ℤ_[l] c.O) _ h
  rwa [map_natCast] at this
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.RigFin
section
open NumberField Matrix IsLocalRing Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.Aut UpperTheory.V.UnitaryThreeInertia

private def glOn {G R : Type} [Group G] [CommRing R] {m : ℕ} (H : Subgroup G) (r : G →* GG (m := m) (R := R))
    (h : ∀ g ∈ H, (r g).right = 1) : H →* GL (Fin m) R where
  toFun g := (r g).left
  map_one' := by simp
  map_mul' g g' := by simp [h g g.2]

private theorem contAd {G R : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R] {m : ℕ} (η : G →* ℤˣ) (hη : IsLocallyConstant η)
    (r : G →* GG (m := m) (R := R)) (hm : HasMult η r) (hr : Continuous (mats r)) : ReciprocityTheory.Gal.ContAction (adRep r) := by
  unfold ReciprocityTheory.Gal.ContAction
  refine continuous_iff_continuousAt.2 fun p₀ => ?_
  have hr' : Continuous fun g => (r g).mat := hr
  have hc : Continuous fun p : G × Matrix (Fin m) (Fin m) R =>
      (r p.1).mat * (if η p₀.1 = 1 then p.2 else thetaLie p.2) *
        ((((r p₀.1).left⁻¹ : GL (Fin m) R) : Matrix (Fin m) (Fin m) R) * (r (p₀.1 * p.1⁻¹)).mat) := by
    refine ((hr'.comp continuous_fst).matrix_mul ?_).matrix_mul
      (continuous_const.matrix_mul (hr'.comp (continuous_const.mul continuous_fst.inv)))
    split_ifs
    · exact continuous_snd
    · exact ((continuous_const.matrix_mul continuous_snd.matrix_transpose).matrix_mul continuous_const).neg
  refine hc.continuousAt.congr ?_
  filter_upwards [continuous_fst.continuousAt.eventually (hη.eventually_eq p₀.1)] with p hp
  have h1 : (r (p₀.1 * p.1⁻¹)).right = 1 := by rw [hm, map_mul, map_inv, hp, mul_inv_cancel]
  have h2 : (r p₀.1).left = (r (p₀.1 * p.1⁻¹)).left * (r p.1).left := by
    conv_lhs => rw [← inv_mul_cancel_right p₀.1 p.1, map_mul, SemidirectProduct.mul_left, h1, sgnAct_one]
  have h3 : (r p.1).left⁻¹ = (r p₀.1).left⁻¹ * (r (p₀.1 * p.1⁻¹)).left := by
    rw [h2]; group
  change _ = (r p.1).adFun p.2
  rw [GG.adFun, hm, hp, h3]
  rfl

private def diagCh {G R : Type} [Group G] [CommRing R] {m : ℕ} (r : G →* GL (Fin m) R)
    (h : ∀ g i j, j < i → (r g : Matrix (Fin m) (Fin m) R) i j = 0) (a : Fin m) : G →* Rˣ :=
  MonoidHom.toHomUnits
    { toFun := fun g => (r g : Matrix (Fin m) (Fin m) R) a a
      map_one' := by simp
      map_mul' := fun g k => by
        rw [map_mul, Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single a]
        · intro b _ hb
          rcases lt_or_gt_of_ne hb with hb | hb
          · rw [h g a b hb, zero_mul]
          · rw [h k b a hb, mul_zero]
        · simp }

theorem UpperTheory.V.UnitaryThreeInertia.rig_fin :
    UpperTheory.V.Loc.LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] (φ : Γ →* Formalism.BasicNotions.Loc.GQ l), Topology.IsOpenEmbedding φ → ∀ {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] ℚ_[l] E] [TopologicalSpace E] [IsModuleTopology ℚ_[l] E] [IsTopologicalRing E], ∀ (η : Γ →* ℤˣ), IsLocallyConstant η → ∀ (r : Γ →* GG (m := 3) (R := E)) (y : Γ → Matrix (Fin 3) (Fin 3) E) (r' : Γ →* GG (m := 3) (R := DualNumber E)) (h : GL (Fin 3) (DualNumber E)), HasMult η r → Continuous (mats r) → Continuous y → IsCoc r y → IsDeform ((GG.map (algebraMap E (DualNumber E))).comp r) (fun g => (y g).map (TrivSqZeroExt.inr : E → DualNumber E)) r' → ∀ (H : Subgroup Γ) [H.Normal], IsOpen (H : Set Γ) → H ≤ η.ker → Upper η (conjBy h⁻¹ r') → ∀ w : Fin 3 → ℤ, StrictAnti w → (∀ g ∈ H, φ g ∈ UpperTheory.V.Loc.Iq l → ∀ a, (conjBy h⁻¹ r' g).mat a a = ((UpperTheory.V.Loc.cycA l l (DualNumber E) (φ g) ^ w a : (DualNumber E)ˣ) : DualNumber E)) → (∀ i j : Fin 3, i < j → ∃ g ∈ H, ((conjBy h⁻¹ r' g).mat i i).fst ≠ ((conjBy h⁻¹ r' g).mat j j).fst * ((UpperTheory.V.Loc.cycA l l E (φ g) : Eˣ) : E)) → y ∈ UpperTheory.V.Loc.finiteCocycles φ (adRep r) := by
  intro P l _ Γ _ _ _ φ hφ E _ _ _ _ _ _ _ _ η hη r y r' h hm hr hy hc hd H _ hH hle hU w hw hdiag hne
  haveI : IsModuleTopology ℚ_[l] (Matrix (Fin 3) (Fin 3) E) :=
    inferInstanceAs (IsModuleTopology ℚ_[l] (Fin 3 → Fin 3 → E))
  haveI : FiniteDimensional ℚ_[l] (Matrix (Fin 3) (Fin 3) E) :=
    inferInstanceAs (FiniteDimensional ℚ_[l] (Fin 3 → Fin 3 → E))
  have h1 : ∀ g ∈ H, (r g).right = 1 := fun g hg => (hm g).trans (hle hg)
  have h1' : ∀ g ∈ H, (r' g).right = 1 := fun g hg => (hd g).1.trans (h1 g hg)
  have had : ∀ (g : H) X, adRep r g X = UpperTheory.V.Loc.adGL (glOn H r h1) g X := fun g X => by
    change (r g).adFun X = _
    rw [GG.adFun, if_pos (h1 g g.2)]
    rfl
  have hcj : ∀ g : H, (UpperTheory.V.Loc.conjGL h⁻¹ (glOn H r' h1') g : Matrix (Fin 3) (Fin 3) (DualNumber E)) =
      (conjBy h⁻¹ r' g).mat := fun g => by
    simp [UpperTheory.V.Loc.conjGL, glOn, conjBy, GG.mat, h1' g g.2]
  have hup : ∀ (g : H) i j, j < i →
      (UpperTheory.V.Loc.conjGL h⁻¹ (glOn H r' h1') g : Matrix (Fin 3) (Fin 3) (DualNumber E)) i j = 0 :=
    fun g i j hij => by
      rw [hcj]
      refine hU g (hle g.2) i j ?_
      have : (j : ℕ) < i := hij
      simp only [wt, wt1]
      omega
  have hκ : ∀ i (g : H), ((diagCh _ hup i g : (DualNumber E)ˣ) : DualNumber E) = (conjBy h⁻¹ r' g).mat i i :=
    fun i g => by rw [← hcj]; rfl
  refine (UpperTheory.V.Loc.pr6 P φ hφ (adRep r) (contAd η hη r hm hr) y ⟨hy, hc⟩ H hH (glOn H r h1)
    (hr.comp continuous_subtype_val) LinearMap.id LinearMap.id (fun _ => rfl) had (fun g X => (had g X).symm)
    (glOn H r' h1') ?_ h⁻¹ (diagCh _ hup) w (fun g => ⟨hup g, fun _ => rfl⟩) hw
    (fun i g hg => Units.ext ((hκ i g).trans (hdiag g g.2 hg i))) ?_).2.2
  · intro g i j
    change (r' g).mat i j = ⟨(r g).mat i j, (y g * (r g).mat) i j⟩
    rw [(hd g).2, Matrix.add_mul, Matrix.one_mul, Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply]
    ext <;> simp [Fin.sum_univ_three, TrivSqZeroExt.algebraMap_eq_inl, mul_comm]
  · intro i j hij
    obtain ⟨g, hg, hn⟩ := hne i j hij
    exact ⟨⟨g, hg⟩, by rw [hκ, hκ]; exact hn⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.UnitaryLiftTheoremOfReducedForm
section
open NumberField Matrix IsLocalRing Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.Aut UpperTheory.V.UnitaryThreeInertia

private theorem totDisc_quot {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G] (N : Subgroup G) [N.Normal] (hN : IsClosed (N : Set G)) :
    TotallyDisconnectedSpace (G ⧸ N) := by
  rw [totallyDisconnectedSpace_iff_connectedComponent_one]
  refine Set.eq_singleton_iff_unique_mem.2 ⟨mem_connectedComponent, fun y hy => ?_⟩
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
  by_contra hx
  have hx' : x ∉ N := fun h => hx ((QuotientGroup.eq_one_iff x).2 h)
  have ho : IsOpen {g : G | g * x ∉ N} := hN.isOpen_compl.preimage (continuous_mul_const x)
  obtain ⟨U, hU⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one ho (by simpa using hx')
  let V : Subgroup (G ⧸ N) := U.toSubgroup.map (QuotientGroup.mk' N)
  have hVo : IsOpen (V : Set (G ⧸ N)) := QuotientGroup.isOpenMap_coe _ U.isOpen'
  have hV : IsClopen (V : Set (G ⧸ N)) := ⟨V.isClosed_of_isOpen hVo, hVo⟩
  obtain ⟨u, hu, hux⟩ := hV.connectedComponent_subset V.one_mem hy
  exact hU (U.toSubgroup.inv_mem hu) (QuotientGroup.eq.1 hux)
end

