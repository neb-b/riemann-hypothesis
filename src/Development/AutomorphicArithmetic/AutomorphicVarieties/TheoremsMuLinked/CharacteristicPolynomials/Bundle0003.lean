module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.OrdZero
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.IsUnitOrIsUnitOfAddOne
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.UniversalOrdinaryDeterminantRing
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.Bundle0004
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.BaseRepGL3NormalisedOfPsiEqOne
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.IrreducibleSpans.Burnside
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CharacteristicPolynomials.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.Bundle0003

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CharacteristicPolynomials.CharpolyCompNegRoots
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.HV UpperTheory.V.Alg GlobalTheory.GalOfCusp

private theorem charpoly_neg {R : Type} [CommRing R] {n : ℕ} (M : Matrix (Fin n) (Fin n) R) :
    (-M).charpoly = (-1) ^ n * M.charpoly.comp (-X) := by
  have h : (M.charmatrix).map (Polynomial.compRingHom (-X : R[X])) = -(-M).charmatrix := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [charmatrix_apply_eq]
      ring
    · simp [charmatrix_apply_ne _ _ _ hij]
  have h2 : M.charpoly.comp (-X) = (-1) ^ n * (-M).charpoly := by
    rw [Matrix.charpoly, ← Polynomial.coe_compRingHom_apply, RingHom.map_det, RingHom.mapMatrix_apply, h,
      det_neg, Fintype.card_fin]
    rfl
  rw [h2, ← mul_assoc, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_mul]

private theorem charpoly_comp_neg_roots {R : Type} [CommRing R] {n : ℕ} (a : Fin n → R) :
    (-1 : R[X]) ^ n * (∏ i, (X - C (a i))).comp (-X) = ∏ i, (X - C (-a i)) := by
  rw [Polynomial.prod_comp, ← Fin.prod_const, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [sub_comp, X_comp, C_comp, map_neg]
  ring

theorem UpperTheory.V.Th.Det.perm4 :
    ∀ (K k B G : Type) [Field K] [Field k] [CommRing B] [Group G] (n : ℕ) (r : G →* GL (Fin n) K) (j : B →+* K) (φ : B →+* k) (χ : Fin n → G →* kˣ) (η : G →* ℤˣ), Function.Injective j → Pr.RedTo r j φ χ → (∀ g, (W.mat r g).charpoly = ((((η g : ℤˣ) : ℤ) : K) • W.mat r g).charpoly) → ∀ i, ∃ i', W.pushCh (Int.castRingHom k) η * χ i = χ i' := by
  intro K k B G _ _ _ _ n r j φ χ η hj hred hsym
  let χ' : Fin n → G →* kˣ := fun i => W.pushCh (Int.castRingHom k) η * χ i
  have hval : ∀ g i, (((χ' i) g : kˣ) : k) = (((η g : ℤˣ) : ℤ) : k) * ((χ i g : kˣ) : k) := by
    intro g i
    simp [χ', W.pushCh]
  have key : ∀ g, Pr.chPoly χ g = Pr.chPoly χ' g := by
    intro g
    rcases Int.units_eq_one_or (η g) with h | h
    · unfold Pr.chPoly
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [hval g i, h]
      simp
    · obtain ⟨p, hp1, hp2⟩ := hred g
      have hp1' : Polynomial.map j p = (W.mat r g).charpoly := hp1
      have hM : (W.mat r g).charpoly = (-1) ^ n * (W.mat r g).charpoly.comp (-X) := by
        rw [← charpoly_neg, hsym g, h, Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one,
          neg_one_smul]
      have hp : p = (-1) ^ n * p.comp (-X) := by
        apply Polynomial.map_injective j hj
        rw [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_neg, Polynomial.map_one,
          Polynomial.map_comp, Polynomial.map_neg, Polynomial.map_X, hp1']
        exact hM
      have hq := congrArg (Polynomial.map φ) hp
      rw [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_neg, Polynomial.map_one,
        Polynomial.map_comp, Polynomial.map_neg, Polynomial.map_X, hp2] at hq
      rw [hq]
      unfold Pr.chPoly
      rw [charpoly_comp_neg_roots (fun i => (((χ i) g : kˣ) : k))]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [hval g i, h]
      simp
  obtain ⟨σ, hσ⟩ := Pr.charPerm G k n χ χ' key
  intro i
  exact ⟨σ i, hσ i⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CharacteristicPolynomials.CharpolyPow
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.HV UpperTheory.V.Alg GlobalTheory.GalOfCusp

namespace UpperTheory.V.Th.Det

open UpperTheory.V.U3 UpperTheory.V.Pr

private lemma open_basis {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G] (O : Set G) (hO : IsOpen O) (h1 : (1 : G) ∈ O) :
    ∃ V : Subgroup G, IsOpen (V : Set G) ∧ (V : Set G) ⊆ O := by
  obtain ⟨H, hH⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hO h1
  exact ⟨H.toSubgroup, H.isOpen', hH⟩

private lemma strong_of {G κ : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G] [Field κ] {m : ℕ} (G' V : Subgroup G) (hV : IsOpen (V : Set G))
    (r : G →* GL (Fin m) κ) (hc : LinClosed (gm r))
    (hirr : ∀ U : Subgroup G, IsOpen (U : Set G) → MatIrr (U ⊓ G') (gm r)) :
    StrongIrr (r.comp (V ⊓ G').subtype) := by
  refine strongIrrOfOpen _ κ m _ (fun f => (hc f).preimage continuous_subtype_val) ?_
  intro U hU W hW
  obtain ⟨O, hO, hOU⟩ := isOpen_induced_iff.1 hU
  have h1 : (1 : G) ∈ O := by
    have : (1 : ↥(V ⊓ G')) ∈ (U : Set ↥(V ⊓ G')) := U.one_mem
    rw [← hOU] at this
    exact this
  obtain ⟨V', hV', hsub⟩ := open_basis (O ∩ V) (hO.inter hV) ⟨h1, V.one_mem⟩
  refine hirr V' hV' W fun g hg => ?_
  have h2 := hsub hg.1
  have h3 : (⟨g, h2.2, hg.2⟩ : ↥(V ⊓ G')) ∈ (U : Set ↥(V ⊓ G')) := by
    rw [← hOU]; exact h2.1
  exact hW _ h3

private lemma coset_in {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G] (U : Set G) (hU : IsOpen U) (s : G) (hs : s ∈ U) :
    ∃ V : Subgroup G, IsOpen (V : Set G) ∧ ∀ h ∈ V, s * h ∈ U := by
  obtain ⟨V, hV, hsub⟩ := open_basis ((fun h => s * h) ⁻¹' U) (hU.preimage (continuous_const.mul continuous_id))
    (by simpa using hs)
  exact ⟨V, hV, fun h hh => hsub hh⟩

private lemma cosetI {G κ : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G] [Field κ] {n : ℕ} (hn : n ≤ 3) (G' : Subgroup G)
    (r : G →* GL (Fin n) κ) (hc : LinClosed (gm r))
    (hirr : ∀ U : Subgroup G, IsOpen (U : Set G) → MatIrr (U ⊓ G') (gm r))
    (hsep : ∀ U : Subgroup G, IsOpen (U : Set G) → ∃ u ∈ U ⊓ G', ∃ α : Fin n → κˣ, FreeRatios α ∧
      (gm r u).charpoly = ∏ i, (X - C ((α i : κˣ) : κ)))
    (U : Set G) (hU : IsOpen U) (hne : (U ∩ (G' : Set G)).Nonempty) :
    ∃ σ ∈ U ∩ (G' : Set G), (gm r σ).charpoly.Separable := by
  obtain ⟨s, hs, hs'⟩ := hne
  obtain ⟨V, hV, hsV⟩ := coset_in U hU s hs
  obtain ⟨u, hu, α, hα, hch⟩ := hsep V hV
  obtain ⟨h, hh⟩ := regCoset _ κ n hn _ (strong_of G' V hV r hc hirr) ⟨u, hu⟩ α hα hch (r s)
  refine ⟨s * h, ⟨hsV _ h.2.1, G'.mul_mem hs' h.2.2⟩, ?_⟩
  simp only [gm, map_mul, Units.val_mul]
  exact hh

private lemma charpoly_pow {K : Type} [Field K] {n : ℕ} (M : Matrix (Fin n) (Fin n) K) (a : Fin n → Kˣ)
    (hM : M.charpoly = ∏ i, (X - C (a i : K))) (ha : FreeRatios a) (d : ℕ) (hd : 0 < d) :
    (M ^ d).charpoly = ∏ i, (X - C ((a i : K) ^ d)) :=
  _root_.UpperTheory.Reformulated.B.CharpolyPowersRatios.charpoly_pow M a hM ha d hd

end UpperTheory.V.Th.Det

theorem UpperTheory.V.Th.Det.n3small :
    ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] {n : ℕ}, n ≤ 3 → ∀ (G' : Subgroup G) (ρ : G →* GL (Fin n) (Qbar l)), Continuous ρ → (∀ U : Subgroup G, IsOpen (U : Set G) → U3.MatIrr (U ⊓ G') (W.mat ρ)) → (∃ u ∈ G', ∃ α : Fin n → (Qbar l)ˣ, Pr.FreeRatios α ∧ (W.mat ρ u).charpoly = ∏ i, (X - C ((α i : (Qbar l)ˣ) : Qbar l))) → ∀ U : Set G, IsOpen U → (U ∩ (G' : Set G)).Nonempty → ∃ σ ∈ U ∩ (G' : Set G), (W.mat ρ σ).charpoly.Separable := by
  intro l _ G _ _ _ _ _ n hn G' ρ hρ hirr ⟨u, hu, α, hα, hch⟩ U hU hne
  have hc : Pr.LinClosed (Pr.gm ρ) := by
    intro f
    have h1 : Continuous (Pr.gm ρ) := Units.continuous_val.comp hρ
    have h2 : Continuous fun g => f (Pr.gm ρ g) := by
      have e : (fun g => f (Pr.gm ρ g)) = fun g => ∑ i, ∑ j, Pr.gm ρ g i j * f (Matrix.single i j 1) := by
        funext g
        conv_lhs => rw [Matrix.matrix_eq_sum_single (Pr.gm ρ g)]
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [map_sum]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        rw [← smul_eq_mul, ← map_smul, Matrix.smul_single, smul_eq_mul, mul_one]
      rw [e]
      refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
      exact (h1.matrix_elem i j).mul continuous_const
    exact isClosed_eq h2 continuous_const
  refine cosetI hn G' ρ hc hirr ?_ U hU hne
  intro V hV
  haveI : Finite (G ⧸ V) := Subgroup.quotient_finite_of_isOpen V hV
  haveI : V.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  obtain ⟨d, hd, -, hdV⟩ := Subgroup.exists_pow_mem_of_index_ne_zero (Subgroup.FiniteIndex.index_ne_zero (H := V)) u
  refine ⟨u ^ d, ⟨hdV, G'.pow_mem hu d⟩, fun i => α i ^ d, ?_, ?_⟩
  · intro i j hij m hm
    simp only [← pow_mul]
    exact hα i j hij _ (Nat.mul_pos hd hm)
  · have := charpoly_pow _ α hch hα d hd
    rw [← map_pow] at this
    simp only [Units.val_pow_eq_pow_val]
    exact this
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CharacteristicPolynomials.DetGCentral
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.HV UpperTheory.V.Alg GlobalTheory.GalOfCusp

private theorem detG_central {K G : Type} [Field K] [Group G] {n : ℕ}
    (m : G →* Matrix (Fin n) (Fin n) K) (χ : G →* Kˣ) (N : Subgroup G)
    (w : G → Matrix (Fin n) (Fin n) K) (hc : commutator G ≤ N) (hk : N ≤ χ.ker) (hχ : χ ≠ 1)
    (hspan : Submodule.span K (Set.range (m.comp N.subtype)) = ⊤)
    (hw : ∀ g g', w (g * g') = w g + (χ g : K) • (m g * w g' * m g⁻¹))
    (h0 : ∀ g ∈ N, w g = 0) :
    ∃ A, ∀ g, w g = (χ g : K) • (m g * A * m g⁻¹) - A := by
  have hinv : ∀ g, m g⁻¹ * m g = 1 := fun g => by rw [← map_mul, inv_mul_cancel, map_one]
  have hinv' : ∀ g, m g * m g⁻¹ = 1 := fun g => by rw [← map_mul, mul_inv_cancel, map_one]
  have hcom : ∀ g h : G, g * h * g⁻¹ * h⁻¹ ∈ N := fun g h =>
    hc (Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top h))
  have hone : ∀ x ∈ N, (χ x : K) = 1 := fun x hx => by
    have : χ x = 1 := hk hx
    rw [this, Units.val_one]
  have hconj : ∀ g, ∀ x ∈ N, w g = m x * w g * m x⁻¹ := by
    intro g x hx
    have hy : g⁻¹ * x * g ∈ N := by
      have := N.mul_mem (hcom g⁻¹ x) hx
      simpa [mul_assoc] using this
    have e : x * g = g * (g⁻¹ * x * g) := by simp [mul_assoc]
    have h1 := hw x g
    rw [e, hw, h0 _ hy, h0 _ hx, hone x hx] at h1
    simpa using h1
  have hcen : ∀ g (X : Matrix (Fin n) (Fin n) K), X * w g = w g * X := by
    intro g X
    have hX : X ∈ Submodule.span K (Set.range (m.comp N.subtype)) := hspan ▸ Submodule.mem_top
    induction hX using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨y, rfl⟩ := hx
      change m y * w g = w g * m y
      conv_rhs => rw [hconj g y y.2]
      rw [mul_assoc, hinv, mul_one]
    | zero => simp
    | add x y _ _ h₁ h₂ => rw [mul_add, add_mul, h₁, h₂]
    | smul a x _ h₁ => rw [mul_smul_comm, smul_mul_assoc, h₁]
  have hfix : ∀ g h, m g * w h * m g⁻¹ = w h := fun g h => by
    rw [hcen, mul_assoc, hinv', mul_one]
  have hw' : ∀ g h, w (g * h) = w g + (χ g : K) • w h := fun g h => by rw [hw, hfix]
  have hsym : ∀ g h, w (g * h) = w (h * g) := by
    intro g h
    have e : g * h = (g * h * g⁻¹ * h⁻¹) * (h * g) := by simp [mul_assoc]
    rw [e, hw' (g * h * g⁻¹ * h⁻¹), h0 _ (hcom g h), hone _ (hcom g h), zero_add, one_smul]
  obtain ⟨h, hh⟩ : ∃ h, χ h ≠ 1 := by
    by_contra hn
    exact hχ (MonoidHom.ext fun g => by_contra fun hg => hn ⟨g, hg⟩)
  have hh' : (χ h : K) - 1 ≠ 0 := fun e => hh (Units.ext (by simpa using sub_eq_zero.mp e))
  refine ⟨((χ h : K) - 1)⁻¹ • w h, fun g => ?_⟩
  have h1 := hsym g h
  rw [hw', hw'] at h1
  have h2 : ((χ h : K) - 1) • w g = (χ g : K) • w h - w h := by
    rw [sub_smul, one_smul, sub_eq_sub_iff_add_eq_add, add_comm, ← h1, add_comm]
  rw [mul_smul_comm, smul_mul_assoc, hfix, smul_comm, ← smul_sub, ← h2, smul_smul,
    inv_mul_cancel₀ hh', one_smul]

theorem UpperTheory.V.Th.Det.detG :
    ∀ {K G : Type} [Field K] [IsAlgClosed K] [Group G] {n : ℕ} (ρ : G →* GL (Fin n) K) (χ : G →* Kˣ) (N : Subgroup G) (z : G → Matrix (Fin n) (Fin n) K), 1 ≤ n → commutator G ≤ N → N ≤ χ.ker → χ ≠ 1 → U3.MatIrr N (W.mat ρ) → (∀ g g', z (g * g') = z g + (χ g : K) • (W.mat ρ g * z g' * W.mat ρ g⁻¹)) → (∀ g ∈ N, (z g * W.mat ρ g).trace = 0) → ∃ Y, ∀ g, z g = (χ g : K) • (W.mat ρ g * Y * W.mat ρ g⁻¹) - Y := by
  intro K G _ _ _ n ρ χ N z hn hc hk hχ hirr hz htr
  generalize W.mat ρ = m at hirr hz htr ⊢
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hone : ∀ x ∈ N, (χ x : K) = 1 := fun x hx => by
    have : χ x = 1 := hk hx
    rw [this, Units.val_one]
  have hspan : Submodule.span K (Set.range (m.comp N.subtype)) = ⊤ :=
    KStar.Schema.span_eq_top_of_irreducible _ fun U hU => hirr U fun g hg v hv => hU ⟨g, hg⟩ v hv
  let r : N →* (∀ _ : Unit, Matrix (Fin n) (Fin n) K) := MonoidHom.pi fun _ => m.comp N.subtype
  have hspan' : Submodule.span K (Set.range r) = ⊤ := by
    let L : Matrix (Fin n) (Fin n) K →ₗ[K] (∀ _ : Unit, Matrix (Fin n) (Fin n) K) :=
      LinearMap.pi fun _ => LinearMap.id
    have hL : Function.Surjective L := fun x => ⟨x (), rfl⟩
    have e : Set.range r = L '' Set.range (m.comp N.subtype) := by
      rw [← Set.range_comp]; rfl
    rw [e, ← Submodule.map_span, hspan, Submodule.map_top, LinearMap.range_eq_top.mpr hL]
  obtain ⟨Y₀, hY₀⟩ := UpperTheory.V.AlgebraTools.cocycle_trace_zero (K := K) (fun _ : Unit => Fin n) r
    (fun g _ => z g) hspan'
    (fun g h => by
      funext s
      have := hz g h
      rw [hone g g.2, one_smul] at this
      exact this)
    (fun g => by
      rw [Fintype.sum_unique]
      exact htr g g.2)
  have hY : ∀ g ∈ N, z g = Y₀ () - m g * Y₀ () * m g⁻¹ := fun g hg => congrFun (hY₀ ⟨g, hg⟩) ()
  have hinv' : ∀ g, m g * m g⁻¹ = 1 := fun g => by rw [← map_mul, mul_inv_cancel, map_one]
  obtain ⟨A, hA⟩ := detG_central m χ N
    (fun g => z g + ((χ g : K) • (m g * Y₀ () * m g⁻¹) - Y₀ ())) hc hk hχ hspan
    (fun g h => by
      simp only [hz, map_mul, _root_.mul_inv_rev, Units.val_mul, mul_add, add_mul, mul_sub, sub_mul,
        smul_add, smul_sub, mul_smul_comm, smul_mul_assoc, smul_smul, mul_assoc]
      abel)
    (fun g hg => by
      simp only [hY g hg, hone g hg, one_smul]
      abel)
  refine ⟨A - Y₀ (), fun g => ?_⟩
  have := hA g
  simp only [mul_sub, sub_mul, smul_sub]
  rw [eq_sub_of_add_eq this]
  abel
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CharacteristicPolynomials.FinDet
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.HV UpperTheory.V.Alg GlobalTheory.GalOfCusp

theorem UpperTheory.V.Th.Det.finDet :
    ∀ {K V S ι : Type} [Field K] [AddCommGroup V] [Module K V] [Module.Finite K V] (f : S → ι → V →ₗ[K] K), ∃ T : Finset S, ∀ v : V, (∀ s ∈ T, ∀ i, f s i v = 0) → ∀ s i, f s i v = 0 := by
  intro K V S ι _ _ _ _ f
  classical
  let U : Finset S → Submodule K V := fun T => ⨅ s ∈ T, ⨅ i, LinearMap.ker (f s i)
  obtain ⟨_, ⟨T, rfl⟩, hT⟩ :=
    (wellFounded_lt (α := Submodule K V)).has_min (Set.range U) ⟨U ∅, ∅, rfl⟩
  refine ⟨T, fun v hv s i => ?_⟩
  have hle : U (insert s T) ≤ U T := by
    intro w hw
    simp only [U, Submodule.mem_iInf, Finset.mem_insert] at hw ⊢
    intro t ht j
    exact hw t (Or.inr ht) j
  have heq : U (insert s T) = U T := by
    by_contra hne
    exact hT _ ⟨_, rfl⟩ (lt_of_le_of_ne hle hne)
  have hvT : v ∈ U T := by
    simp only [U, Submodule.mem_iInf, LinearMap.mem_ker]
    exact hv
  rw [← heq] at hvT
  simp only [U, Submodule.mem_iInf, LinearMap.mem_ker, Finset.mem_insert] at hvT
  exact hvT s (Or.inl rfl) i
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CharacteristicPolynomials.FiniteCocyclesMatrixRepresentationOfPhiCond
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.HV UpperTheory.V.Alg GlobalTheory.GalOfCusp

private def matrixFlattenLinearEquiv (K : Type) [Field K] (n : ℕ) :
    Matrix (Fin n) (Fin n) K ≃ₗ[K] (Fin (n * n) → K) where
  toFun X i := X (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2
  invFun v a b := v (finProdFinEquiv (a, b))
  map_add' X Y := rfl
  map_smul' c X := rfl
  left_inv X := by
    funext a b
    simp
  right_inv v := by
    funext i
    simp only [Prod.mk.eta, Equiv.apply_symm_apply]

private theorem continuous_matrix_flatten (K : Type) [Field K] [TopologicalSpace K] (n : ℕ) :
    Continuous (matrixFlattenLinearEquiv K n) := by
  show Continuous fun (X : Matrix (Fin n) (Fin n) K) (i : Fin (n * n)) => X (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2
  exact continuous_pi fun i => (continuous_apply _).comp (continuous_apply _)

private noncomputable def flattenedMatrixRepresentation {K : Type} [Field K] {G : Type} [Group G] {n : ℕ}
    (R : Representation K G (Matrix (Fin n) (Fin n) K)) :
    G →* Matrix (Fin (n * n)) (Fin (n * n)) K where
  toFun g := LinearMap.toMatrix'
    ((matrixFlattenLinearEquiv K n).toLinearMap ∘ₗ R g ∘ₗ (matrixFlattenLinearEquiv K n).symm.toLinearMap)
  map_one' := by
    rw [← LinearMap.toMatrix'_id]
    congr 1
    refine LinearMap.ext fun v => ?_
    simp
  map_mul' g h := by
    rw [← LinearMap.toMatrix'_comp]
    congr 1
    refine LinearMap.ext fun v => ?_
    simp

private theorem matrix_rep_flatten_apply {K : Type} [Field K] {G : Type} [Group G] {n : ℕ}
    (R : Representation K G (Matrix (Fin n) (Fin n) K)) (g : G) (X : Matrix (Fin n) (Fin n) K) :
    Matrix.toLin' (flattenedMatrixRepresentation R g) (matrixFlattenLinearEquiv K n X) = matrixFlattenLinearEquiv K n (R g X) := by
  show Matrix.toLin' (LinearMap.toMatrix' _) _ = _
  rw [Matrix.toLin'_toMatrix']
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, LinearEquiv.symm_apply_apply]

private theorem continuous_matrix_rep_flatten {K : Type} [Field K] [TopologicalSpace K] {G : Type} [Group G]
    [TopologicalSpace G] {n : ℕ}
    (R : Representation K G (Matrix (Fin n) (Fin n) K)) (hR : ∀ X, Continuous fun g => R g X) :
    Continuous (flattenedMatrixRepresentation R) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  show Continuous fun g => LinearMap.toMatrix' ((matrixFlattenLinearEquiv K n).toLinearMap ∘ₗ R g ∘ₗ (matrixFlattenLinearEquiv K n).symm.toLinearMap) i j
  simp only [LinearMap.toMatrix'_apply]
  exact (continuous_matrix_flatten K n).comp (hR _) |>.comp continuous_id |> fun h => (continuous_apply i).comp h

theorem UpperTheory.V.Th.Det.finite_cocycles_matrixRepresentation_of_phiCond :
    ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] {n : ℕ} (R : Representation (Qbar l) G (Matrix (Fin n) (Fin n) (Qbar l))), PhiCond G l → (∀ X, Continuous fun g => R g X) → Module.Finite (Qbar l) (Z1 R) := by
  intro l _ G _ _ _ _ _ n R hΦ hR
  let σ : G →* GL (Fin (n * n)) (Qbar l) := (flattenedMatrixRepresentation R).toHomUnits
  have hσ : Continuous σ := by
    rw [Units.continuous_iff]
    refine ⟨continuous_matrix_rep_flatten R hR, ?_⟩
    have h : (fun g => (((σ g)⁻¹ : GL (Fin (n * n)) (Qbar l)) : Matrix (Fin (n * n)) (Fin (n * n)) (Qbar l))) = fun g => flattenedMatrixRepresentation R g⁻¹ := by
      funext g
      rw [← map_inv]
      rfl
    rw [h]
    exact (continuous_matrix_rep_flatten R hR).comp continuous_inv
  have hfin := UpperTheory.V.Th.Det.finite_cocycles_colRep_of_phiCond σ hΦ hσ
  let Φ : (G → Matrix (Fin n) (Fin n) (Qbar l)) →ₗ[Qbar l] (G → Fin (n * n) → Qbar l) :=
    LinearMap.compLeft (matrixFlattenLinearEquiv (Qbar l) n).toLinearMap G
  have hmem : ∀ f ∈ Z1 R, Φ f ∈ Z1 (UpperTheory.V.Loc.colRep σ) := by
    rintro f ⟨hc, hco⟩
    refine ⟨(continuous_matrix_flatten (Qbar l) n).comp hc, fun g h => ?_⟩
    show matrixFlattenLinearEquiv (Qbar l) n (f (g * h)) = matrixFlattenLinearEquiv (Qbar l) n (f g) + Matrix.toLin' (flattenedMatrixRepresentation R g) (matrixFlattenLinearEquiv (Qbar l) n (f h))
    rw [hco g h, map_add (f := _), matrix_rep_flatten_apply]
  have hinj : Function.Injective (Φ.restrict hmem) := by
    intro x y hxy
    apply Subtype.ext
    funext g
    have e := congrFun (congrArg Subtype.val hxy) g
    exact (matrixFlattenLinearEquiv (Qbar l) n).injective e
  exact Module.Finite.of_injective (Φ.restrict hmem) hinj
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CharacteristicPolynomials.IrrSmall
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.HV UpperTheory.V.Alg GlobalTheory.GalOfCusp

private theorem charpoly_flag {H k : Type} [Group H] [CommRing k] {n : ℕ} (r : H →* GL (Fin n) k)
    (κ : Fin n → H →* kˣ) (h : W.HasFlag r κ) (s : H) : (Pr.gm r s).charpoly = Pr.chPoly κ s := by
  obtain ⟨g, hg⟩ := h
  have h1 := Matrix.charpoly_units_conj g (Pr.gm r s)
  have h2 : ((g * r s * g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).BlockTriangular id :=
    fun i j hij => (hg s).1 i j hij
  have h3 := Matrix.charpoly_of_upperTriangular _ h2
  rw [← h1]
  simp only [Units.val_mul, Matrix.coe_units_inv] at h3
  rw [h3]
  refine Finset.prod_congr rfl fun i _ => ?_
  have h4 := (hg s).2 i
  simp only [Units.val_mul, Matrix.coe_units_inv] at h4
  rw [h4]

private theorem root_eq {k : Type} [Field k] {n : ℕ} (x y : Fin n → k) (c : k) (hy : ∀ i, y i = c)
    (h : ∏ i, (X - C (x i)) = ∏ i, (X - C (y i))) (a : Fin n) : x a = c := by
  have h3 := congrArg (Polynomial.eval (x a)) h
  rw [Polynomial.eval_prod, Polynomial.eval_prod,
    Finset.prod_eq_zero (f := fun i => Polynomial.eval (x a) (X - C (x i))) (Finset.mem_univ a) (by simp),
    eq_comm, Finset.prod_eq_zero_iff] at h3
  obtain ⟨i, _, h4⟩ := h3
  rw [← hy i]
  simpa [sub_eq_zero] using h4

theorem UpperTheory.V.Th.Det.irrSmall :
    ∀ {K k B G D : Type} [Field K] [IsAlgClosed K] [Field k] [CommRing B] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [Group D] {n : ℕ}, n.Prime → ∀ (G' : Subgroup G) [G'.Normal] (ρ : G →* GL (Fin n) K) (j : B →+* K) (φ : B →+* k) (χ : Fin n → G →* kˣ) (ι : D →* G) (ψ : Fin n → D →* Kˣ) (ψb : Fin n → D →* kˣ), U3.MatIrr ⊤ (W.mat ρ) → Function.Injective j → Pr.RedTo ρ j φ χ → W.HasFlag (ρ.comp ι) ψ → (∀ i g, ∃ a : B, j a = (ψ i g : K) ∧ φ a = (ψb i g : k)) → (∃ g, ι g ∈ G' ∧ Pr.FreeRatios fun i => ψ i g) → (∃ a b g, ψb a g ≠ ψb b g) → ∀ U : Subgroup G, IsOpen (U : Set G) → U3.MatIrr (U ⊓ G') (W.mat ρ) := by
  intro K k B G D _ _ _ _ _ _ _ _ _ n hn G' _ ρ j φ χ ι ψ ψb hirr hj hred hflag hlift hfree hne U hU
  classical
  have hfi : U.FiniteIndex := by
    haveI := Subgroup.quotient_finite_of_isOpen U hU
    exact Subgroup.finiteIndex_of_finite_quotient
  have hch : ∀ g, (Pr.gm ρ (ι g)).charpoly = Pr.chPoly ψ g := fun g => charpoly_flag _ _ hflag g
  have key := Pr.irrNormal G K k B n hn ρ hirr j φ χ hj hred D ι ψ hch (U.normalCore ⊓ G') (fun a b hab => ?_) ?_
  · intro W hW
    exact key W fun g hg => hW g ⟨U.normalCore_le hg.1, hg.2⟩
  · obtain ⟨g, hg, hfr⟩ := hfree
    have hpos : 0 < U.normalCore.index := Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero
    refine ⟨g ^ U.normalCore.index, ?_, ?_⟩
    · rw [map_pow]
      exact ⟨U.normalCore.pow_index_mem _, G'.pow_mem hg _⟩
    · rw [map_pow, map_pow]
      exact hfr a b hab _ hpos
  · obtain ⟨a, b, g, hab⟩ := hne
    by_contra hcon
    push Not at hcon
    apply hab
    choose c hc1 hc2 using fun i => hlift i g
    obtain ⟨p, hp1, hp2⟩ := hred (ι g)
    have hp : p = ∏ i, (X - C (c i)) := by
      apply Polynomial.map_injective j hj
      rw [hp1, hch, Pr.chPoly, Polynomial.map_prod]
      simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, hc1]
    rw [hp, Pr.chPoly, Polynomial.map_prod] at hp2
    simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, hc2] at hp2
    have h := root_eq (fun i => ((ψb i g : kˣ) : k)) (fun i => ((χ i (ι g) : kˣ) : k)) (χ a (ι g) : kˣ)
      (fun i => by rw [hcon i a g]) hp2
    exact Units.ext ((h a).trans (h b).symm)
end

